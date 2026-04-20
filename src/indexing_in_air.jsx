import { useState, useMemo, useCallback, useRef, useEffect } from "react";

// ─── Utility: Build a balanced B+ tree from data items ───
function buildTree(dataItems, fanout) {
  // dataItems: array of { key, label } sorted by key
  // fanout: branching factor (children per internal node)
  if (dataItems.length === 0) return null;

  // Leaf nodes: each leaf covers `fanout` data items
  const leaves = [];
  for (let i = 0; i < dataItems.length; i += fanout) {
    const chunk = dataItems.slice(i, i + fanout);
    leaves.push({
      id: `c${leaves.length + 1}`,
      level: "leaf",
      keys: chunk.map((d) => d.key),
      labels: chunk.map((d) => d.label),
      dataRange: [i, Math.min(i + fanout - 1, dataItems.length - 1)],
      children: [],
    });
  }

  let currentLevel = leaves;
  let levelName = "b";
  let levelCounter = 0;

  while (currentLevel.length > 1) {
    const nextLevel = [];
    for (let i = 0; i < currentLevel.length; i += fanout) {
      const chunk = currentLevel.slice(i, i + fanout);
      levelCounter++;
      const node = {
        id: `${levelName}${nextLevel.length + 1}`,
        level: levelName,
        keys: chunk.map((c) => c.keys[0]),
        children: chunk,
      };
      nextLevel.push(node);
    }
    currentLevel = nextLevel;
    levelName = String.fromCharCode(levelName.charCodeAt(0) - 1);
    if (levelName < "a") levelName = "I";
  }

  const root = currentLevel[0];
  if (root.level !== "I") root.level = "I";
  root.id = "I";
  return root;
}

// Assign depth levels to tree
function assignDepths(node, depth = 0) {
  node.depth = depth;
  if (node.children) {
    node.children.forEach((c) => assignDepths(c, depth + 1));
  }
}

// Get tree height
function getTreeHeight(node) {
  if (!node.children || node.children.length === 0) return 0;
  return 1 + Math.max(...node.children.map(getTreeHeight));
}

// Flatten tree by level
function flattenByLevel(node) {
  const levels = {};
  function walk(n) {
    if (!levels[n.depth]) levels[n.depth] = [];
    levels[n.depth].push(n);
    if (n.children) n.children.forEach(walk);
  }
  walk(node);
  return levels;
}

// Get all leaves in order
function getLeaves(node) {
  if (!node.children || node.children.length === 0) return [node];
  return node.children.flatMap(getLeaves);
}

// Get all nodes at a specific depth
function getNodesAtDepth(node, targetDepth) {
  if (node.depth === targetDepth) return [node];
  if (!node.children) return [];
  return node.children.flatMap((c) => getNodesAtDepth(c, targetDepth));
}

// Find path from root to a leaf containing a data offset
function findPath(node, dataOffset) {
  if (node.level === "leaf") {
    if (dataOffset >= node.dataRange[0] && dataOffset <= node.dataRange[1]) {
      return [node];
    }
    return null;
  }
  if (node.children) {
    for (const child of node.children) {
      const result = findPath(child, dataOffset);
      if (result) return [node, ...result];
    }
  }
  return null;
}

// Build the broadcast schedule with partial replication
function buildBroadcastSchedule(tree, replicationDepth, dataItems, fanout) {
  if (!tree) return [];

  const leaves = getLeaves(tree);
  const height = getTreeHeight(tree);
  const schedule = [];

  // Group leaves by their ancestor at replicationDepth
  // The "non-replicated root" (NRR) nodes are at replicationDepth level
  const nrrNodes = getNodesAtDepth(tree, replicationDepth);

  for (const nrrNode of nrrNodes) {
    const nrrLeaves = getLeaves(nrrNode);

    for (let li = 0; li < nrrLeaves.length; li++) {
      const leaf = nrrLeaves[li];

      // Replicated part: path from root down to (but not including) replicationDepth
      const pathToNRR = [];
      function findPathToNode(current, target) {
        if (current === target) return [current];
        if (current.children) {
          for (const c of current.children) {
            const r = findPathToNode(c, target);
            if (r) return [current, ...r];
          }
        }
        return null;
      }

      const fullPathToNRR = findPathToNode(tree, nrrNode) || [];
      const replicatedNodes = fullPathToNRR.slice(0, replicationDepth);

      // Non-replicated part: path from NRR node down to this leaf
      const pathFromNRR = findPathToNode(nrrNode, leaf) || [];

      // Build index segment
      const indexSegment = [];

      // Add replicated part
      for (const rn of replicatedNodes) {
        indexSegment.push({
          type: "index",
          nodeId: rn.id,
          replicated: true,
          keys: rn.keys,
        });
      }

      // Add non-replicated path
      for (const nrn of pathFromNRR) {
        indexSegment.push({
          type: "index",
          nodeId: nrn.id,
          replicated: false,
          keys: nrn.keys,
        });
      }

      // Data segment
      const dataStart = leaf.dataRange[0];
      const dataEnd = leaf.dataRange[1];
      const dataSegment = [];
      for (let d = dataStart; d <= dataEnd; d++) {
        dataSegment.push({
          type: "data",
          offset: d,
          label: dataItems[d]?.label || `D${d}`,
          key: dataItems[d]?.key,
        });
      }

      schedule.push({
        leafId: leaf.id,
        indexSegment,
        dataSegment,
        dataRange: [dataStart, dataEnd],
      });
    }
  }

  return schedule;
}

// Simulate search sequence
function simulateSearch(schedule, tuneInSlot, targetKey, tree, replicationDepth) {
  const steps = [];
  const totalSlots = schedule.reduce(
    (acc, seg) => acc + seg.indexSegment.length + seg.dataSegment.length,
    0
  );

  // Build flat timeline
  const timeline = [];
  let pos = 0;
  for (const seg of schedule) {
    for (const idx of seg.indexSegment) {
      timeline.push({ ...idx, pos, segLeaf: seg.leafId });
      pos++;
    }
    for (const dat of seg.dataSegment) {
      timeline.push({ ...dat, pos, segLeaf: seg.leafId });
      pos++;
    }
  }

  // Step 1: Initial probe — client tunes in at tuneInSlot
  const tuneInPos = Math.min(tuneInSlot, timeline.length - 1);
  const tuneInItem = timeline[tuneInPos];
  steps.push({
    step: 1,
    name: "Initial Probe",
    description: `Client tunes in at slot ${tuneInPos}. Encounters: ${tuneInItem.type === "index" ? `Index node [${tuneInItem.nodeId}]` : `Data item [${tuneInItem.label}]`}`,
    pos: tuneInPos,
    action: "tune_in",
    state: "active",
  });

  // Step 2: Find the next index segment
  let nextIndexPos = tuneInPos;
  // Scan forward to find the start of next index segment
  // First, skip past current segment
  let foundData = false;
  for (let i = tuneInPos; i < timeline.length; i++) {
    if (timeline[i].type === "data") foundData = true;
    if (foundData && timeline[i].type === "index" && timeline[i].replicated) {
      nextIndexPos = i;
      break;
    }
    // If we're already in an index at the beginning of a segment
    if (i === tuneInPos && timeline[i].type === "index" && timeline[i].replicated) {
      nextIndexPos = i;
      break;
    }
  }

  // If didn't find, wrap around
  if (nextIndexPos === tuneInPos && !timeline[tuneInPos].replicated) {
    for (let i = 0; i < tuneInPos; i++) {
      if (timeline[i].type === "index" && timeline[i].replicated) {
        nextIndexPos = i;
        break;
      }
    }
  }

  steps.push({
    step: 2,
    name: "Wait / Doze",
    description: `Client dozes until next index segment starting at slot ${nextIndexPos}`,
    pos: nextIndexPos,
    fromPos: tuneInPos,
    action: "doze",
    state: "doze",
  });

  // Step 3: Read index — navigate tree using replicated part
  // Find which segment's index contains the path to our target key
  let targetDataOffset = -1;
  const leaves = getLeaves(tree);
  for (const leaf of leaves) {
    if (leaf.keys.includes(targetKey)) {
      targetDataOffset = leaf.dataRange[0];
      break;
    }
    // Check if target key falls in this leaf's range
    if (targetKey >= leaf.keys[0] && targetKey <= leaf.keys[leaf.keys.length - 1]) {
      targetDataOffset = leaf.dataRange[0];
      break;
    }
  }
  if (targetDataOffset === -1) {
    // Find closest
    for (const leaf of leaves) {
      for (let i = 0; i < leaf.keys.length; i++) {
        if (leaf.keys[i] === targetKey) {
          targetDataOffset = leaf.dataRange[0] + i;
          break;
        }
      }
      if (targetDataOffset !== -1) break;
    }
  }

  // Find the segment that contains this data
  let targetSegIdx = -1;
  for (let s = 0; s < schedule.length; s++) {
    if (
      targetKey >= schedule[s].dataSegment[0]?.key &&
      targetKey <= schedule[s].dataSegment[schedule[s].dataSegment.length - 1]?.key
    ) {
      targetSegIdx = s;
      break;
    }
  }

  if (targetSegIdx === -1) {
    // Try exact match
    for (let s = 0; s < schedule.length; s++) {
      for (const d of schedule[s].dataSegment) {
        if (d.key === targetKey) {
          targetSegIdx = s;
          break;
        }
      }
      if (targetSegIdx !== -1) break;
    }
  }

  // Find the index segment for the target in the timeline
  let targetIndexStart = -1;
  let cumulativePos = 0;
  for (let s = 0; s < schedule.length; s++) {
    if (s === targetSegIdx) {
      targetIndexStart = cumulativePos;
      break;
    }
    cumulativePos += schedule[s].indexSegment.length + schedule[s].dataSegment.length;
  }

  if (targetIndexStart >= 0) {
    const seg = schedule[targetSegIdx];
    steps.push({
      step: 3,
      name: "Read Index",
      description: `Read index nodes [${seg.indexSegment.map((n) => n.nodeId).join(" → ")}] to locate data`,
      pos: targetIndexStart,
      endPos: targetIndexStart + seg.indexSegment.length - 1,
      action: "read_index",
      state: "active",
    });

    // Step 4: Navigate to data
    const dataStartPos = targetIndexStart + seg.indexSegment.length;
    let exactDataPos = dataStartPos;
    for (let i = dataStartPos; i < dataStartPos + seg.dataSegment.length; i++) {
      if (timeline[i] && timeline[i].key === targetKey) {
        exactDataPos = i;
        break;
      }
    }

    if (dataStartPos !== targetIndexStart + seg.indexSegment.length - 1) {
      steps.push({
        step: 4,
        name: "Doze to Data",
        description: `Client dozes and wakes at data offset slot ${exactDataPos}`,
        pos: exactDataPos,
        fromPos: targetIndexStart + seg.indexSegment.length - 1,
        action: "doze",
        state: "doze",
      });
    }

    steps.push({
      step: 5,
      name: "Retrieve Data",
      description: `Client retrieves data item "${timeline[exactDataPos]?.label || "?"}" (key=${targetKey}) at slot ${exactDataPos}`,
      pos: exactDataPos,
      action: "retrieve",
      state: "active",
    });
  }

  return { steps, timeline };
}

// ─── Color palette ───
const COLORS = {
  bg: "#0a0e17",
  surface: "#111827",
  surfaceHover: "#1a2332",
  border: "#1e293b",
  borderLight: "#334155",
  text: "#e2e8f0",
  textMuted: "#94a3b8",
  textDim: "#64748b",
  accent: "#22d3ee",
  accentDim: "#0e7490",
  replicated: "#8b5cf6",
  replicatedDim: "#6d28d9",
  nonReplicated: "#f59e0b",
  nonReplicatedDim: "#b45309",
  data: "#10b981",
  dataDim: "#047857",
  active: "#ef4444",
  doze: "#3b82f6",
  highlight: "#fbbf24",
  treeNode: "#1e293b",
  treeBorder: "#475569",
};

// ─── Main Component ───
export default function IndexingInAir() {
  const [step, setStep] = useState("input"); // input | tree | schedule | search
  const [fanout, setFanout] = useState(3);
  const [numItems, setNumItems] = useState(27);
  const [dataItems, setDataItems] = useState([]);
  const [tree, setTree] = useState(null);
  const [replicationDepth, setReplicationDepth] = useState(1);
  const [treeHeight, setTreeHeight] = useState(0);
  const [schedule, setSchedule] = useState([]);
  const [tuneInSlot, setTuneInSlot] = useState(0);
  const [searchKey, setSearchKey] = useState(1);
  const [searchResult, setSearchResult] = useState(null);
  const [activeStep, setActiveStep] = useState(-1);
  const [openNotes, setOpenNotes] = useState({});
  const timelineRef = useRef(null);

  const toggleNote = (id) => setOpenNotes((prev) => ({ ...prev, [id]: !prev[id] }));

  const NotesPanel = ({ id, items }) => {
    const isOpen = openNotes[id];
    return (
      <div style={{ marginBottom: 14 }}>
        <button
          onClick={() => toggleNote(id)}
          style={{
            background: "transparent",
            border: `1px solid ${COLORS.borderLight}`,
            borderRadius: 5,
            color: COLORS.textMuted,
            padding: "5px 12px",
            fontSize: 10,
            fontFamily: "'JetBrains Mono', monospace",
            cursor: "pointer",
            letterSpacing: 0.5,
            textTransform: "uppercase",
            display: "flex",
            alignItems: "center",
            gap: 6,
          }}
        >
          <span style={{ fontSize: 8, transform: isOpen ? "rotate(90deg)" : "rotate(0deg)", transition: "transform 0.2s", display: "inline-block" }}>&#9654;</span>
          Quick Reference Notes
        </button>
        {isOpen && (
          <div
            style={{
              marginTop: 8,
              padding: "12px 16px",
              background: COLORS.bg,
              border: `1px solid ${COLORS.border}`,
              borderLeft: `3px solid ${COLORS.accentDim}`,
              borderRadius: 6,
              fontSize: 11,
              lineHeight: 1.7,
              color: COLORS.textMuted,
              fontFamily: "'JetBrains Mono', monospace",
            }}
          >
            {items.map((item, i) => (
              <div key={i} style={{ marginBottom: i < items.length - 1 ? 8 : 0 }}>
                {item.heading && (
                  <div style={{ color: COLORS.accent, fontWeight: 700, fontSize: 10, textTransform: "uppercase", letterSpacing: 1, marginBottom: 3 }}>
                    {item.heading}
                  </div>
                )}
                <div style={{ color: COLORS.textMuted }}>{item.text}</div>
              </div>
            ))}
          </div>
        )}
      </div>
    );
  };

  // Generate data items
  const generateData = useCallback(() => {
    const items = [];
    for (let i = 0; i < numItems; i++) {
      items.push({ key: i + 1, label: `D${i}` });
    }
    setDataItems(items);
    const t = buildTree(items, fanout);
    if (t) {
      assignDepths(t);
      const h = getTreeHeight(t);
      setTree(t);
      setTreeHeight(h);
      setReplicationDepth(Math.min(1, h));
    }
    setStep("tree");
    setSchedule([]);
    setSearchResult(null);
  }, [numItems, fanout]);

  // Generate schedule
  const generateSchedule = useCallback(() => {
    if (!tree) return;
    const sched = buildBroadcastSchedule(tree, replicationDepth, dataItems, fanout);
    setSchedule(sched);
    setStep("schedule");
    setSearchResult(null);
    setSearchKey(Math.min(searchKey, numItems));
  }, [tree, replicationDepth, dataItems, fanout, searchKey, numItems]);

  // Run search
  const runSearch = useCallback(() => {
    if (schedule.length === 0) return;
    const result = simulateSearch(schedule, tuneInSlot, searchKey, tree, replicationDepth);
    setSearchResult(result);
    setStep("search");
    setActiveStep(0);
  }, [schedule, tuneInSlot, searchKey, tree, replicationDepth]);

  // Scroll timeline to active position
  useEffect(() => {
    if (searchResult && activeStep >= 0 && timelineRef.current) {
      const stepData = searchResult.steps[activeStep];
      if (stepData) {
        const slotEl = timelineRef.current.querySelector(`[data-pos="${stepData.pos}"]`);
        if (slotEl) {
          slotEl.scrollIntoView({ behavior: "smooth", inline: "center", block: "nearest" });
        }
      }
    }
  }, [activeStep, searchResult]);

  // Tree visualization
  const TreeView = ({ tree, replicationDepth, highlightPath }) => {
    if (!tree) return null;
    const levels = flattenByLevel(tree);
    const maxDepth = Math.max(...Object.keys(levels).map(Number));
    const highlightIds = new Set((highlightPath || []).map((n) => n.id));

    return (
      <div style={{ overflowX: "auto", padding: "16px 0" }}>
        {Object.keys(levels)
          .sort((a, b) => a - b)
          .map((depth) => {
            const d = Number(depth);
            const isAboveReplication = d < replicationDepth;
            const isAtReplication = d === replicationDepth;

            return (
              <div key={depth}>
                {isAtReplication && (
                  <div
                    style={{
                      borderTop: `2px dashed ${COLORS.accent}`,
                      margin: "4px 0",
                      position: "relative",
                    }}
                  >
                    <span
                      style={{
                        position: "absolute",
                        right: 0,
                        top: -10,
                        fontSize: 10,
                        color: COLORS.accent,
                        background: COLORS.bg,
                        padding: "0 4px",
                        fontFamily: "'JetBrains Mono', monospace",
                      }}
                    >
                      replication horizon (depth {replicationDepth})
                    </span>
                  </div>
                )}
                <div
                  style={{
                    display: "flex",
                    justifyContent: "center",
                    gap: 8,
                    marginBottom: 8,
                    flexWrap: "wrap",
                  }}
                >
                  {levels[depth].map((node) => {
                    const isHighlighted = highlightIds.has(node.id);
                    const isReplicated = d < replicationDepth;
                    const isLeaf = node.level === "leaf";

                    let bgColor = COLORS.treeNode;
                    let borderColor = COLORS.treeBorder;
                    if (isHighlighted) {
                      bgColor = COLORS.active + "33";
                      borderColor = COLORS.active;
                    } else if (isReplicated) {
                      bgColor = COLORS.replicated + "22";
                      borderColor = COLORS.replicated;
                    }

                    return (
                      <div
                        key={node.id}
                        style={{
                          background: bgColor,
                          border: `1.5px solid ${borderColor}`,
                          borderRadius: isLeaf ? 4 : 20,
                          padding: "4px 10px",
                          textAlign: "center",
                          minWidth: 40,
                          transition: "all 0.3s",
                        }}
                      >
                        <div
                          style={{
                            fontSize: 11,
                            fontWeight: 700,
                            color: isHighlighted ? COLORS.active : isReplicated ? COLORS.replicated : COLORS.accent,
                            fontFamily: "'JetBrains Mono', monospace",
                          }}
                        >
                          {node.id}
                        </div>
                        <div
                          style={{
                            fontSize: 9,
                            color: COLORS.textDim,
                            fontFamily: "'JetBrains Mono', monospace",
                          }}
                        >
                          [{node.keys.join(",")}]
                        </div>
                      </div>
                    );
                  })}
                </div>
              </div>
            );
          })}
        <div style={{ display: "flex", gap: 12, justifyContent: "center", marginTop: 8 }}>
          <span style={{ fontSize: 10, color: COLORS.replicated, fontFamily: "'JetBrains Mono', monospace" }}>
            ■ Replicated (above horizon)
          </span>
          <span style={{ fontSize: 10, color: COLORS.treeBorder, fontFamily: "'JetBrains Mono', monospace" }}>
            ■ Non-Replicated (below horizon)
          </span>
        </div>
      </div>
    );
  };

  // Schedule visualization
  const ScheduleView = ({ schedule, searchResult, activeStep: as2 }) => {
    // Build flat timeline
    const timeline = [];
    let pos = 0;
    for (const seg of schedule) {
      for (const idx of seg.indexSegment) {
        timeline.push({ ...idx, pos, segLeaf: seg.leafId });
        pos++;
      }
      for (const dat of seg.dataSegment) {
        timeline.push({ ...dat, pos, segLeaf: seg.leafId });
        pos++;
      }
    }

    // Compute index_pointer for each slot (offset to next index segment start)
    // and bcast_pointer (offset to next broadcast cycle = totalSlots)
    const segBoundaries = [];
    let cumPos = 0;
    for (const seg of schedule) {
      segBoundaries.push(cumPos); // start of this segment's index
      cumPos += seg.indexSegment.length + seg.dataSegment.length;
    }
    const totalLen = cumPos;

    function getNextIndexStart(currentPos) {
      for (const b of segBoundaries) {
        if (b > currentPos) return b;
      }
      return totalLen; // wraps to next broadcast
    }

    // Determine highlighted positions from search
    const highlightedPositions = {};
    if (searchResult && as2 >= 0) {
      for (let i = 0; i <= as2; i++) {
        const s = searchResult.steps[i];
        if (s) {
          if (s.action === "tune_in") highlightedPositions[s.pos] = "tune_in";
          if (s.action === "read_index") {
            for (let p = s.pos; p <= (s.endPos || s.pos); p++) {
              highlightedPositions[p] = "read_index";
            }
          }
          if (s.action === "retrieve") highlightedPositions[s.pos] = "retrieve";
        }
      }
    }

    // Group by segment for visual separation
    let segStart = 0;
    const segments = schedule.map((seg, si) => {
      const start = segStart;
      const len = seg.indexSegment.length + seg.dataSegment.length;
      segStart += len;
      return { ...seg, start, len, segIndex: si };
    });

    const [hoveredSlot, setHoveredSlot] = useState(null);

    return (
      <div ref={timelineRef} style={{ overflowX: "auto", padding: "8px 0" }}>
        {/* Slot detail tooltip */}
        {hoveredSlot !== null && hoveredSlot < timeline.length && (
          <div style={{
            background: COLORS.surface,
            border: `1px solid ${COLORS.accent}`,
            borderRadius: 6,
            padding: "8px 12px",
            marginBottom: 8,
            fontSize: 10,
            fontFamily: "'JetBrains Mono', monospace",
            color: COLORS.textMuted,
            display: "flex",
            gap: 16,
            flexWrap: "wrap",
          }}>
            <span>
              <span style={{ color: COLORS.accent }}>SLOT {hoveredSlot}</span>
              {" | "}
              {timeline[hoveredSlot].type === "index"
                ? <span style={{ color: timeline[hoveredSlot].replicated ? COLORS.replicated : COLORS.nonReplicated }}>Index [{timeline[hoveredSlot].nodeId}]</span>
                : <span style={{ color: COLORS.data }}>Data [{timeline[hoveredSlot].label}] key={timeline[hoveredSlot].key}</span>
              }
            </span>
            <span>
              <span style={{ color: COLORS.nonReplicated }}>index_pointer:</span> {getNextIndexStart(hoveredSlot)}
              <span style={{ color: COLORS.textDim }}> (next index segment)</span>
            </span>
            <span>
              <span style={{ color: COLORS.replicated }}>bcast_pointer:</span> {totalLen}
              <span style={{ color: COLORS.textDim }}> (next broadcast cycle)</span>
            </span>
          </div>
        )}
        <div style={{ display: "flex", gap: 0, minWidth: "max-content" }}>
          {segments.map((seg, si) => (
            <div
              key={si}
              style={{
                display: "flex",
                gap: 0,
                borderRight: si < segments.length - 1 ? `2px solid ${COLORS.borderLight}` : "none",
                paddingRight: si < segments.length - 1 ? 2 : 0,
                marginRight: si < segments.length - 1 ? 2 : 0,
              }}
            >
              {/* Index slots */}
              {seg.indexSegment.map((idx, ii) => {
                const p = seg.start + ii;
                const hl = highlightedPositions[p];
                let bg = idx.replicated ? COLORS.replicated + "55" : COLORS.nonReplicated + "55";
                let border = idx.replicated ? COLORS.replicated : COLORS.nonReplicated;
                if (hl === "tune_in") {
                  bg = COLORS.active + "88";
                  border = COLORS.active;
                }
                if (hl === "read_index") {
                  bg = COLORS.doze + "88";
                  border = COLORS.doze;
                }
                return (
                  <div
                    key={`i${p}`}
                    data-pos={p}
                    onMouseEnter={() => setHoveredSlot(p)}
                    onMouseLeave={() => setHoveredSlot(null)}
                    style={{
                      width: 32,
                      height: 44,
                      background: bg,
                      border: `1px solid ${border}`,
                      display: "flex",
                      flexDirection: "column",
                      alignItems: "center",
                      justifyContent: "center",
                      fontSize: 8,
                      fontFamily: "'JetBrains Mono', monospace",
                      color: COLORS.text,
                      position: "relative",
                      borderRadius: 2,
                      margin: "0 0.5px",
                      cursor: "pointer",
                    }}
                  >
                    <div style={{ fontWeight: 700, fontSize: 9 }}>{idx.nodeId}</div>
                    <div style={{ fontSize: 7, color: COLORS.textDim }}>{p}</div>
                  </div>
                );
              })}
              {/* Data slots */}
              {seg.dataSegment.map((dat, di) => {
                const p = seg.start + seg.indexSegment.length + di;
                const hl = highlightedPositions[p];
                let bg = COLORS.data + "33";
                let border = COLORS.dataDim;
                if (hl === "tune_in") {
                  bg = COLORS.active + "88";
                  border = COLORS.active;
                }
                if (hl === "retrieve") {
                  bg = COLORS.highlight + "88";
                  border = COLORS.highlight;
                }
                return (
                  <div
                    key={`d${p}`}
                    data-pos={p}
                    onMouseEnter={() => setHoveredSlot(p)}
                    onMouseLeave={() => setHoveredSlot(null)}
                    style={{
                      width: 32,
                      height: 44,
                      background: bg,
                      border: `1px solid ${border}`,
                      display: "flex",
                      flexDirection: "column",
                      alignItems: "center",
                      justifyContent: "center",
                      fontSize: 8,
                      fontFamily: "'JetBrains Mono', monospace",
                      color: COLORS.text,
                      borderRadius: 2,
                      margin: "0 0.5px",
                      cursor: "pointer",
                    }}
                  >
                    <div style={{ fontWeight: 600, fontSize: 8 }}>{dat.label}</div>
                    <div style={{ fontSize: 7, color: COLORS.textDim }}>{p}</div>
                  </div>
                );
              })}
            </div>
          ))}
        </div>
        <p style={{ fontSize: 9, color: COLORS.textDim, marginTop: 6, fontFamily: "'JetBrains Mono', monospace" }}>
          Hover over any slot to see its header info (index_pointer, bcast_pointer)
        </p>
        {/* Legend */}
        <div style={{ display: "flex", gap: 14, marginTop: 6, flexWrap: "wrap" }}>
          <span style={{ fontSize: 10, color: COLORS.replicated, fontFamily: "'JetBrains Mono', monospace" }}>
            ■ Replicated Index
          </span>
          <span style={{ fontSize: 10, color: COLORS.nonReplicated, fontFamily: "'JetBrains Mono', monospace" }}>
            ■ Non-Replicated Index
          </span>
          <span style={{ fontSize: 10, color: COLORS.data, fontFamily: "'JetBrains Mono', monospace" }}>
            ■ Data
          </span>
          {searchResult && (
            <>
              <span style={{ fontSize: 10, color: COLORS.active, fontFamily: "'JetBrains Mono', monospace" }}>
                ■ Tune-in Point
              </span>
              <span style={{ fontSize: 10, color: COLORS.doze, fontFamily: "'JetBrains Mono', monospace" }}>
                ■ Index Read
              </span>
              <span style={{ fontSize: 10, color: COLORS.highlight, fontFamily: "'JetBrains Mono', monospace" }}>
                ■ Retrieved
              </span>
            </>
          )}
        </div>
      </div>
    );
  };

  // ─── Input fields styling ───
  const inputStyle = {
    background: COLORS.surface,
    border: `1px solid ${COLORS.border}`,
    borderRadius: 6,
    color: COLORS.text,
    padding: "8px 12px",
    fontSize: 14,
    fontFamily: "'JetBrains Mono', monospace",
    width: "100%",
    outline: "none",
    boxSizing: "border-box",
  };

  const labelStyle = {
    fontSize: 11,
    color: COLORS.textMuted,
    fontFamily: "'JetBrains Mono', monospace",
    textTransform: "uppercase",
    letterSpacing: 1,
    marginBottom: 4,
    display: "block",
  };

  const btnPrimary = {
    background: `linear-gradient(135deg, ${COLORS.accent}, ${COLORS.accentDim})`,
    color: "#000",
    border: "none",
    borderRadius: 6,
    padding: "10px 20px",
    fontSize: 13,
    fontWeight: 700,
    fontFamily: "'JetBrains Mono', monospace",
    cursor: "pointer",
    textTransform: "uppercase",
    letterSpacing: 1,
  };

  const btnSecondary = {
    background: "transparent",
    color: COLORS.accent,
    border: `1px solid ${COLORS.accent}`,
    borderRadius: 6,
    padding: "8px 16px",
    fontSize: 12,
    fontWeight: 600,
    fontFamily: "'JetBrains Mono', monospace",
    cursor: "pointer",
    letterSpacing: 0.5,
  };

  const sectionStyle = {
    background: COLORS.surface,
    border: `1px solid ${COLORS.border}`,
    borderRadius: 10,
    padding: 20,
    marginBottom: 16,
  };

  const headingStyle = {
    fontSize: 14,
    fontWeight: 700,
    color: COLORS.accent,
    fontFamily: "'JetBrains Mono', monospace",
    textTransform: "uppercase",
    letterSpacing: 1.5,
    marginBottom: 14,
  };

  const totalSlots = schedule.reduce(
    (acc, seg) => acc + seg.indexSegment.length + seg.dataSegment.length,
    0
  );

  return (
    <div
      style={{
        background: COLORS.bg,
        minHeight: "100vh",
        color: COLORS.text,
        fontFamily: "'Segoe UI', system-ui, sans-serif",
        padding: "20px",
        boxSizing: "border-box",
      }}
    >
      {/* Header */}
      <div
        style={{
          textAlign: "center",
          marginBottom: 24,
          padding: "16px 0",
          borderBottom: `1px solid ${COLORS.border}`,
        }}
      >
        <h1
          style={{
            fontSize: 22,
            fontWeight: 800,
            fontFamily: "'JetBrains Mono', monospace",
            color: COLORS.accent,
            margin: 0,
            letterSpacing: 2,
          }}
        >
          INDEXING DATA IN AIR
        </h1>
        <p
          style={{
            fontSize: 11,
            color: COLORS.textDim,
            marginTop: 6,
            fontFamily: "'JetBrains Mono', monospace",
            letterSpacing: 1,
          }}
        >
          Partial Replication Scheme — Broadcast Index Simulator
        </p>
      </div>

      {/* Overview Notes */}
      <NotesPanel
        id="overview"
        items={[
          {
            heading: "What is Indexing in Air?",
            text: "In broadcast-based data services, the server broadcasts data on a public wireless channel. Mobile clients tune in to retrieve requested items. Indexing in air means interleaving index information with data in the broadcast so clients can predict when their data will arrive and doze in between.",
          },
          {
            heading: "Why it matters",
            text: "Response time is the total wait from request to receipt. Tuning time is how long the device radio is actually powered on. Minimizing tuning time saves battery. Indexing lets clients enter doze mode and only wake at the right moment.",
          },
          {
            heading: "Key tradeoff",
            text: "Probe wait: time to reach the next index segment. Bcast wait: time after reading the index until the data arrives. Replicating more index reduces probe wait but increases broadcast length (and thus bcast wait).",
          },
          {
            heading: "Three replication strategies",
            text: "Non-replicated distribution: index nodes broadcast once, no duplication. Entire path replication: full root-to-leaf path repeated before every data segment. Partial path replication (distributed indexing): only nodes above the replication horizon are repeated; nodes below are broadcast once. This is the balanced approach.",
          },
        ]}
      />

      {/* Step 1: Input Configuration */}
      <div style={sectionStyle}>
        <div style={headingStyle}>1 — Configuration</div>
        <NotesPanel
          id="config"
          items={[
            {
              heading: "Data items",
              text: "These represent database records broadcast on the wireless channel. Each has a search attribute (key) used for indexing. Items with the same attribute are clustered consecutively in the broadcast.",
            },
            {
              heading: "Fanout (branching factor)",
              text: "The maximum number of children per internal node in the B+ index tree. A fanout of 3 means each node has up to 3 children. Higher fanout means a shallower tree (fewer index levels) but wider nodes.",
            },
            {
              heading: "Demo suggestion",
              text: "Start with 27 items and fanout 3. This produces a clean 3-level tree (root I, level a with 3 nodes, level b with 9 nodes, 9 leaf nodes with 3 items each) matching the textbook example exactly.",
            },
          ]}
        />
        <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 14 }}>
          <div>
            <label style={labelStyle}>Number of Data Items</label>
            <input
              type="number"
              min={3}
              max={81}
              value={numItems}
              onChange={(e) => setNumItems(Math.max(3, Math.min(81, parseInt(e.target.value) || 3)))}
              style={inputStyle}
            />
          </div>
          <div>
            <label style={labelStyle}>Fanout (Branching Factor)</label>
            <input
              type="number"
              min={2}
              max={5}
              value={fanout}
              onChange={(e) => setFanout(Math.max(2, Math.min(5, parseInt(e.target.value) || 2)))}
              style={inputStyle}
            />
          </div>
        </div>
        <div style={{ marginTop: 14 }}>
          <button onClick={generateData} style={btnPrimary}>
            Generate Index Tree
          </button>
        </div>
      </div>

      {/* Step 2: Tree + Replication Level */}
      {tree && step !== "input" && (
        <div style={sectionStyle}>
          <div style={headingStyle}>2 — Index Tree Structure</div>
          <NotesPanel
            id="tree"
            items={[
              {
                heading: "Tree structure",
                text: "The index is organized as a B+ tree. The root (I) is at depth 0. Intermediate nodes (a-level, b-level) guide the search. Leaf nodes (c-level) point directly to data segments. Each leaf covers a contiguous range of data items.",
              },
              {
                heading: "Replication horizon",
                text: "The dashed line divides the tree into two zones. Above: replicated part -- these nodes are repeated in every index segment throughout the broadcast. Below: non-replicated part -- these nodes appear only once, in the index segment immediately before their corresponding data.",
              },
              {
                heading: "Depth = 0 (no replication)",
                text: "Non-replicated distribution. The entire index is broadcast once. A client that tunes in mid-broadcast must wait for the next full broadcast cycle to access the root. Lowest broadcast overhead, highest probe wait.",
              },
              {
                heading: "Depth = max (full replication)",
                text: "Entire path replication. Every index segment contains the complete root-to-leaf path. Lowest probe wait (client always finds a nearby root), but the broadcast becomes much longer due to repeated index nodes.",
              },
              {
                heading: "Depth = middle (partial replication)",
                text: "The sweet spot. Only upper levels are replicated. The client can quickly find a replicated ancestor to navigate down to the needed non-replicated subtree. Balances probe wait and broadcast length.",
              },
            ]}
          />
          <p style={{ fontSize: 12, color: COLORS.textMuted, marginBottom: 8, fontFamily: "'JetBrains Mono', monospace" }}>
            Tree height: {treeHeight} | Fanout: {fanout} | Leaves: {getLeaves(tree).length} | Data items: {numItems}
          </p>
          <TreeView tree={tree} replicationDepth={replicationDepth} />

          <div style={{ marginTop: 16, borderTop: `1px solid ${COLORS.border}`, paddingTop: 14 }}>
            <label style={labelStyle}>
              Replication Level (depth 0=root only, {treeHeight}=full tree replicated)
            </label>
            <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
              <input
                type="range"
                min={0}
                max={treeHeight}
                value={replicationDepth}
                onChange={(e) => setReplicationDepth(parseInt(e.target.value))}
                style={{ flex: 1, accentColor: COLORS.accent }}
              />
              <span
                style={{
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 14,
                  color: COLORS.accent,
                  fontWeight: 700,
                  minWidth: 24,
                  textAlign: "center",
                }}
              >
                {replicationDepth}
              </span>
            </div>
            <p style={{ fontSize: 11, color: COLORS.textDim, marginTop: 6, fontFamily: "'JetBrains Mono', monospace" }}>
              Nodes above depth {replicationDepth} are replicated before every data segment.
              {replicationDepth === 0
                ? " (No replication — non-replicated distribution)"
                : replicationDepth >= treeHeight
                  ? " (Entire path replication)"
                  : " (Partial path replication)"}
            </p>
          </div>
          <div style={{ marginTop: 14 }}>
            <button onClick={generateSchedule} style={btnPrimary}>
              Generate Broadcast Schedule
            </button>
          </div>
        </div>
      )}

      {/* Step 3: Broadcast Schedule */}
      {schedule.length > 0 && (step === "schedule" || step === "search") && (
        <div style={sectionStyle}>
          <div style={headingStyle}>3 — Broadcast Schedule</div>
          <NotesPanel
            id="schedule"
            items={[
              {
                heading: "How to read the schedule",
                text: "The broadcast is a linear sequence of slots. Each segment consists of: (1) replicated index nodes (purple) repeated for every segment, (2) non-replicated index nodes (amber) specific to this segment's subtree path, (3) data items (green) belonging to the leaf node. Vertical dividers separate segments.",
              },
              {
                heading: "Slot numbering",
                text: "Each slot has a position number shown below it. This is the broadcast offset -- the absolute position in the broadcast cycle. The client uses these offsets to know when to wake up and tune in.",
              },
              {
                heading: "Segment detail table",
                text: "The table below the timeline shows which index nodes are replicated vs non-replicated for each segment, plus the data range. Rep(bX) from the lecture maps to the Replicated column. Ind(bX) maps to the full index path (replicated + non-replicated).",
              },
              {
                heading: "Control index",
                text: "In practice, each replicated node also carries a control index with two entries: (offset_of_data_begin, begin) telling where the next data segment starts, and (offset_of_next_subtree, next_index_pointer) telling where the next sibling subtree index begins. This lets the client decide whether to follow this subtree or skip ahead.",
              },
            ]}
          />
          <p style={{ fontSize: 11, color: COLORS.textMuted, marginBottom: 8, fontFamily: "'JetBrains Mono', monospace" }}>
            Total broadcast slots: {totalSlots} | Segments: {schedule.length} | Each segment: [replicated index → non-replicated index → data]
          </p>
          <ScheduleView schedule={schedule} searchResult={searchResult} activeStep={activeStep} />

          {/* Segment detail table */}
          <div style={{ marginTop: 14, overflowX: "auto" }}>
            <table
              style={{
                width: "100%",
                borderCollapse: "collapse",
                fontSize: 11,
                fontFamily: "'JetBrains Mono', monospace",
              }}
            >
              <thead>
                <tr style={{ borderBottom: `1px solid ${COLORS.border}` }}>
                  <th style={{ padding: "6px 8px", textAlign: "left", color: COLORS.textDim }}>Segment</th>
                  <th style={{ padding: "6px 8px", textAlign: "left", color: COLORS.textDim }}>Leaf</th>
                  <th style={{ padding: "6px 8px", textAlign: "left", color: COLORS.replicated }}>Replicated</th>
                  <th style={{ padding: "6px 8px", textAlign: "left", color: COLORS.nonReplicated }}>Non-Replicated</th>
                  <th style={{ padding: "6px 8px", textAlign: "left", color: COLORS.data }}>Data Range</th>
                </tr>
              </thead>
              <tbody>
                {schedule.map((seg, si) => (
                  <tr key={si} style={{ borderBottom: `1px solid ${COLORS.border}22` }}>
                    <td style={{ padding: "5px 8px", color: COLORS.text }}>{si + 1}</td>
                    <td style={{ padding: "5px 8px", color: COLORS.accent }}>{seg.leafId}</td>
                    <td style={{ padding: "5px 8px", color: COLORS.replicated }}>
                      {seg.indexSegment
                        .filter((n) => n.replicated)
                        .map((n) => n.nodeId)
                        .join(", ") || "—"}
                    </td>
                    <td style={{ padding: "5px 8px", color: COLORS.nonReplicated }}>
                      {seg.indexSegment
                        .filter((n) => !n.replicated)
                        .map((n) => n.nodeId)
                        .join(", ")}
                    </td>
                    <td style={{ padding: "5px 8px", color: COLORS.data }}>
                      [{seg.dataRange[0]}..{seg.dataRange[1]}]
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>

          {/* Broadcast Statistics */}
          <div style={{ marginTop: 16, borderTop: `1px solid ${COLORS.border}`, paddingTop: 14 }}>
            <div style={{ ...headingStyle, fontSize: 12, marginBottom: 10 }}>Broadcast Statistics</div>
            {(() => {
              const totalIndexSlots = schedule.reduce((a, s) => a + s.indexSegment.length, 0);
              const totalDataSlots = schedule.reduce((a, s) => a + s.dataSegment.length, 0);
              const replicatedSlots = schedule.reduce((a, s) => a + s.indexSegment.filter(n => n.replicated).length, 0);
              const nonReplicatedSlots = totalIndexSlots - replicatedSlots;
              const indexOverhead = ((totalIndexSlots / totalSlots) * 100).toFixed(1);
              const treeDepth = treeHeight;
              const indexSizeFormula = Array.from({length: treeDepth}, (_, i) => Math.pow(fanout, i)).reduce((a, b) => a + b, 0);
              return (
                <div style={{ display: "grid", gridTemplateColumns: "repeat(auto-fit, minmax(140px, 1fr))", gap: 10 }}>
                  {[
                    { label: "|D| (data slots)", value: totalDataSlots, color: COLORS.data, note: "Total data items in broadcast" },
                    { label: "|I| (index slots)", value: totalIndexSlots, color: COLORS.nonReplicated, note: "Total index slots (replicated + non-replicated)" },
                    { label: "Replicated slots", value: replicatedSlots, color: COLORS.replicated, note: "Index nodes repeated across segments" },
                    { label: "Non-replicated slots", value: nonReplicatedSlots, color: COLORS.nonReplicated, note: "Index nodes appearing once" },
                    { label: "Broadcast length", value: totalSlots, color: COLORS.accent, note: "|D| + |I| = total slots per cycle" },
                    { label: "Index overhead", value: `${indexOverhead}%`, color: COLORS.highlight, note: "|I| / (|D| + |I|) as percentage" },
                    { label: "Tree depth (k)", value: treeDepth, color: COLORS.textMuted, note: `k = ceil(log_${fanout}(|D|/C))` },
                    { label: "Tuning time (theoretical)", value: `1 + k + C = 1 + ${treeDepth} + ${fanout} = ${1 + treeDepth + fanout}`, color: COLORS.active, note: "Initial probe + tree traversal + data read" },
                  ].map((stat, i) => (
                    <div key={i} style={{
                      background: COLORS.bg,
                      border: `1px solid ${COLORS.border}`,
                      borderRadius: 6,
                      padding: "10px 12px",
                    }}>
                      <div style={{ fontSize: 9, color: COLORS.textDim, fontFamily: "'JetBrains Mono', monospace", textTransform: "uppercase", letterSpacing: 0.5 }}>{stat.label}</div>
                      <div style={{ fontSize: 16, fontWeight: 700, color: stat.color, fontFamily: "'JetBrains Mono', monospace", marginTop: 2 }}>{stat.value}</div>
                      <div style={{ fontSize: 8, color: COLORS.textDim, fontFamily: "'JetBrains Mono', monospace", marginTop: 3 }}>{stat.note}</div>
                    </div>
                  ))}
                </div>
              );
            })()}
          </div>
        </div>
      )}

      {/* Step 4: Search Simulation */}
      {schedule.length > 0 && (step === "schedule" || step === "search") && (
        <div style={sectionStyle}>
          <div style={headingStyle}>4 — Search Simulation</div>
          <NotesPanel
            id="search"
            items={[
              {
                heading: "Access protocol (3 phases)",
                text: "Step 1 -- Initial probe: client tunes into the broadcast at an arbitrary point and reads the current slot to determine its position. Step 2 -- Index access: client waits (dozes) until the next replicated index segment, then reads the index tree to find the offset of the target data. Step 3 -- Data access: client dozes again until the target data slot arrives, then wakes to retrieve it.",
              },
              {
                heading: "Active vs doze states",
                text: "ACTIVE means the device radio is powered on, consuming energy. DOZE means the radio is off, conserving battery. The whole point of indexing in air is to maximize doze time. Tuning time = total active time across all steps.",
              },
              {
                heading: "Tune-in slot",
                text: "This simulates where the client randomly joins the broadcast. A client might tune in during a data segment (must wait for next index), during a replicated index (can start navigating immediately), or during a non-replicated index (may need the replicated parent first).",
              },
              {
                heading: "What to show your professor",
                text: "Try different tune-in points for the same search key to show how probe wait changes. Then change the replication level and regenerate -- show that higher replication reduces the distance to the nearest usable index but increases total broadcast length. The search steps panel highlights exactly which slots the client is active vs dozing.",
              },
            ]}
          />
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 14 }}>
            <div>
              <label style={labelStyle}>Client Tune-in Slot (0–{totalSlots - 1})</label>
              <input
                type="number"
                min={0}
                max={totalSlots - 1}
                value={tuneInSlot}
                onChange={(e) =>
                  setTuneInSlot(Math.max(0, Math.min(totalSlots - 1, parseInt(e.target.value) || 0)))
                }
                style={inputStyle}
              />
            </div>
            <div>
              <label style={labelStyle}>Search Key (1–{numItems})</label>
              <input
                type="number"
                min={1}
                max={numItems}
                value={searchKey}
                onChange={(e) =>
                  setSearchKey(Math.max(1, Math.min(numItems, parseInt(e.target.value) || 1)))
                }
                style={inputStyle}
              />
            </div>
          </div>
          <div style={{ marginTop: 14, display: "flex", gap: 10 }}>
            <button onClick={runSearch} style={btnPrimary}>
              Run Search
            </button>
            {searchResult && (
              <>
                <button
                  onClick={() => setActiveStep(Math.max(0, activeStep - 1))}
                  disabled={activeStep <= 0}
                  style={{ ...btnSecondary, opacity: activeStep <= 0 ? 0.4 : 1 }}
                >
                  ← Prev Step
                </button>
                <button
                  onClick={() => setActiveStep(Math.min(searchResult.steps.length - 1, activeStep + 1))}
                  disabled={activeStep >= searchResult.steps.length - 1}
                  style={{
                    ...btnSecondary,
                    opacity: activeStep >= searchResult.steps.length - 1 ? 0.4 : 1,
                  }}
                >
                  Next Step →
                </button>
              </>
            )}
          </div>
        </div>
      )}

      {/* Search Result */}
      {searchResult && step === "search" && (
        <div style={sectionStyle}>
          <div style={headingStyle}>Search Sequence</div>
          <NotesPanel
            id="results"
            items={[
              {
                heading: "Reading the results",
                text: "Each step shows what the client does and whether the radio is active or dozing. Click any step to highlight the corresponding slot(s) in the broadcast schedule above. Red = tune-in point, blue = index being read, yellow = retrieved data item.",
              },
              {
                heading: "Tuning time calculation",
                text: "Tuning time = sum of all ACTIVE step durations. In this simulation, each slot = 1 time unit. Count the active slots across all steps to get total tuning time. Compare this to response time (total slots from tune-in to retrieval, including doze periods).",
              },
              {
                heading: "Performance comparison",
                text: "To demonstrate the tradeoff: run the same search with replication depth 0 (non-replicated), depth 1 (partial), and depth max (full). Note how probe wait decreases but total broadcast length increases. Partial replication offers the best balance for most access patterns.",
              },
            ]}
          />
          <div style={{ display: "flex", flexDirection: "column", gap: 8 }}>
            {searchResult.steps.map((s, i) => {
              const isActive = i === activeStep;
              const isPast = i < activeStep;
              return (
                <div
                  key={i}
                  onClick={() => setActiveStep(i)}
                  style={{
                    display: "flex",
                    gap: 12,
                    alignItems: "flex-start",
                    padding: "10px 14px",
                    borderRadius: 8,
                    background: isActive
                      ? COLORS.accent + "18"
                      : isPast
                        ? COLORS.surface
                        : "transparent",
                    border: `1px solid ${isActive ? COLORS.accent : isPast ? COLORS.border : "transparent"}`,
                    cursor: "pointer",
                    transition: "all 0.2s",
                    opacity: !isPast && !isActive ? 0.4 : 1,
                  }}
                >
                  <div
                    style={{
                      width: 28,
                      height: 28,
                      borderRadius: "50%",
                      display: "flex",
                      alignItems: "center",
                      justifyContent: "center",
                      fontSize: 12,
                      fontWeight: 700,
                      fontFamily: "'JetBrains Mono', monospace",
                      flexShrink: 0,
                      background:
                        s.state === "active"
                          ? COLORS.active + "33"
                          : s.state === "doze"
                            ? COLORS.doze + "33"
                            : COLORS.surface,
                      color:
                        s.state === "active"
                          ? COLORS.active
                          : s.state === "doze"
                            ? COLORS.doze
                            : COLORS.text,
                      border: `1.5px solid ${s.state === "active" ? COLORS.active : s.state === "doze" ? COLORS.doze : COLORS.border}`,
                    }}
                  >
                    {s.step}
                  </div>
                  <div>
                    <div
                      style={{
                        fontSize: 12,
                        fontWeight: 700,
                        color: isActive ? COLORS.accent : COLORS.text,
                        fontFamily: "'JetBrains Mono', monospace",
                      }}
                    >
                      {s.name}{" "}
                      <span
                        style={{
                          fontSize: 9,
                          padding: "1px 6px",
                          borderRadius: 4,
                          background:
                            s.state === "active" ? COLORS.active + "33" : COLORS.doze + "33",
                          color: s.state === "active" ? COLORS.active : COLORS.doze,
                          marginLeft: 6,
                        }}
                      >
                        {s.state === "active" ? "ACTIVE" : "DOZE"}
                      </span>
                    </div>
                    <div
                      style={{
                        fontSize: 11,
                        color: COLORS.textMuted,
                        marginTop: 3,
                        fontFamily: "'JetBrains Mono', monospace",
                      }}
                    >
                      {s.description}
                    </div>
                  </div>
                </div>
              );
            })}
          </div>

          {/* Performance Metrics Dashboard */}
          <div style={{ marginTop: 16, borderTop: `1px solid ${COLORS.border}`, paddingTop: 14 }}>
            <div style={{ ...headingStyle, fontSize: 12, marginBottom: 10 }}>Performance Metrics</div>
            {(() => {
              const steps = searchResult.steps;
              const tuneInPos = steps[0]?.pos ?? 0;
              const retrievePos = steps[steps.length - 1]?.pos ?? 0;
              const responseTime = retrievePos - tuneInPos;

              // Probe wait: slots from tune-in to next index segment start
              const probeStep = steps.find(s => s.action === "doze" && s.step === 2);
              const indexReadStep = steps.find(s => s.action === "read_index");
              const probeWait = probeStep ? (probeStep.pos - tuneInPos) : 0;

              // Index read time: slots spent reading index
              const indexReadTime = indexReadStep ? ((indexReadStep.endPos || indexReadStep.pos) - indexReadStep.pos + 1) : 0;

              // Bcast wait: slots from end of index read to data retrieval
              const indexEndPos = indexReadStep ? (indexReadStep.endPos || indexReadStep.pos) : tuneInPos;
              const bcastWait = retrievePos - indexEndPos - 1;

              // Tuning time: count only active slots
              let tuningTime = 0;
              for (const s of steps) {
                if (s.state === "active") {
                  if (s.endPos !== undefined) {
                    tuningTime += (s.endPos - s.pos + 1);
                  } else {
                    tuningTime += 1;
                  }
                }
              }

              // Doze time
              const dozeTime = responseTime - tuningTime;

              // Energy savings
              const energySavings = responseTime > 0 ? ((dozeTime / responseTime) * 100).toFixed(1) : 0;

              return (
                <div style={{ display: "grid", gridTemplateColumns: "repeat(auto-fit, minmax(150px, 1fr))", gap: 10 }}>
                  {[
                    { label: "Probe Wait", value: `${probeWait} slots`, color: COLORS.doze, note: "Time from tune-in to reaching next index segment. Client dozes during this period." },
                    { label: "Index Read Time", value: `${indexReadTime} slots`, color: COLORS.active, note: "Slots spent actively reading index nodes (root to leaf traversal)." },
                    { label: "Bcast Wait", value: `${Math.max(0, bcastWait)} slots`, color: COLORS.doze, note: "Time from finishing index read to data arrival. Client dozes during this period." },
                    { label: "Tuning Time", value: `${tuningTime} slots`, color: COLORS.active, note: "Total time radio is ON (active). This determines battery drain." },
                    { label: "Doze Time", value: `${Math.max(0, dozeTime)} slots`, color: COLORS.data, note: "Total time radio is OFF. Battery is conserved." },
                    { label: "Response Time (Latency)", value: `${responseTime} slots`, color: COLORS.accent, note: "Total elapsed time from tune-in to data retrieval. Response = Probe Wait + Index Read + Bcast Wait + 1." },
                    { label: "Energy Savings", value: `${energySavings}%`, color: COLORS.highlight, note: "Doze time as percentage of response time. Higher = more battery saved by indexing." },
                  ].map((stat, i) => (
                    <div key={i} style={{
                      background: COLORS.bg,
                      border: `1px solid ${COLORS.border}`,
                      borderRadius: 6,
                      padding: "10px 12px",
                    }}>
                      <div style={{ fontSize: 9, color: COLORS.textDim, fontFamily: "'JetBrains Mono', monospace", textTransform: "uppercase", letterSpacing: 0.5 }}>{stat.label}</div>
                      <div style={{ fontSize: 16, fontWeight: 700, color: stat.color, fontFamily: "'JetBrains Mono', monospace", marginTop: 2 }}>{stat.value}</div>
                      <div style={{ fontSize: 8, color: COLORS.textDim, fontFamily: "'JetBrains Mono', monospace", marginTop: 3 }}>{stat.note}</div>
                    </div>
                  ))}
                </div>
              );
            })()}
          </div>
        </div>
      )}
      <div style={{ textAlign: "center", padding: "12px 0", fontSize: 10, color: COLORS.textDim, fontFamily: "'JetBrains Mono', monospace" }}>
        Partial Replication Indexing in Air — Based on Imielinski, Viswanathan & Badrinath
      </div>
    </div>
  );
}
