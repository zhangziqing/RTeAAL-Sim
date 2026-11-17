# Nanhu simulation fork

This branch preserves the history of
[TAC-UCB/RTeAAL-Sim](https://github.com/TAC-UCB/RTeAAL-Sim), starting from
upstream commit `a41492ee3177a15a01f3583fd7e08010b2ab3886`.
The original paper, authorship, and citation remain in the root README.

## Scope

The Nanhu input is XiangShan single-core DefaultConfig at commit
`0a68ebc13b3d96a78d8663679393ecbea5b8fb73`. The processor source and its pinned
dependencies are unchanged. Adaptations belong to the FIRRTL compiler and
simulation environment:

- `src/main/scala/passes/NanhuSimulation.scala` models the fixed harness's
  RAM, flash and idle JTAG, and handles its clock enables. RAM is bounded to
  256 MiB; the host runner must reject out-of-range accesses and SD requests.
- Compiler extraction and lowering retain observable signals, support wide
  values, and provide compiler checkpoints and scalable graph indexing.
  Chain membership, missing reverse edges during layering, shift groups and
  tensor input membership use indices in Nanhu mode. Text/YAML export writes
  layers incrementally. These changes are part of the regular compiler source;
  the historical `chain-index.jar` overlay is no longer needed.
- Graph optimizations include associative and binary-concat balancing,
  ordered priority mux balancing, constant mux reduction, decoder/Mux1H
  folding and optional dense mux-index normalization.
- `FactorMuxBitwise.scala` exposes shared AND/OR/XOR operands before mux
  optimization. Shared mux outputs remain eligible lookup roots when they
  also feed a mux data input.
- Optional slice projection shortens demanded bit ranges with explicit host
  normalization. Ordered masked-update composition combines proven independent
  register fields while preserving overwrite order and state dependencies.

The Nanhu harness is opt-in with the JVM property `-Drteaal.nanhu=true`.
Dense mux normalization additionally requires `--normalize-mux-index`.
Graph AND/OR balancing additionally requires `-Drteaal.balanceAndOr=true`.
The default tensor concat representation remains binary; the historical
variadic-concat implementation was reverted in this branch's history.

## Build and checks

The build pins sbt 1.9.6, Scala 2.13.12 and FIRRTL 1.5.6. Use **JDK 11**
to build all targets, including the separate Scala 2.12.13 / FIRRTL 1.5.1
override required by the pinned Nanhu elaborator. The Scala 2.13 simulator
also builds on the verified JDK 21 toolchain. From this repository:

```bash
sbt test assembly "fastAccesses212 / checkFastAccesses" "fastAccesses213 / checkFastAccesses"
python3 tools/check_graph_index.py
sbt -Drteaal.nanhu=true -Drteaal.preserved=utils/bin/preserved_signals.txt \
    "Test / runMain CheckMuxBitwise" "Test / runMain CheckSharedMuxRoot"
```

The assembly target is `utils/bin/essent.jar`. The fast-accesses build targets
produce `utils/bin/firrtl-fast-accesses-{2.12,2.13}.jar` from the maintained
[source](../tools/firrtl-fast-accesses/README.md), using pinned Maven
dependencies. They do not require an old assembly or a Nanhu Mill output.
Put the matching override first on the JVM classpath for High FIRRTL lowering
or Nanhu elaboration. Preclock and optimized-graph replay bypass
`RemoveAccesses`; the runtime and CUDA kernel build do not use these JARs.
Generated FIRRTL, tensors, compiled binaries and caches are excluded from Git.

The graph check runs the scan and indexed implementations in separate JVMs
and compares 120 mixed-operation graphs, 80 layering controls, 9,600 shift
lookups, and six tensor graphs including 18 byte-identical exports. It also
accepts `--reference-classpath` for an independently compiled baseline.
The source integration was checked against both the retained scan path and
compiler revision `61346d343ea8410c91814e6c07845a27cc296a21`.
The fast-accesses checks compare stock, optimized and cached lowering of a
nested dynamic read/write fixture and verify the loaded class origins.

Use `-Drteaal.postGraphDump=/absolute/path/graph.bin` in Nanhu mode to save
the graph after all enabled optimizations and before tensor allocation.
From `utils/bin`, replay with the same source revision and observation list:

```bash
java -Drteaal.nanhu=true -Drteaal.preserved=/absolute/path/preserved.txt \
     -cp essent.jar essent.NanhuGraphCheckpoint /absolute/path/graph.bin
```

`rteaal.design`, when supplied, must match the checkpoint's design name.
The checkpoint carries graph, state, lookup, memory-dependency and export
metadata. It is a compiler-specific build artifact. Four workspace controls
(Bool SRAM, RAMHelper, FlashHelper and idle JTAG) compared fresh compilation
and checkpoint replay against their Verilator traces through cycle 999;
comparison starts after each control's documented initial-state boundary.
No checkpoint or previous experiment artifact is required for the source build.

Slice projection requires `--project-slices`; ordered masked-update composition
requires `--compose-masked-updates`. Both are off by default. Their contracts,
fixture corrections and verification are documented in
[SLICE_PROJECTION.md](SLICE_PROJECTION.md). The earlier integration's cached
ScalaTest results are preserved there; the graph/checkpoint/source-build
follow-up passed all 102 ScalaTest tests with no cancellations on JDK 11,
built the simulator assembly and both override JARs, and passed the graph and
FIRRTL differential checks. The independent mux smoke programs cover
54 bitwise comparisons at widths 1, 8 and 65, plus shared lookup consumers
and dependencies. Full Nanhu execution and performance were not rerun for
this integration; there is no newly measured end-to-end compilation speedup.

## Verification boundary

Compiler and small semantic checks do not establish full-design equivalence.
The experiment's CoreMark 100K prefix does not establish a completed CoreMark
run, final CRC or score. General multiple-clock RTL remains outside the
supported contract; a successful clock diagnostic may intentionally reproduce
a known incompatibility. Complete Nanhu runs additionally require the pinned
RTL, workload, host adapters and observation configuration supplied by the
workspace reproduction flow.
