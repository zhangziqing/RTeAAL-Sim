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
- Graph optimizations include associative and binary-concat balancing,
  ordered priority mux balancing, constant mux reduction, decoder/Mux1H
  folding and optional dense mux-index normalization.
- `FactorMuxBitwise.scala` exposes shared AND/OR/XOR operands before mux
  optimization. Shared mux outputs remain eligible lookup roots when they
  also feed a mux data input.

The Nanhu harness is opt-in with the JVM property `-Drteaal.nanhu=true`.
Dense mux normalization additionally requires `--normalize-mux-index`.
Graph AND/OR balancing additionally requires `-Drteaal.balanceAndOr=true`.
The default tensor concat representation remains binary; the historical
variadic-concat implementation was reverted in this branch's history.

## Build and checks

The build pins sbt 1.9.6, Scala 2.13.12 and FIRRTL 1.5.6. Publication checks
used Java 21 and the existing cached dependencies. From this repository:

```bash
sbt test
sbt "Test / runMain CheckMuxBitwise"
sbt -Drteaal.nanhu=true "Test / runMain CheckSharedMuxRoot"
sbt assembly
```

The assembly target is `utils/bin/essent.jar`. Generated FIRRTL, tensors,
compiled binaries and dependency caches are not part of the source release.
The independent smoke programs above are preserved from the workspace's
existing checks. They cover bitwise mux semantics at widths 1, 8 and 65, and
shared lookup consumers and dependencies.

The `experimental/slice-projection` branch separately preserves the workspace's
slice projection and ordered masked-update composition work. Its publication
snapshot has two failing projection tests; those changes are not enabled by
this branch.

## Verification boundary

Compiler and small semantic checks do not establish full-design equivalence.
The experiment's CoreMark 100K prefix does not establish a completed CoreMark
run, final CRC or score. General multiple-clock RTL remains outside the
supported contract; a successful clock diagnostic may intentionally reproduce
a known incompatibility. Complete Nanhu runs additionally require the pinned
RTL, workload, host adapters and observation configuration supplied by the
workspace reproduction flow.
