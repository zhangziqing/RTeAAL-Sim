# Experimental slice projection snapshot

This branch preserves the workspace's existing slice-projection and ordered
masked-update work on top of `nanhu-simulation`. It is a research snapshot with
unresolved test failures, separate from the branch that passed its checks.

## Changes

- `SliceGraph.scala` defines explicitly sized expressions and bounded proofs
  for reusing host values without dropping required normalization.
- `ProjectSlices.scala` analyzes demanded bit ranges; `SliceRewrite.scala`
  owns graph updates, depth accounting and growth budgets.
- `ComposeMaskedUpdates.scala` composes proven independent updates while
  retaining their overwrite order and state dependencies.
- `--project-slices` and `--compose-masked-updates` are both off by default.

## Publication verification

All 51 production Scala sources and 19 test sources compiled with cached
Scala 2.13.12 dependencies. ScalaTest ran 99 tests: 97 passed and two failed
in `ProjectSlicesTest`:

1. `project crossing binary and variadic fields including repeated operands`
   expected a rewrite, but the pass reported zero applied rewrites.
2. `include the final assignment in whole-reference depth and growth decisions`
   expected a direct reference, but the plan emitted an explicit AND with 255.

These failures are preserved for investigation. Their causes have not been
resolved by changing the tests or implementation for publication. Passing
compiler tests and the historical Nanhu prefix comparisons do not override
the failures in this snapshot.

`PLRUProjectionTest` requires the separately generated, pinned Nanhu preclock
FIRRTL at `../results/nanhu/SimTop.preclock.lo.fir` or
`results/nanhu/SimTop.preclock.lo.fir`. It cancels its actual-cone check when
that artifact is unavailable. The publication run supplied the existing
artifact; no tests were canceled.

The normal `sbt test` launcher could not start in the publication sandbox
because its boot-socket directory was read-only. The reported run used the
Scala compiler and ScalaTest runner directly with the cached sbt dependency
classpath; dependency resolution and assembly were not run.
