# Slice projection and ordered masked updates

The workspace's slice-projection and ordered masked-update passes are included
in `nanhu-simulation` after regression verification. Their original publication
snapshot is retained in the history of `experimental/slice-projection`.

## Changes

- `SliceGraph.scala` defines explicitly sized expressions and bounded proofs
  for reusing host values without dropping required normalization.
- `ProjectSlices.scala` analyzes demanded bit ranges; `SliceRewrite.scala`
  owns graph updates, depth accounting and growth budgets.
- `ComposeMaskedUpdates.scala` composes proven independent updates while
  retaining their overwrite order and state dependencies.
- `--project-slices` and `--compose-masked-updates` are both off by default.

## Publication verification

The initial published snapshot compiled all sources and ran 99 ScalaTest tests:
97 passed and two fixtures in `ProjectSlicesTest` failed. The November 17, 2026
follow-up identified stale assumptions from before the host-normalization
repair:

1. The variadic crossing-slice fixture used narrow input metadata as its only
   normalization evidence. Retaining the required host mask made the rewrite
   add one operator at the same depth (2 to 2), so rejection was correct.
   The positive crossing-field fixture now has explicitly masked producers.
   A separate regression preserves the original graph and checks the rejected
   rewrite, unchanged graph and independent output values.
2. The whole-reference fixture expected an assignment while its producer only
   assigned an unproven narrow input. Emitting an AND with 255 was required.
   The fixture now uses an explicitly masked producer to exercise the intended
   assignment-depth accounting. A new regression checks unproven assignment
   chains at widths 1, 6, 7, 8, 31, 32, 63 and 64, including nonzero upper host
   bits, before and after rewriting against independent masked values.

The existing normalization proof and profitability rules are retained. All 51
production sources and 19 test sources recompiled with cached Scala 2.13.12
dependencies. All 101 ScalaTest tests passed, including both real Nanhu PLRU
checks; no tests were canceled. The 54 independent bitwise mux comparisons and
the shared-root smoke also passed. Full Nanhu execution and performance
experiments were not rerun for this integration.

`PLRUProjectionTest` requires the separately generated, pinned Nanhu preclock
FIRRTL at `../results/nanhu/SimTop.preclock.lo.fir` or
`results/nanhu/SimTop.preclock.lo.fir`. It cancels its actual-cone check when
that artifact is unavailable. The publication run supplied the existing
artifact; no tests were canceled.

The normal `sbt test` launcher could not start during the initial publication
because its boot-socket directory was read-only. The follow-up also used the
Scala compiler and ScalaTest runner directly with the cached sbt dependency
classpath; dependency resolution, `sbt test` and assembly were not rerun.
