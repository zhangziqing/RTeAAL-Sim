# FIRRTL fast-accesses override

This source is derived from `firrtl/passes/RemoveAccesses.scala` in the Maven
source artifacts `edu.berkeley.cs:firrtl_2.12:1.5.1` and
`edu.berkeley.cs:firrtl_2.13:1.5.6`. The original sources are identical.
The Apache-2.0 license and attribution are included under `resources/META-INF`
and packaged with each override.

The modifications expand the selected static subtree directly and bypass an
expression cache whose keys recursively hash ancestor aggregate types.
`-Dfirrtl.fastAccesses.useCache=true` retains the cache for comparison.

## Source build

Run sbt on **JDK 11** for the pinned Scala 2.12.13 compiler. Its compiler bridge
fails on Java 21. The Scala 2.13.12 simulator also supports the verified JDK 21
build; using JDK 11 allows all targets to be built in one invocation.
No previously built simulator JAR or Nanhu Mill classpath is required.
From the repository root:

```bash
sbt "fastAccesses212 / packageBin" "fastAccesses213 / packageBin" assembly
sbt "fastAccesses212 / checkFastAccesses" "fastAccesses213 / checkFastAccesses"
```

Outputs are `utils/bin/firrtl-fast-accesses-2.12.jar`,
`utils/bin/firrtl-fast-accesses-2.13.jar`, and `utils/bin/essent.jar`.
They are build artifacts excluded from Git.

Use the 2.12 override with the pinned Nanhu elaboration classpath and the 2.13
override with the simulator's FIRRTL 1.5.6 classpath. Put the override **first**
on the JVM classpath. The simulator assembly contains stock FIRRTL;
`assembly` does not embed this separate override. Preclock and optimized-graph
checkpoint replay bypass `RemoveAccesses` and do not require this JAR.

## Differential check

Each check builds its override from source, lowers `test/NestedAccess.fir`
with stock FIRRTL, the optimized pass, and the optimized pass with caching.
It checks the actual loaded class origin and compares all Low FIRRTL bytes.
The fixture covers nested bundles/vectors, static selections, dynamic reads
and writes, and indices wider than their vector bounds. Logs and generated
FIRRTL are isolated in the corresponding subproject's ignored `target/`.
This is a compiler-output comparison; it does not prove whole-Nanhu equivalence
or measure compilation speedup.
