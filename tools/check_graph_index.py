#!/usr/bin/env python3
"""Compare indexed graph extraction with the retained scan path or a baseline build.

Run `sbt "Test / compile"` first. A supplied reference classpath must include
these test fixtures and the reference compiler before the candidate compiler.
All outputs are isolated under target/; historical experiment files are untouched.
"""
import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference-classpath")
    parser.add_argument("--classpath", help="Candidate test and compiler classpath")
    parser.add_argument("--java", default="java")
    args = parser.parse_args()
    dependencies = ROOT / "target/streams/test/dependencyClasspath/_global/streams/export"
    candidate = args.classpath or ":".join((str(ROOT / "target/scala-2.13/test-classes"),
        str(ROOT / "target/scala-2.13/classes"), dependencies.read_text().strip()))
    reference = args.reference_classpath or candidate
    output = Path(tempfile.mkdtemp(prefix="graph-index-", dir=ROOT / "target"))
    preserved = output / "preserved.txt"
    preserved.write_text("")
    for fixture in ("CheckNanhuChainIndex", "CheckNanhuLayerIndex", "CheckNanhuOrderIndex"):
        results = []
        exports = []
        for label, classpath in (("reference", reference), ("indexed", candidate)):
            export = output / f"{fixture}-{label}"
            export.mkdir()
            indexed = label == "indexed" or bool(args.reference_classpath)
            command = [args.java, "-XX:ActiveProcessorCount=4", "-Xmx4g",
                f"-Drteaal.nanhu={str(indexed).lower()}", f"-Drteaal.preserved={preserved}",
                f"-Drteaal.exportCheckDir={export}", "-cp", classpath, fixture]
            result = subprocess.run(command, cwd=ROOT, capture_output=True, check=True)
            (output / f"{fixture}-{label}.log").write_bytes(result.stdout + result.stderr)
            results.append(b"\n".join(line for line in result.stdout.splitlines()
                                      if not line.startswith(b"[Nanhu]")))
            exports.append({p.name: p.read_bytes() for p in export.iterdir()})
        assert results[0] == results[1], f"Graph output differs: {fixture} ({output})"
        assert exports[0] == exports[1], f"Tensor exports differ: {fixture} ({output})"
        if fixture == "CheckNanhuOrderIndex":
            assert len(exports[0]) == 18, "Expected three exports for each of six graphs"
        print(f"PASS {fixture}: graph output and exports match")
    print(f"120 chain graphs, 80 layer graphs, 9600 shift lookups, 6 tensor graphs; logs: {output}")


if __name__ == "__main__":
    main()
