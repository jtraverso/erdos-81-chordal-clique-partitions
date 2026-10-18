# Paper VI Preprint 1.0 formal sources

The default target PaperVIRelease imports all 79 local modules. The sources and two check files are released under Apache-2.0 with existing credits preserved. Install the pinned Lean toolchain. Preserve lake-manifest.json unchanged, then run:

```
lake exe cache get
lake build PaperVIRelease
lake env lean -j1 -s32768 EndpointGate.lean
lake env lean -j1 -s32768 FreezeFullAudit.lean
```

The recorded build used the compatible pinned Mathlib cache and local build cache. Changed source modules and affected imports were rebuilt by Lake. The separate type/axiom checks were rerun on that aggregate. Only licensing comments and package metadata changed; mathematical proof bodies and theorem types are unchanged. This archive excludes .lake, junctions and machine-specific dependency paths.
