# Artifact manifest

- Artifact name: `choicefree-bc-dct`
- Version: `0.3.0`
- Date: 2026-08-08
- DOI (software deposit, this version): `10.5281/zenodo.21850966`
- Lean version: `leanprover/lean4:v4.30.0`
- mathlib revision: `v4.30.0`

## Top-level files

- `README.md`
- `LICENSE`
- `CITATION.cff`
- `ARTIFACT_MANIFEST.md`
- `DEPENDENCY_CLOSURE.md`
- `lean-toolchain`
- `lakefile.toml`
- `lake-manifest.json`
- `build_audit.sh`
- `ChoiceFreeMeasureDCTPublic.lean`
- `SupplementChoiceFreeMeasureDCT.lean`
- `Mathdemo.lean`
- `Mathdemo/BishopSec3PresentedEnhancements.lean`
- `Mathdemo/BishopSec3PresentedEnhancementsC.lean`
- `Mathdemo/BishopChengTheorem415Prop.lean`
- `Mathdemo/BishopChengTheorem415FullSetData.lean`
- `Mathdemo/CheckDCTV2Axioms.lean`
- `Mathdemo/CheckBishopChengTheorem415PropAxioms.lean`
- `Mathdemo/ChoiceFreeDCTExamples.lean`
- `Mathdemo/ChoiceFreeDCTConcreteExamples.lean`
- `Mathdemo/MathematicalInterface.lean`
- `Mathdemo/SourceIntegrationSpaceDef11.lean`
- `Mathdemo/DiracIntegrationSpace.lean`
- `Mathdemo/`
- `tools/`
- `paper/` (development repository only; excluded from the archived deposit)
- `logs/`
- `audits/corn/`
- `SHA256SUMS`

## Audit commands

```bash
./build_audit.sh
sha256sum -c SHA256SUMS
cd audits/corn && sha256sum -c SHA256SUMS
```

`./build_audit.sh` runs the public theorem build, the public alias files, and the strengthened static no-choice audit. The script writes local rerun logs to `logs/build_audit.rerun.txt` and `logs/static_audit.rerun.txt`; shipped reference logs remain stable.

Release status: on 2026-08-05 a complete `./build_audit.sh` run finished with `BUILD_AUDIT_EXIT=0`: `lake build Mathdemo.CheckSec3PortAxioms` completed all 2856 build jobs (identical to the 2026-07-12 record), and the static source-closure audit passed with `closure_files: 512`, which includes the three modules added in this line (`MathematicalInterface`, `SourceIntegrationSpaceDef11`, `DiracIntegrationSpace`). The audit was rerun from the `v0.3.0` release tree on 2026-08-08; the shipped logs `logs/build_audit.txt` and `logs/static_audit.txt` record that run. The 512 Lean files tracked by the repository coincide exactly with the audited import closure of the public roots: the artifact contains no Lean file outside the dependency closure of its public theorems.

## Expected result summary

- The listed public theorem aliases, including the automatic aliases and the Prop-facing theorem, `#check` successfully.
- The listed implementation declarations `#check` successfully.
- The major audited Lean declarations report only `[propext, Quot.sound]` as axioms.
- The build log contains no `Classical.choice`, `Classical.choose`, `sorryAx`, `native_decide`, or `Quot.out` in the axiom output for the audited declarations.
- The strengthened static audit finds no executable occurrence of `sorry`, `admit`, `Classical.choice`, `Classical.choose`, `Classical.`, `native_decide`, `Quot.out`, `unsafe`, `open Classical`, `open scoped Classical`, or standalone `classical` in the public Lean source closure.
- The packaged CoRN audit reports `CvMeasure`, `DominatedMeasureCvZero`, and `DominatedConvergence` as `Closed under the global context` at CoRN commit `ada7c0b497ff15dd67cf7932c6f20e143a2aee2f` using Rocq 9.0.1.
- `SHA256SUMS` excludes local rerun logs so that rerunning the audit does not invalidate the shipped reference checksums.

## Development-line additions

Version `0.3.0` (release) adds three modules on top of the audited closure without reorganizing it: `Mathdemo/MathematicalInterface.lean`, a thin mathematical facade (36 declarations, mathematician-facing names, all auditing to `[propext, Quot.sound]`, with implementation counterparts matching 20/20 on axiom footprints) that Part I of the paper transcribes; `Mathdemo/SourceIntegrationSpaceDef11.lean`, a field-for-field transcription of Bishop--Cheng Definition 1.1 with an adapter to the development interface that isolates the difference in a single hypothesis (truncation at an arbitrary constant); and `Mathdemo/DiracIntegrationSpace.lean`, an unconditional normalized point-evaluation model. It also freezes the full-audit status above. The archived software deposit for this version excludes the `paper/` sources, which are maintained in the development repository.

Version `0.2.3-dev` documented the reproduced CoRN/Rocq assumption audit, clarifies that this project does not claim priority over Semeria's CoRN Bishop--Cheng DCT formalization, explains the three-layer Lean API, and qualifies the weaker-domination comparison with CoRN's public `DominatedConvergence` theorem. It also adds a Type-valued full-set route whose indexed carriers, fullness proofs, and domination bounds are explicit input data while the conclusion retains its convergence modulus.

The underlying `0.2.2` development line added a separated L1/integral public API, a good-set convergence wrapper, CReal-native countable-avoidance and Cauchy-completeness support, an internal dyadic smooth-level data constructor, automatic public DCT wrappers, a Prop-facing Bishop--Cheng theorem 4.15 surface from `ConvergeInMeasureC` and an existential full-set majorant, abstract public-API application examples, and a nonempty concrete zero-integral `PUnit` application example.

## Paper files

- `paper/paper.tex` is the editable paper source maintained in the development repository.
- `paper/paper.pdf` is generated from that TeX source.
- The `paper/` directory is excluded from the archived software deposit (`export-ignore`) and from `SHA256SUMS`: the deposit is the Lean code and its audit apparatus; the paper is referenced separately.

## CoRN audit package

`audits/corn/` contains a minimal reproducibility package for the independently reproduced Rocq `Print Assumptions` audit. It does not include a CoRN clone, build products, Docker layers, OPAM caches, or development-history archives.

## Development archive

Historical auxiliary files, failed routes, previous attempts, and other development-history files are not included in the public artifact zip. A separate development archive, if present, is a sibling of this public artifact and is not part of the public zip.

## Note on Lean warnings

The reference Lean build may contain style/linter warnings from the imported historical closure. It contains no Lean errors in the audited run; the audited declarations build and have the stated dependency profile.
