# Artifact manifest

- Artifact name: `choicefree-bc-dct`
- Version: `0.5.1`
- Date: 2026-08-31
- DOI (software deposit, this version): reserved at deposit time; not yet assigned in this tree
- DOI (previous version v0.4.1): `10.5281/zenodo.22137161`
- DOI (previous version v0.4.0): `10.5281/zenodo.21854936`
- DOI (all versions): `10.5281/zenodo.21850965`
- Published: v0.4.1 on 2026-08-28 (Zenodo, https://zenodo.org/record/22137161); v0.4.2 not yet deposited
- Git tag: `v0.5.1`
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
lake build Mathdemo   # second audit route; recorded in logs/mathdemo_build.txt
sha256sum -c SHA256SUMS
cd audits/corn && sha256sum -c SHA256SUMS
```

`./build_audit.sh` runs the public theorem build, the public alias files, and the strengthened static no-choice audit. The script writes local rerun logs to `logs/build_audit.rerun.txt` and `logs/static_audit.rerun.txt`; shipped reference logs remain stable.

Release status: on 2026-08-31 a complete `./build_audit.sh` run from the v0.5.1 tree finished with `BUILD_AUDIT_EXIT=0` (build stages of 2856, 2857, 2858, 3 and 2869 jobs in the shipped log; the 2869-job aggregate build `lake build Mathdemo` is part of the script as of this version), and the static source-closure audit passed with `closure_files: 512` — the same closure set as v0.3.0 and v0.4.0. The shipped logs `logs/build_audit.txt` and `logs/static_audit.txt` record that run (`artifact_version=0.5.1`).  Two further evidence logs are shipped: `logs/mathdemo_build.txt`, the aggregate build, and `logs/reading_layer_axioms.txt`, the kernel axiom output of all 73 reading-layer declarations (72 report `[propext, Quot.sound]`, one reports no axioms). The 512 Lean files tracked by the repository coincide exactly with the union of the transitive import closures of the six audit roots, so the artifact contains no tracked Lean file outside what the audit traverses; the closure of the public theorem aliases alone is 502 of them.

## Expected result summary

- The listed public theorem aliases, including the automatic aliases and the Prop-facing theorem, `#check` successfully.
- The listed implementation declarations `#check` successfully.
- The major audited Lean declarations report only `[propext, Quot.sound]` as axioms.
- The build log contains no `Classical.choice`, `Classical.choose`, `sorryAx`, `native_decide`, or `Quot.out` in the axiom output for the audited declarations.
- The strengthened static audit finds no executable occurrence of `sorry`, `admit`, `Classical.choice`, `Classical.choose`, `Classical.`, `native_decide`, `Quot.out`, `unsafe`, `open Classical`, `open scoped Classical`, or standalone `classical` in the public Lean source closure.
- The packaged CoRN audit reports `CvMeasure`, `DominatedMeasureCvZero`, and `DominatedConvergence` as `Closed under the global context` at CoRN commit `ada7c0b497ff15dd67cf7932c6f20e143a2aee2f` using Rocq 9.0.1.
- `SHA256SUMS` excludes local rerun logs so that rerunning the audit does not invalidate the shipped reference checksums.

## Development-line additions

Version `0.4.0` (release) repairs the integration-space interface. The arbitrary-constant truncation clause `cutConst_mem` is replaced by a positivity-witnessed clause `cutPos_mem`; the zero cut is derived as a lemma from linearity, absolute value, and equality-respect; a witness type `CutConstWitnessC` (positive/zero) threads the data through the development, and every use site carries a canonical witness. As a consequence all fourteen fields of the working interface became derivable, without extra hypotheses, from the clause-by-clause encoded transcription of Bishop--Cheng Definition 1.1.  Version `0.4.1` machine-checks the remaining gauge passage: the transcription now states clause (4) at the source's own gauge `1/(n+1)`, and `cutSmall_tendsto_of_src` derives the dyadic-gauge field used by the working interface.  The reverse comparison `srcGauge_le_halfPow` is used by the point-evaluation model. The full audit was rerun from the repaired tree (see Release status).  Version `0.4.2` removes five declarations whose conclusion or body was `True` — `ContinuousOn`, `lemma33_lt_of_not_le`, `lemma34_out_exists_cell`, `fatou_type_stub_not_source_4_14` and `thm_4_15_dominated_convergence`, all vestiges of the earlier neutralization of unused generic branches, none referenced anywhere in the closure — and adds a public alias for Theorem 3.5, `profile_smooth_away_from_sequenceC`.  The file set is unchanged at 512; the tree is 177,990 lines and 8,953 declarations.  Version `0.5.0` replaces the encoding of the ambient function class by the memoir's own: `BFunC` is a domain together with a map defined only on that domain, and the integral of `IntSpaceC` and of the Definition 1.1 transcription is defined only on `L`.  The adapter `toIntSpaceC` still derives all fourteen fields with no hypotheses, and now needs no total extension, so an integration space in the memoir's sense instantiates the interface directly.  The file set is unchanged at 512; the tree is 182,344 lines and 9,073 declarations, the growth being the membership witnesses carried at each point of use.  Version `0.5.1` guards the tail conditions of `ProfileC.IsSmoothAtC` by `a <= x <= b`, as the memoir's `F` within `C[a,b]` has them, and exports Theorem 3.6 in the memoir's global form: `profile_level_sets_integrable_apart_globalC` produces one exceptional sequence for all positive `t`, obtained by covering the positive half-line with `((n+2)^{-1}, n+2)` and flattening the per-interval sequences.  The interval-local alias is kept.  The tree is 182,630 lines and 9,091 declarations.

Version `0.3.0` (release) added three modules on top of the audited closure without reorganizing it: `Mathdemo/MathematicalInterface.lean`, a thin mathematical facade (36 declarations, mathematician-facing names, all auditing to `[propext, Quot.sound]`, with implementation counterparts matching 20/20 on axiom footprints) that Part I of the paper transcribes; `Mathdemo/SourceIntegrationSpaceDef11.lean`, a clause-by-clause transcription of the displayed Bishop--Cheng Definition 1.1 with an adapter to the development interface that isolates the difference in a single hypothesis (truncation at an arbitrary constant); and `Mathdemo/DiracIntegrationSpace.lean`, an unconditional normalized point-evaluation model. It also freezes the full-audit status above. The archived software deposit for this version excludes the `paper/` sources, which are maintained in the development repository.

Version `0.2.3-dev` documented the reproduced CoRN/Rocq assumption audit, clarifies that this project does not claim priority over Semeria's CoRN Bishop--Cheng DCT formalization, explains the three-layer Lean API, and qualifies the weaker-domination comparison with CoRN's public `DominatedConvergence` theorem. It also adds a Type-valued full-set route whose indexed carriers, fullness proofs, and domination bounds are explicit input data while the conclusion retains its convergence modulus.

The underlying `0.2.2` development line added a separated L1/integral public API, a good-set convergence wrapper, CReal-native countable-avoidance and Cauchy-completeness support, an internal dyadic smooth-level data constructor, automatic public DCT wrappers, a Prop-facing Bishop--Cheng theorem 4.15 surface from `ConvergeInMeasureC` and an existential full-set majorant, abstract public-API application examples, and a nonempty concrete zero-integral `PUnit` application example.

## Paper files

- `paper/paper.tex` is the editable paper source maintained in the development repository.
- `paper/paper.pdf` is generated from that TeX source.
- The `paper/` directory is excluded from the archived software deposit (`export-ignore`) and from `SHA256SUMS`: the deposit is the Lean code and its audit apparatus; the paper is referenced separately.

## CoRN audit package

`audits/corn/` contains a minimal reproducibility package for the Rocq `Print Assumptions` audit reproduced by the present author from the pinned CoRN snapshot. It does not include a CoRN clone, build products, Docker layers, OPAM caches, or development-history archives.

## Development archive

Historical auxiliary files, failed routes, previous attempts, and other development-history files are not included in the public artifact zip. A separate development archive, if present, is a sibling of this public artifact and is not part of the public zip.

## Note on Lean warnings

The reference Lean build may contain style/linter warnings from the imported historical closure. It contains no Lean errors in the audited run; the audited declarations build and have the stated dependency profile.
