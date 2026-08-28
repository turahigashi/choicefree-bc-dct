# choicefree-bc-dct

Version: 0.4.1

DOI (this version): [10.5281/zenodo.22137161](https://doi.org/10.5281/zenodo.22137161)  ·  previous version v0.4.0: [10.5281/zenodo.21854936](https://doi.org/10.5281/zenodo.21854936)

DOI (all versions, resolves to latest): [10.5281/zenodo.21850965](https://doi.org/10.5281/zenodo.21850965)

This is a clean public import-closure Lean artifact for the paper:

**A choice-free Lean formalization of a profile-based dominated convergence theorem in presented Bishop--Cheng measure theory**

The artifact exposes public theorem aliases in `ChoiceFreeMeasureDCTPublic.lean` and audits the implementation declarations used by the paper. It is intentionally an import-closure artifact rather than a minimal hand-extracted micro-library: some historically named internal files remain because stable declarations in the public theorem closure still depend on them. The 512 Lean files tracked here coincide exactly with the audited import closure of the public roots, so the artifact contains no Lean file outside the dependency closure of its public theorems.

For a mathematician-facing entry point, start with `Mathdemo/MathematicalInterface.lean`: a thin facade (36 declarations, all auditing to `[propext, Quot.sound]`; kernel evidence for all 73 reading-layer declarations is shipped in `logs/reading_layer_axioms.txt`) whose names and statements are the ones transcribed in Part I of the paper. `Mathdemo/SourceIntegrationSpaceDef11.lean` contains a clause-by-clause transcription of the displayed Bishop--Cheng Definition 1.1 (ambient notions in the development's encoding) together with a hypothesis-free adapter deriving all fourteen fields of the development interface from it, including the machine-checked passage from the source's gauge `n⁻¹` to the development's dyadic gauge `2⁻ⁿ` (v0.4.1), and `Mathdemo/DiracIntegrationSpace.lean` provides an unconditional normalized point-evaluation model.

That facade is a *reading* layer: it states the results in the form a mathematician reads them, which for the dominated convergence theorem is the `Prop`-facing one. It is not the whole of what is formalized. The original route is the Type-valued, data-carrying one — Layer A of [Three-layer DCT interface](#three-layer-dct-interface) below.  The Type-valued route and the `Prop`-facing route share the profile and measure-theoretic infrastructure, but their endpoints are assembled separately.  The `Prop`-facing theorem is not obtained by applying the Layer A full-set theorem, because its `Prop`-valued convergence and domination hypotheses do not expose the indexed Type-valued selectors that Layer A requires.  Conversely, the `Prop`-valued conclusion does not by itself supply Layer A's data-valued convergence output.  A direct wrapper extracting those hidden witnesses would require an additional choice principle; the artifact does not claim a general logical non-derivability theorem between the two complete statements.

## Related Coq/CoRN formalization

Vincent Séméria previously formalized a substantial portion of Bishop--Cheng
constructive measure theory in
[Coq/CoRN](https://github.com/rocq-community/corn/tree/ada7c0b497ff15dd67cf7932c6f20e143a2aee2f).
At the audited commit, CoRN contains `CvMeasure`, `DominatedMeasureCvZero`, and
`DominatedConvergence` in
[`reals/stdlib/CMTMeasurableFunctions.v`](https://github.com/rocq-community/corn/blob/ada7c0b497ff15dd67cf7932c6f20e143a2aee2f/reals/stdlib/CMTMeasurableFunctions.v).

Séméria's paper
[“Nombres réels dans Coq”](https://inria.hal.science/hal-02427360)
is cited for the constructive-real infrastructure underlying the development,
not as the source publication of the dominated-convergence formalization.

Accordingly, this project does not claim the first proof-assistant
formalization, the first constructive formalization, or the first choice-free
formalization of Bishop--Cheng dominated convergence.

The reproduced Rocq audit packaged in `audits/corn/` checks CoRN commit `ada7c0b497ff15dd67cf7932c6f20e143a2aee2f` with Rocq 9.0.1. For `CvMeasure`, `DominatedMeasureCvZero`, and `DominatedConvergence`, Rocq reported:

```text
Closed under the global context
```

In other words, `Print Assumptions` listed no global axioms in the dependency closure of these declarations. This is a statement about their global axiom footprint, not an assertion that the theorems are free of mathematical hypotheses: their statements remain parameterized by the explicitly quantified `IntegrationSpace` and `ConstructiveReals` structures, whose fields specify the mathematical setting in which the results are proved.

The Lean public declarations have a separate audit profile: the named public aliases and implementation declarations are checked with Lean `#print axioms`, and the intended declaration-level output is `[propext, Quot.sound]`. Both the CoRN result and the Lean result must be interpreted relative to their explicit structures and interfaces.

## What is proved

The public aliases summarize the formalized development. Throughout this list, the suffix `C` marks a declaration of the **Type-valued, data-carrying** route (Layers A and B of the three-layer interface below); it does not indicate a `Prop`-valued statement. Names containing `prop` are the `Prop`-facing facade of Layer C.  Layer C is proved on its own `Prop`-level route and does not apply the Layer A theorem; see [Layer C](#layer-c-prop-facing-theorem) below.

- `ChoiceFreeMeasureDCT.profile_partition_dataC`
- `ChoiceFreeMeasureDCT.profile_level_sets_integrable_apartC`
- `ChoiceFreeMeasureDCT.uniform_complement_from_profile_levelsC`
- `ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_measure_convergenceC`
- `ChoiceFreeMeasureDCT.integral_convergence_from_majorant_measure_convergenceC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_error_majorant_profileC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_profileC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_good_set_profileC`
- `ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_measure_convergence_autoC`
- `ChoiceFreeMeasureDCT.integral_convergence_from_majorant_measure_convergence_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_error_majorant_profile_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_profile_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_good_set_profile_autoC`
- `ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_on_full_dataC`
- `ChoiceFreeMeasureDCT.integral_convergence_from_majorant_on_full_dataC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_dataC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_data_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_good_set_data_autoC`
- `ChoiceFreeMeasureDCT.bishop_cheng_dominated_convergence_propC`

The corresponding implementation declarations audited in this artifact are:

- `BishopSec3P.lemma_3_4DataC`
- `BishopSec3P.thm_3_6_forall_apart_measureC`
- `BishopSec3P.lemma43UniformComplementData_of_majorantC`
- `BishopSec3P.thm_4_15_integral_convergence_from_majorant_smooth_measure_convergeC`
- `BishopSec3P.goalB_dominated_convergence_dataC`
- `BishopSec3P.goalB_classical_dominated_convergence_dataC`
- `BishopSec1P.DominatedOnFullDataC`
- `BishopSec3P.lemma43UniformComplementData_of_majorantOnFullDataC`
- `BishopSec3P.absError_le_absMajorant_add_absLimit_onFullDataC`
- `BishopSec3P.dominatedConvergence_from_pointwiseMajorantOnFullData_autoC`
- `BishopSec3P.bishop_cheng_l1_error_tends_zero_propC_with_majorant`
- `BishopSec3P.bishop_cheng_thm_4_15_propC`
- `BishopSec3P.thm36B1_apartPointDataC`
- `BishopSec3P.thm36B_smoothPointDataC_construct`
- `BishopSec3P.lemma43DyadicSmoothDataC_construct`

Mathematically, the artifact formalizes a presented-real, profile-based Bishop--Cheng dominated-convergence route. Profile partitions and apart level-set integrability supply the uniform complement estimate needed to turn convergence in measure plus an integrable majorant profile into convergence of integrals.

## Three-layer DCT interface

The public Lean API is organized into three layers.

### Layer A: Type-valued data-carrying kernel

The original Lean route exposes explicit proof-relevant data. The public declarations in this layer include:

- `ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_measure_convergenceC`
- `ChoiceFreeMeasureDCT.integral_convergence_from_majorant_measure_convergenceC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_error_majorant_profileC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_profileC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_good_set_profileC`
- `ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_on_full_dataC`
- `ChoiceFreeMeasureDCT.integral_convergence_from_majorant_on_full_dataC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_dataC`

These declarations consume explicit data such as convergence moduli, good-set data, integrability witnesses, point-evaluation witnesses, profile/majorant data, smooth-level data, and Type-valued convergence output. In the full-set route, `BishopSec1P.DominatedOnFullDataC fn g` supplies, for every index `n`, an explicit carrier, a proof that the carrier is full, and the domination proof on that carrier. The carrier may depend on `n`. This artifact does not claim that a Type-valued DCT interface is itself novel; CoRN already has a Type-valued `CvMeasure` interface.

### Layer B: Automatic Type-valued wrappers

The declarations ending in `_autoC` internally construct the dyadic smooth-level data via `BishopSec3P.lemma43DyadicSmoothDataC_construct`, rather than requiring an external `Lemma43DyadicSmoothDataC` argument. These include:

- `ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_measure_convergence_autoC`
- `ChoiceFreeMeasureDCT.integral_convergence_from_majorant_measure_convergence_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_error_majorant_profile_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_profile_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_good_set_profile_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_data_autoC`
- `ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_good_set_data_autoC`

### Layer C: Prop-facing theorem

`ChoiceFreeMeasureDCT.bishop_cheng_dominated_convergence_propC` accepts Prop-valued `ConvergeInMeasureC` and an existential integrable majorant satisfying `DominatedOnFullC`. Its conclusion is Prop-valued epsilon convergence of the integral sequence.

The proof opens existential witnesses from the convergence and domination hypotheses only within Prop proof goals. It does not assemble those witnesses into a global Type-valued selector. Callers who already have such a selector can instead use `DominatedOnFullDataC` and retain the Type-valued convergence modulus.

This layer is choice-free because its hypotheses **and** its conclusion both live in `Prop`: existential witnesses can be opened inside the final `Prop` proof without constructing a global Type-valued selector. Layer A remains a separate data-carrying route. A direct conversion from these `Prop`-valued hypotheses to Layer A's indexed selector would require an additional choice principle; no such conversion is used here.

## Domination assumptions compared with CoRN

CoRN's public `DominatedConvergence` assumes global pointwise domination:

```text
forall n, partialFuncLe (Xabs (fn n)) g
```

The Lean artifact now exposes this same mathematical weakening in two forms. The Prop-facing theorem assumes that for each `n`, domination holds on a full set, which may depend on `n`, and returns Prop-valued convergence. The Type-valued full-set theorem takes the carriers and their fullness and domination proofs as the explicit selector `DominatedOnFullDataC fn g`, and returns convergence data including a modulus. Within Lean, `DominatedOnFullDataC.ofGlobal` packages any global pointwise domination family as full-set data; no converse is asserted.

Relative to the domination clause alone, full-set domination is weaker than global pointwise domination. We nevertheless do not claim a formal strict generalization of the CoRN theorem, because the ambient real-number and integration-space interfaces differ. CoRN's `CR_cv` and the new Lean Type-valued full-set conclusion are both data-valued, but their complete theorem statements are not ordered solely by logical strength.

In the pointwise-majorant wrappers, the verified error majorant is `g + |f|` or `|g| + |f|` in the Prop-facing route. The artifact does not claim a `2g` majorant unless a separate proof of `|f| <= g` is supplied.

## Development-line additions

This development line separates the public L1 error-convergence endpoint from the final integral-convergence endpoint. It adds the explicit full-set Type route described above and a good-set convergence wrapper: the convergence data carries the good set, its integrability, membership in the ambient set, Type-valued point-evaluation witnesses, small complement measure, and the pointwise error estimate restricted to the good set. In the combined wrapper, the convergence good sets and domination full sets remain distinct indexed data.

The development further includes CReal-native support for the countable-avoidance construction used in the smooth-level interface. The formalized support constructs the data-valued nested interval step, the resulting interval sequence, left/right monotonicity, interval-width shrink, Cauchy data for the left endpoints, the limiting apart point, and the dyadic smooth-level data constructor.

`Mathdemo.ChoiceFreeDCTExamples` contains abstract application examples that call both the explicit-smooth and automatic public DCT aliases from proof terms rather than merely checking their names. `Mathdemo.ChoiceFreeDCTConcreteExamples` contains a concrete `PUnit` zero-integral example. This example is intentionally degenerate; it demonstrates end-to-end use of the public API on a nonempty concrete carrier. A nontrivial finite integration model remains future work.

## Internal-code status

`Mathdemo/Internal` contains implementation details in the audited transitive import closure. Files named `CRat_iter*` retain historical or generated intermediate stages that are still in the public import closure. These files are not the intended public API, and this artifact does not claim a large-scale cleanup of the internal implementation library.

## Build and audit

Run from the artifact root:

```bash
./build_audit.sh
```

The script runs at least:

```bash
lake build Mathdemo.CheckSec3PortAxioms
lake env lean SupplementChoiceFreeMeasureDCT.lean
lake env lean ChoiceFreeMeasureDCTPublic.lean
python3 tools/static_no_choice_audit.py
```

It also prints toolchain information and ends successful rerun logs with:

```text
BUILD_AUDIT_EXIT=0
```

Reference logs shipped with the artifact are:

- `logs/build_audit.txt`
- `logs/static_audit.txt`
- `logs/build_audit.reference.txt`
- `logs/static_audit.reference.txt`

A local rerun writes to ignored local files:

- `logs/build_audit.rerun.txt`
- `logs/static_audit.rerun.txt`

This prevents `./build_audit.sh` followed by `sha256sum -c SHA256SUMS` from invalidating the reference checksums.

### Current-worktree build status

On 2026-08-09 a complete `./build_audit.sh` run from the repaired tree finished with `BUILD_AUDIT_EXIT=0` (build stages of 2857 and 2858 jobs in the shipped log), and the static source-closure audit passed with `closure_files: 512` — the same closure set as v0.3.0. The aggregate build `lake build Mathdemo` succeeded with all 2869 jobs, covering the mathematical facade, the Definition 1.1 transcription with its now hypothesis-free adapter, and the point-evaluation model. The shipped logs `logs/build_audit.txt` and `logs/static_audit.txt` record that run. The 512 Lean files tracked by the repository coincide exactly with the audited import closure of the public roots: the artifact contains no Lean file outside the dependency closure of its public theorems.

To verify file integrity after `SHA256SUMS` has been generated:

```bash
sha256sum -c SHA256SUMS
```

To verify the packaged CoRN assumptions audit:

```bash
cd audits/corn
sha256sum -c SHA256SUMS
```

## Axiom audit scope

The declaration-level axiom profile for the listed public aliases, the automatic aliases, and the listed implementation declarations is intended to be exactly:

```text
[propext, Quot.sound]
```

`Quot.sound` is expected because the presented rational layer uses quotient soundness for rational normalization. The following are not expected in the audited public theorem declarations or build output:

- `Classical.choice`
- `Classical.choose`
- `sorryAx`
- `native_decide`
- `Quot.out`

The choice-free claim is about the named public theorem aliases, the listed implementation declarations, and the public transitive Lean source closure shipped in this artifact. It is not a claim about historical development files excluded from this public artifact.

## Static audit

`tools/static_no_choice_audit.py` strips Lean line comments and nested block comments, computes the transitive import closure of these roots, and rejects executable occurrences of forbidden tokens:

- `sorry`
- `admit`
- `Classical.choice`
- `Classical.choose`
- `Classical.`
- `native_decide`
- `Quot.out`
- `unsafe`
- `open Classical`
- `open scoped Classical`
- standalone `classical`

The standalone `classical` check treats underscores and alphanumeric characters as parts of names, so identifiers such as `goalB_classical_dominated_convergence_dataC` are not rejected merely because of their names.

The static audit is a source-level token audit. The declaration-level `#print axioms` output is the authoritative check for the named public declarations.

## AI-assisted development and author responsibility

Generative AI and AI-assisted coding tools were used extensively in the development, refactoring, documentation, and review of this Lean artifact.

The author determined the mathematical scope and formalization goals, reviewed the public theorem statements and proof architecture, executed the reported builds and audits, and assumes responsibility for the contents of the repository. Detailed manual review of the low-level implementation is ongoing.

AI systems are not authors and are not credited as such.

## Contents

See `ARTIFACT_MANIFEST.md` for the top-level manifest and `DEPENDENCY_CLOSURE.md` for the public import closure.

## Citation metadata

`CITATION.cff` contains the author and DOI metadata for this release (software deposit DOI `10.5281/zenodo.22137161`; concept DOI `10.5281/zenodo.21850965`, which resolves to the latest version).

## Note on Lean warnings

The reference Lean build may contain style/linter warnings from the imported historical closure. These are not Lean errors. The audited declarations build successfully and have the stated declaration-level dependency profile.
