import Mathdemo.BishopChengTheorem415Prop

/-!
# The mathematical interface

This file is the *mathematical reading* of the development.  Every declaration
below is a notion or a theorem of Bishop--Cheng constructive measure theory,
carrying the name a mathematician would use for it, and the file is arranged in
the order of the paper's Part I.

Two disciplines govern the file.

1. **No new mathematics.**  Every definition is an abbreviation for an existing
   implementation declaration, and every theorem is discharged by the
   corresponding implementation declaration applied to its arguments.  Nothing
   is proved a second time here.

2. **The axiom footprint is preserved.**  Because (1) performs no proof, the
   output of `#print axioms` on a declaration of this file equals the output on
   the declaration it renames.  The audit block at the end records this, so that
   a change in the implementation which introduced a classical axiom would
   surface here immediately.

The intended reading is: *this file is the paper's Part I, and the
implementation modules are its proof.*
-/

namespace BishopCheng

open BishopCReal BishopSec1P

universe u

/-! ## 1.  The setting  (paper, Section 2) -/

/-- A **partial function** on `X` with values in the presented reals: a map
together with a domain.  Sums are defined on the intersection of domains. -/
abbrev PartialFunction (X : Type u) : Type _ := BFunC X

/-- An **integration space**: a class `L` of partial functions on `X` carrying a
positive linear functional `I`, subject to closure, truncation, and Bishop's
constructive continuity axiom.  Paper, Definition 2.1. -/
abbrev IntegrationSpace (X : Type u) : Type _ := IntSpaceC X

/-- An **integrable function** of `S`.  Following Bishop--Cheng Definition 1.6,
an integrable function is a function *together with a representation*: a
sequence of members of `L` whose absolute integrals sum, the function being the
pointwise sum of the series wherever it converges absolutely. -/
abbrev IntegrableFunction {X : Type u} (S : IntegrationSpace X) : Type _ :=
  IntegrableRepC3 S

/-- The **integral** of an integrable function. -/
abbrev IntegrableFunction.integral {X : Type u} {S : IntegrationSpace X}
    (f : IntegrableFunction S) : CReal :=
  IntegrableRepC3.integral f

/-- The **domain** of an integrable function: the points at which its
representing series converges absolutely. -/
abbrev IntegrableFunction.domain {X : Type u} {S : IntegrationSpace X}
    (f : IntegrableFunction S) : Set X :=
  IntegrableRepC3.domain f

/-- An integrable function is **nonnegative**. -/
abbrev IsNonnegative {X : Type u} {S : IntegrationSpace X}
    (f : IntegrableFunction S) : Prop :=
  RepNonnegC f

/-! ## 2.  Full sets, complemented sets, convergence  (paper, Section 3) -/

/-- `A` is a **full set**: it contains a countable intersection of domains of
integrable functions.  Bishop--Cheng Definition 1.9; the abbreviation unfolds
literally to that statement. -/
abbrev IsFullSet {X : Type u} (S : IntegrationSpace X) (A : Set X) : Prop :=
  IsFullC S A

/-- A **complemented set** of `X`: an ordered pair of subsets whose members are
pairwise distinct.  Bishop--Cheng Definition 2.1. -/
abbrev ComplementedSet (X : Type u) : Type _ := BishopC.BSet X

/-- The complemented set `A` is **integrable**; the witness carries the
integrable representative of its characteristic function, whose integral is the
measure of `A`. -/
abbrev IsIntegrableSet {X : Type u} (S : IntegrationSpace X)
    (A : ComplementedSet X) : Type _ :=
  IntegrableSet1C S A

/-- The **measure** of an integrable complemented set: the integral of the
integrable representative of its characteristic function. -/
abbrev IsIntegrableSet.measure {X : Type u} {S : IntegrationSpace X}
    {A : ComplementedSet X} (hA : IsIntegrableSet S A) : CReal :=
  hA.rep.integral

/-- The view of an integrable function as a partial function with proof-relevant
domain data.  This is the form in which convergence in measure compares values,
since a value may be read off only where the representing series is known to
converge. -/
abbrev IntegrableFunction.asPartialFunction {X : Type u} {S : IntegrationSpace X}
    (f : IntegrableFunction S) : DataPFunRC X :=
  f.toDataPFunRC

/-- `fn` **converges in measure** to `f`.  Bishop--Cheng Definition 4.11: for
every integrable set `A` and every `ε > 0` there is `N` such that every `n ≥ N`
admits an integrable set `B` with `B¹ ⊆ A¹ ∩ dom f ∩ dom fₙ`, with
`μ(A - B) < ε`, and with `|f x - fₙ x| < ε` for every `x ∈ B`. -/
abbrev ConvergesInMeasure {X : Type u} (S : IntegrationSpace X)
    (fn : Nat → IntegrableFunction S) (f : IntegrableFunction S) : Prop :=
  ConvergeInMeasureC S (fun n => (fn n).asPartialFunction) f.asPartialFunction

/-- `u` is bounded in absolute value by `v` **on some full set**.  The full set
is existentially quantified inside this predicate, so a family of such
statements may use a different full set for each member. -/
abbrev AbsLeOnSomeFullSet {X : Type u} {S : IntegrationSpace X}
    (u v : IntegrableFunction S) : Prop :=
  RepAbsLeOnFullC u v

/-- The sequence `fn` is **dominated on full sets** by the single integrable
function `g`: for every index `n` there is a full set on which `|fₙ| ≤ g`.  The
full set may depend on `n`. -/
abbrev DominatedOnFullSets {X : Type u} {S : IntegrationSpace X}
    (fn : Nat → IntegrableFunction S) (g : IntegrableFunction S) : Prop :=
  DominatedOnFullC fn g

/-- The integrals of `fn` **converge to** the integral of `f`, in the ordinary
epsilon formulation: `∀ ε > 0, ∃ N, ∀ n ≥ N, |I(fₙ) - I(f)| < ε`. -/
abbrev IntegralsConvergeTo {X : Type u} {S : IntegrationSpace X}
    (fn : Nat → IntegrableFunction S) (f : IntegrableFunction S) : Prop :=
  RepSeriesTendstoEpsPropC (fun n => (fn n).integral) f.integral

/-! ## 3.  Profiles  (paper, Definitions 3.5-3.6 and Theorem 5.1)

A **profile** on `[a,b]` is a monotone functional on a supply of ramp functions.
The formalization presents the supply by *codes*: `F` is a set of codes and
`embed` interprets a code as a function on `[a,b]`.  This is what makes the
profile theory available without extracting witnesses from extensional objects.
The clauses `bound`, `has_zero`/`embed_zero`, `has_one`/`embed_one` are (a) and
(b) of Bishop--Cheng Definition 3.1. -/

/-- A **profile** on the interval `[a,b]`, presented by codes. -/
abbrev Profile (a b : CReal) (hab : regularSeqLtProp a b) : Type _ :=
  BishopSec3P.ProfileC a b hab

/-- The profile is **smooth at the level `t`**: there is a value `λ̄` such that
`λ(f)` is within `ε` of `λ̄` for every code `f` of the supply which is `1` above
`t + δ` and `0` below `t - δ`.  This is the constructive substitute for the
continuity of a monotone function at `t`. -/
abbrev Profile.IsSmoothAt {a b : CReal} {hab : regularSeqLtProp a b}
    (P : Profile a b hab) (t : CReal) : Prop :=
  BishopSec3P.ProfileC.IsSmoothAtC P t

/-- The **partition data** underlying the smoothness theorem: for a positive
tolerance `eps` and a positive `n` such that the total variation
`λ(1) - λ(0)` of the profile is below `(n+1)·eps`, this produces the finitely
many levels excluded at that stage.

The hypothesis is Bishop and Cheng's condition `(n(k)+1)k⁻¹ > λ(1) - λ(0)` in
the proof of their Theorem 3.5. -/
noncomputable abbrev Profile.partition
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : Profile a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :=
  BishopSec3P.lemma_3_4DataC P heps n hn h_cond

/-- The **exceptional sequence** of an integrable function `h` on `(a,b)`:
an explicit sequence of levels outside of which the profile of `h` is smooth.

This is the crucial point of the whole development.  Theorem 3.5 of
Bishop--Cheng is *not* rendered as "the set of non-smooth levels is countable"
with an existentially hidden enumeration; the exceptional levels arrive as this
explicit sequence, and the countable-avoidance construction of Section 4 below
is then applied to it. -/
noncomputable abbrev exceptionalLevels {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) : Nat → CReal :=
  BishopSec3P.thm36ExceptionSeqC h hab ha

/-- The level `t` is **apart from every exceptional level** of `h`. -/
abbrev IsApartFromExceptionalLevels {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) (t : CReal) : Prop :=
  ∀ n, regularSeqLtProp CReal.zero
    (CReal.abs (CReal.sub t (exceptionalLevels h hab ha n)))

/-- The **profile of an integrable function** `h` on `(a,b)`: the functional
sending a ramp code to the integral of the corresponding truncation of `h`. -/
noncomputable abbrev profileOf {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) : Profile a b hab :=
  BishopSec3P.thm36A2_profileDefaultC h hab ha

/-- **Smoothness away from the exceptional levels**  (paper, Theorem 5.1;
Bishop--Cheng Theorem 3.5).

The profile of `h` is smooth at every level of `(a,b)` apart from every member
of the exceptional sequence.  Note the form of the statement: the exceptional
levels are the explicitly given `exceptionalLevels h hab ha`, not an
existentially quantified enumeration of a "countable set". -/
theorem profile_isSmoothAt_of_apart {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : IsApartFromExceptionalLevels h hab ha t) :
    (profileOf h hab ha).IsSmoothAt t :=
  BishopSec3P.thm_3_6_forall_apart_smoothC h hab ha t hat htb hT

/-- The **smooth value** `λ̄(t)` of the profile of `h` at an apart level `t`.
It is the common measure of the two level sets at `t`. -/
noncomputable abbrev smoothValue {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : IsApartFromExceptionalLevels h hab ha t) : CReal :=
  BishopSec3P.thm36C_lambdaBarC h hab ha t hat htb hT

/-! ## 4.  Countable avoidance  (paper, Lemma 5.3)

Bishop's nested-interval construction.  Given any sequence of reals and any
nondegenerate interval, it produces a point of the interval apart from every
member of the sequence.  Over presented reals this is a *construction*: the
cotransitivity split needed at each stage is decided from rational
approximations and returned as data, so no choice principle is invoked.

Everything here is stated over the presented reals `CReal` themselves.  The
development contains no abstract real-number typeclass on the route to the
theorem; the only quantified structure is the integration space. -/

/-- **A real apart from every member of a sequence**, as data: a point `t` of
the interval `(a,b)` together with its two strict bounds and, for every `n`, the
apartness of `t` from `s n`. -/
abbrev ApartFromSequence (s : Nat → CReal) (a b : CReal)
    (hab : regularSeqLtProp a b) : Type :=
  BishopSec3P.Thm36B1ApartPointDataC s a b hab

/-- **Countable avoidance over the presented reals.**  For every sequence `s` of
presented reals and every nondegenerate interval `(a,b)`, a point of `(a,b)`
apart from every member of `s` is *constructed*, by the nested-interval
construction: the intervals, their monotonicity and shrinking, the Cauchy data
for the left endpoints, and the limit are all produced explicitly. -/
noncomputable abbrev apartFromSequence (s : Nat → CReal) {a b : CReal}
    (hab : regularSeqLtProp a b) : ApartFromSequence s a b hab :=
  BishopSec3P.thm36B1_apartPointDataC s hab

/-- The same statement in propositional form, for readers who do not need the
witness.  It is obtained from the construction, not from a choice principle. -/
theorem exists_real_apart_from_sequence (s : Nat → CReal) {a b : CReal}
    (hab : regularSeqLtProp a b) :
    ∃ t : CReal, regularSeqLtProp a t ∧ regularSeqLtProp t b ∧
      ∀ n : Nat, regularSeqLtProp CReal.zero (CReal.abs (CReal.sub t (s n))) :=
  ⟨(apartFromSequence s hab).t, (apartFromSequence s hab).a_lt,
    (apartFromSequence s hab).lt_b, (apartFromSequence s hab).apart⟩

/-! ## 5.  Integrability of level sets  (paper, Theorem 5.2) -/

/-- **Level sets are integrable at an apart level, with equal measures.**

For an integrable `h` and a level `t` in `(a,b)` apart from every exceptional
level, both complemented sets
`A = ({h ≥ t}, {h < t})` and `B = ({h > t}, {h ≤ t})`
are integrable, and both have measure `λ̄(t)`.  The result is returned as data:
the two sets, their integrability witnesses, and the two measure equations. -/
noncomputable abbrev levelSetsIntegrableAtApartLevel
    {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : IsApartFromExceptionalLevels h hab ha t) :=
  BishopSec3P.thm_3_6_forall_apart_measureC h hab ha t hat htb hT

/-- **The two level sets have the same measure.**  The `≥`-pair and the
`>`-pair produced at an apart level `t` carry equal measures; both equal the
smooth value `λ̄(t)`.  This is the measure equality asserted by Bishop and Cheng
in their Theorem 3.6. -/
theorem levelSet_measure_eq {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : IsApartFromExceptionalLevels h hab ha t) :
    IsIntegrableSet.measure
        (levelSetsIntegrableAtApartLevel h hab ha t hat htb hT).1.2.1 ≈
      IsIntegrableSet.measure
        (levelSetsIntegrableAtApartLevel h hab ha t hat htb hT).2.2.1 :=
  BishopSec3P.thm_3_6_AB_measure_eqC h hab ha t hat htb hT

/-! ### The dyadic supply of admissible levels  (paper, Lemma 5.3 applied)

Two distinct pieces of data occur here and must not be confused.

* `DyadicSmoothLevels h` chooses, in every dyadic window `(2^{-(n+1)}, 2^{-n})`,
  a level at which the profile of `h` is smooth.  This is where countable
  avoidance is used.
* `DyadicLevelSetData h` records the resulting levels *together with* the
  integrable level sets at them and their measures.

`DyadicSmoothLevels.levelSets` is the bridge from the first to the second, and
is exactly the place where Theorem 5.2 is applied. -/

/-- **Smooth levels in every dyadic window**: for every `n`, a level in
`(2^{-(n+1)}, 2^{-n})` at which the profile of `h` is smooth. -/
abbrev DyadicSmoothLevels {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) : Type _ :=
  BishopSec3P.Lemma43DyadicSmoothDataC h

/-- The dyadic smooth levels of an integrable function, **constructed**.  No
hypotheses are required: the exceptional levels of `h` are enumerated by
`exceptionalLevels` and the countable-avoidance construction of Section 4
supplies an admissible level in each dyadic window. -/
noncomputable abbrev dyadicSmoothLevels {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) : DyadicSmoothLevels h :=
  BishopSec3P.lemma43DyadicSmoothDataC_construct h

/-- **Dyadic level-set data** for `h`: for every `n` an admissible level
`αₙ ∈ (2^{-(n+1)}, 2^{-n})` together with the integrable level set
`Aₙ = ({h ≥ αₙ}, {h < αₙ})` and its measure.  This is the form in which the
level sets enter the convergence argument. -/
abbrev DyadicLevelSetData {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) : Type _ :=
  BishopSec3P.Lemma43LevelSetSeqDataC h

/-- **From smooth levels to level sets**: applying Theorem 5.2 at each of the
chosen dyadic levels turns smooth-level data into level-set data. -/
noncomputable abbrev DyadicSmoothLevels.levelSets {X : Type u}
    {S : IntegrationSpace X} {h : IntegrableFunction S}
    (D : DyadicSmoothLevels h) : DyadicLevelSetData h :=
  BishopSec3P.lemma43LevelSetSeqDataC_of_dyadicSmoothDataC h D

/-- The dyadic level-set data of an integrable function, constructed with no
hypotheses: choose smooth levels, then apply Theorem 5.2 at each of them. -/
noncomputable abbrev dyadicLevelSetData {X : Type u} {S : IntegrationSpace X}
    (h : IntegrableFunction S) : DyadicLevelSetData h :=
  (dyadicSmoothLevels h).levelSets

/-! ## 6.  The uniform complement estimate  (paper, Proposition 5.4) -/

/-- **Uniform complement estimate.**

Let `fn` be a sequence of nonnegative integrable functions dominated pointwise
by a nonnegative integrable `g`, let `D` be dyadic level-set data for `g`, and
let a positive tolerance `eps` be given.  Then one obtains an integrable set, an
index bound, and a positive measure threshold witnessing that every sufficiently
late `fₙ` has small integral outside every sufficiently large integrable subset
of that set. -/
noncomputable abbrev uniformComplementEstimate
    {X : Type u} {S : IntegrationSpace X}
    (fn : Nat → IntegrableFunction S)
    (hnn : ∀ n, IsNonnegative (fn n))
    (g : IntegrableFunction S) (hgnn : IsNonnegative g)
    (D : DyadicLevelSetData g)
    (hdom : ∀ (n : Nat) (x : X)
      (fv : RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe fv.sum gv.sum)
    (eps : CReal) (heps : regularSeqLtProp CReal.zero eps) :=
  BishopSec3P.lemma43UniformComplementData_of_majorantC
    fn hnn g hgnn D hdom eps heps

/-! ## 7.  The theorem  (paper, Theorem 4.1) -/

/-- **Dominated convergence.**

Let `S` be an integration space, let `f` and `fn` be integrable functions of
`S`, suppose that `fn` converges in measure to `f`, and suppose that `fn` is
dominated on full sets by some integrable `g`.  Then the integrals of `fn`
converge to the integral of `f`.

Paper, Theorem 4.1; Bishop--Cheng, Theorem 4.15. -/
theorem dominated_convergence {X : Type u} (S : IntegrationSpace X)
    (fn : Nat → IntegrableFunction S) (f : IntegrableFunction S)
    (hconv : ConvergesInMeasure S fn f)
    (hdom : ∃ g : IntegrableFunction S, DominatedOnFullSets fn g) :
    IntegralsConvergeTo fn f :=
  BishopSec3P.bishop_cheng_thm_4_15_propC S fn f hconv hdom

/-- Dominated convergence with the majorant supplied explicitly. -/
theorem dominated_convergence_of_majorant {X : Type u} (S : IntegrationSpace X)
    (fn : Nat → IntegrableFunction S) (f g : IntegrableFunction S)
    (hconv : ConvergesInMeasure S fn f)
    (hdom : DominatedOnFullSets fn g) :
    IntegralsConvergeTo fn f :=
  BishopSec3P.bishop_cheng_thm_4_15_propC_with_majorant S fn f g hconv hdom

/-! ## 8.  Axiom audit

Every declaration above is a rename or a direct application, so its axiom
footprint is that of the implementation declaration it names.  The expected
output for each entry is `[propext, Quot.sound]`. -/

#print axioms BishopCheng.dominated_convergence
#print axioms BishopCheng.dominated_convergence_of_majorant
#print axioms BishopCheng.exists_real_apart_from_sequence
#print axioms BishopCheng.apartFromSequence
#print axioms BishopCheng.levelSetsIntegrableAtApartLevel
#print axioms BishopCheng.dyadicLevelSetData
#print axioms BishopCheng.uniformComplementEstimate
#print axioms BishopCheng.smoothValue
#print axioms BishopCheng.exceptionalLevels
#print axioms BishopCheng.Profile.partition
#print axioms BishopCheng.profile_isSmoothAt_of_apart
#print axioms BishopCheng.levelSet_measure_eq
#print axioms BishopCheng.profileOf

end BishopCheng
