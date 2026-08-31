/-
  reachable_core.lean --- which declarations of this artifact does the proof reach?

  Run from the artifact root:

      lake env lean --run tools/reachable_core.lean

  The artifact retains historical and generated intermediate stages (README,
  "Internal-code status").  This tool measures how much of the tree the claims of
  the paper actually depend on.  It reports two numbers that the paper cites:
  the declarations reachable from the public surface, and the modules that
  contain at least one of them.

  Method.  Seed with every declaration of the modules that carry a claim of the
  paper -- the public aliases, the reading interface, the Definition 1.1
  transcription, the point-evaluation model, the supplementary check module and
  the three axiom-check modules -- then take the transitive closure of the
  constants occurring in the type and the value of each declaration.  A
  declaration is counted only if it carries a source position, which excludes
  the projections, equation lemmas and recursors that Lean generates.

  Note.  `ConstantInfo.value?` does not expose the proof term of a theorem in
  this toolchain, so the constructors are matched directly, as `CollectAxioms`
  does.  Using `value?` here silently omits every proof-term dependency.
-/
import ChoiceFreeMeasureDCTPublic
import Mathdemo
open Lean

/-- Constants occurring in the type and the value of `c`. -/
def directDeps (env : Environment) (c : Name) : NameSet :=
  let add (s : NameSet) (e : Expr) := e.getUsedConstants.foldl (·.insert ·) s
  match env.find? c with
  | none => {}
  | some (ConstantInfo.defnInfo v)   => add (add {} v.type) v.value
  | some (ConstantInfo.thmInfo v)    => add (add {} v.type) v.value
  | some (ConstantInfo.opaqueInfo v) => add (add {} v.type) v.value
  | some (ConstantInfo.axiomInfo v)  => add {} v.type
  | some (ConstantInfo.inductInfo v) => v.ctors.foldl (·.insert ·) (add {} v.type)
  | some (ConstantInfo.ctorInfo v)   => add {} v.type
  | some (ConstantInfo.recInfo v)    => add {} v.type
  | some (ConstantInfo.quotInfo v)   => add {} v.type

partial def reach (env : Environment) (seeds : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := seeds
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if !seen.contains c then
      seen := seen.insert c
      for d in (directDeps env c).toList do
        if !seen.contains d then stack := d :: stack
  return seen

/-- The modules that carry a claim of the paper. -/
def claimModules : List String :=
  [ "ChoiceFreeMeasureDCTPublic",
    "SupplementChoiceFreeMeasureDCT",
    "Mathdemo.MathematicalInterface",
    "Mathdemo.SourceIntegrationSpaceDef11",
    "Mathdemo.DiracIntegrationSpace",
    "Mathdemo.ChoiceFreeDCTConcreteExamples",
    "Mathdemo.CheckSec3PortAxioms",
    "Mathdemo.CheckDCTV2Axioms",
    "Mathdemo.CheckBishopChengTheorem415PropAxioms" ]

def main : IO Unit := do
  let env ← importModules #[{module := `ChoiceFreeMeasureDCTPublic}, {module := `Mathdemo}] {}
  let ourMods := env.header.moduleNames.filterMap fun m =>
    let s := m.toString
    if s.startsWith "Mathdemo" || s.startsWith "ChoiceFree" || s.startsWith "Supplement"
       || s.startsWith "Bishop" then some m else none
  let ourModSet : NameSet := ourMods.foldl (·.insert ·) {}
  -- declarations of this artifact that carry a source position
  let mut src : Array Name := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleFor? n with
    | some m => if ourModSet.contains m && (Lean.declRangeExt.find? env n).isSome then
                  src := src.push n
    | none   => pure ()
  -- seeds
  let mut seeds : List Name := []
  for (n, _) in env.constants.toList do
    match env.getModuleFor? n with
    | some m => if claimModules.contains m.toString && (Lean.declRangeExt.find? env n).isSome then
                  seeds := n :: seeds
    | none   => pure ()
  let r := reach env seeds
  let used := src.filter fun n => r.contains n
  let mut live : NameSet := {}
  for n in used do
    match env.getModuleFor? n with | some m => live := live.insert m | none => pure ()
  -- sanity: the principal declarations must be reachable
  let checks : List Name :=
    [ `BishopSec3P.bishop_cheng_thm_4_15_propC, `BishopSec3P.thm_3_5_smooth_aeC,
      `BishopSec3P.thm_3_6_all_posC, `BishopSec3P.lemma_3_4DataC, `BishopSec1P.IntSpaceC ]
  let mut ok := true
  for c in checks do
    let hit := r.contains c
    if !hit then ok := false
    IO.println s!"check {c} reachable={hit}"
  IO.println s!"seed_declarations: {seeds.length}"
  IO.println s!"source_declarations: {src.size}"
  IO.println s!"reachable_declarations: {used.size}"
  IO.println s!"modules_total: {ourMods.size}"
  IO.println s!"modules_with_a_reachable_declaration: {live.size}"
  IO.println (if ok then "REACHABLE CORE CHECK PASSED" else "REACHABLE CORE CHECK FAILED")
