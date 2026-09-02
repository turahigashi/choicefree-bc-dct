import ChoiceFreeMeasureDCTPublic
import Mathdemo
open Lean

/-- ★value? は定理の証明項を返さないので構成子に直接照合する（CollectAxioms と同じ流儀） -/
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

def main : IO Unit := do
  let env ← importModules #[{module := `ChoiceFreeMeasureDCTPublic}, {module := `Mathdemo}] {}
  let ourMods := env.header.moduleNames.filterMap (fun m =>
    let s := m.toString
    if s.startsWith "Mathdemo" || s.startsWith "ChoiceFree" || s.startsWith "Supplement"
       || s.startsWith "Bishop" then some m else none)
  let ourModSet : NameSet := ourMods.foldl (·.insert ·) {}
  let mut src : Array Name := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleFor? n with
    | some m => if ourModSet.contains m && (Lean.declRangeExt.find? env n).isSome then src := src.push n
    | none   => pure ()
  let seedMods : List String :=
    ["Mathdemo.MathematicalInterface", "Mathdemo.SourceIntegrationSpaceDef11",
     "Mathdemo.DiracIntegrationSpace",
    "Mathdemo.FiniteWeightedIntegrationSpace", "Mathdemo.CheckSec3PortAxioms",
     "Mathdemo.CheckDCTV2Axioms", "Mathdemo.CheckBishopChengTheorem415PropAxioms",
     "SupplementChoiceFreeMeasureDCT", "ChoiceFreeMeasureDCTPublic",
     "Mathdemo.ChoiceFreeDCTConcreteExamples"]
  let mut seeds : List Name := []
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "ChoiceFreeMeasureDCT." && !n.isInternal then seeds := n :: seeds
    else match env.getModuleFor? n with
      | some mo => if seedMods.contains mo.toString && (Lean.declRangeExt.find? env n).isSome
                   then seeds := n :: seeds
      | none => pure ()
  let r := reach env seeds
  let used   := src.filter (fun n => r.contains n)
  let unused := src.filter (fun n => !r.contains n)
  IO.println s!"modules of this development : {ourMods.size}"
  IO.println s!"declarations written in source : {src.size}"
  IO.println s!"  reachable from the claim-carrying modules : {used.size}  ({(used.size*100)/src.size}%)"
  IO.println s!"  not reachable : {unused.size}  ({(unused.size*100)/src.size}%)"
  for k in [`BishopSec3P.bishop_cheng_thm_4_15_propC, `BishopSec3P.thm_3_6_all_posC,
            `BishopSec1P.IntSpaceC, `BishopSec3P.lemma_3_4DataC,
            `BishopSec3P.thm_3_5_smooth_aeC] do
    IO.println s!"  [probe] {k} reachable= {r.contains k}"
  IO.println "\n-- modules holding unreachable declarations, top 25 --"
  let mut m : Std.HashMap String Nat := {}
  for n in unused do
    let p := match env.getModuleFor? n with | some mo => mo.toString | none => "?"
    m := m.insert p ((m.getD p 0) + 1)
  for (k,v) in (m.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 25 do
    IO.println s!"  {v}\t{k}"
  IO.println "\n-- modules holding reachable declarations, top 12 --"
  let mut m2 : Std.HashMap String Nat := {}
  for n in used do
    let p := match env.getModuleFor? n with | some mo => mo.toString | none => "?"
    m2 := m2.insert p ((m2.getD p 0) + 1)
  for (k,v) in (m2.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 12 do
    IO.println s!"  {v}\t{k}"
  IO.println s!"\nmodules touched by reachable declarations : {m2.size} / 511"
  IO.println s!"modules holding unreachable declarations : {m.size} / 511"
  -- ★試行錯誤の痕跡（iter 系）を分離する
  -- モジュール名の最後の成分で判定する
  let isIter (mo : Name) : Bool :=
    let last := mo.getString!
    last.startsWith "CRat_iter" || last.endsWith "iteration1" || last.startsWith "Sec4GenIB"
      || last.endsWith "iteration2"
  let mut iterMods : NameSet := {}
  for mo in ourMods do if isIter mo then iterMods := iterMods.insert mo
  let inIter (n : Name) : Bool :=
    match env.getModuleFor? n with | some mo => iterMods.contains mo | none => false
  let iterAll := src.filter inIter
  let iterUsed := iterAll.filter (fun n => r.contains n)
  let restAll := src.filter (fun n => !inIter n)
  let restUsed := restAll.filter (fun n => r.contains n)
  IO.println "\n==== iteration-named modules separated from the rest ===="
  -- ★ファイル単位：到達宣言を1つも含まないモジュール＝削除候補
  let mut liveMods : NameSet := {}
  for n in used do
    match env.getModuleFor? n with | some mo => liveMods := liveMods.insert mo | none => pure ()
  let dead := ourMods.filter (fun mo => !liveMods.contains mo)
  IO.println s!"\nby file"
  IO.println s!"  modules containing a reachable declaration : {liveMods.size} / {ourMods.size}"
  IO.println s!"  candidates for removal (containing none) : {dead.size} / {ourMods.size}"
  IO.println s!"iteration-named modules : {iterMods.size} / 511"
  IO.println s!"  their declarations : {iterAll.size}   reachable {iterUsed.size}  ({(iterUsed.size*100)/(max iterAll.size 1)}%)"
  IO.println s!"  the rest : {restAll.size}   reachable {restUsed.size}  ({(restUsed.size*100)/(max restAll.size 1)}%)"
