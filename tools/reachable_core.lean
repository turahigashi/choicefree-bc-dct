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
  IO.println s!"当方のモジュール数     : {ourMods.size}"
  IO.println s!"★ソースに書かれた宣言 : {src.size}"
  IO.println s!"  うち主定理群から到達 : {used.size}  ({(used.size*100)/src.size}%)"
  IO.println s!"  到達しない           : {unused.size}  ({(unused.size*100)/src.size}%)"
  for k in [`BishopSec3P.bishop_cheng_thm_4_15_propC, `BishopSec3P.thm_3_6_all_posC,
            `BishopSec1P.IntSpaceC, `BishopSec3P.lemma_3_4DataC,
            `BishopSec3P.thm_3_5_smooth_aeC] do
    IO.println s!"  [検査] {k} 到達= {r.contains k}"
  IO.println "\n── 到達しない宣言が住むモジュール 上位25 ──"
  let mut m : Std.HashMap String Nat := {}
  for n in unused do
    let p := match env.getModuleFor? n with | some mo => mo.toString | none => "?"
    m := m.insert p ((m.getD p 0) + 1)
  for (k,v) in (m.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 25 do
    IO.println s!"  {v}\t{k}"
  IO.println "\n── 到達する宣言が住むモジュール 上位12 ──"
  let mut m2 : Std.HashMap String Nat := {}
  for n in used do
    let p := match env.getModuleFor? n with | some mo => mo.toString | none => "?"
    m2 := m2.insert p ((m2.getD p 0) + 1)
  for (k,v) in (m2.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 12 do
    IO.println s!"  {v}\t{k}"
  IO.println s!"\n到達する宣言が触れるモジュール数 : {m2.size} / 511"
  IO.println s!"到達しない宣言が住むモジュール数 : {m.size} / 511"
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
  IO.println "\n════ 試行錯誤の痕跡（iter 系モジュール）と本体の分離 ════"
  -- ★ファイル単位：到達宣言を1つも含まないモジュール＝削除候補
  let mut liveMods : NameSet := {}
  for n in used do
    match env.getModuleFor? n with | some mo => liveMods := liveMods.insert mo | none => pure ()
  let dead := ourMods.filter (fun mo => !liveMods.contains mo)
  IO.println s!"\n★ファイル単位"
  IO.println s!"  到達宣言を含むモジュール : {liveMods.size} / {ourMods.size}"
  IO.println s!"  削除候補（1つも含まない）: {dead.size} / {ourMods.size}"
  IO.println s!"iter 系モジュール数 : {iterMods.size} / 511"
  IO.println s!"  iter 系の宣言     : {iterAll.size}   到達 {iterUsed.size}  ({(iterUsed.size*100)/(max iterAll.size 1)}%)"
  IO.println s!"  本体側の宣言      : {restAll.size}   到達 {restUsed.size}  ({(restUsed.size*100)/(max restAll.size 1)}%)"
