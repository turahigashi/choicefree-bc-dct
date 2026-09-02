import ChoiceFreeMeasureDCTPublic
import Mathdemo

/-! # Vacuous-statement check

The source-closure scan of the audit is lexical: it matches `: True :=` on one line.
A statement written across lines, or one whose conclusion merely *reduces* to `True`,
escapes it.  This file performs the complete check the paper describes: it enumerates
the declarations the development writes in source, strips the leading binders from
each type, reduces the conclusion to weak head normal form, and reports every
declaration whose conclusion is `True`.

A declaration whose conclusion is `True` carries no information, so a vacuous
statement can never contribute to a proof; the point of the check is that a
*plausibly named* one can be mistaken by a reader for a substantive result.
-/

open Lean Lean.Meta

/-- Strip the leading binders and reduce; is what remains `True`? -/
def conclusionIsTrue (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ concl => do
    let c ← whnf concl
    return c.isConstOf ``True

def report : MetaM Unit := do
  let env ← getEnv
  let ourMods := env.header.moduleNames.filterMap (fun m =>
    let s := m.toString
    if s.startsWith "Mathdemo" || s.startsWith "ChoiceFree" || s.startsWith "Supplement"
       || s.startsWith "Bishop" then some m else none)
  let ourModSet : NameSet := ourMods.foldl (·.insert ·) {}
  let mut src : Array Name := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleFor? n with
    | some m => if ourModSet.contains m && (Lean.declRangeExt.find? env n).isSome then
                  src := src.push n
    | none   => pure ()
  IO.println s!"modules of this development : {ourMods.size}"
  IO.println s!"declarations written in source : {src.size}"
  let mut vacuous : Array Name := #[]
  let mut skipped : Array Name := #[]
  for n in src do
    match env.find? n with
    | none => pure ()
    | some ci =>
      -- Inductive types, constructors and recursors are not statements.
      match ci with
      | ConstantInfo.inductInfo _ | ConstantInfo.ctorInfo _
      | ConstantInfo.recInfo _   | ConstantInfo.quotInfo _ => pure ()
      | _ =>
        try
          if ← conclusionIsTrue ci.type then vacuous := vacuous.push n
        catch _ => skipped := skipped.push n
  IO.println s!"declarations examined : {src.size - skipped.size}"
  IO.println s!"skipped (elaboration error while reducing) : {skipped.size}"
  for n in skipped do IO.println s!"  skipped {n}"
  IO.println s!"vacuous statements (conclusion reduces to True) : {vacuous.size}"
  for n in vacuous do IO.println s!"  vacuous {n}"
  -- Compare against the recorded list, in both directions: an unlisted vacuous
  -- statement is a finding, and a listed name that is no longer vacuous means the
  -- list has gone stale and is no longer describing the tree.
  let known ← IO.FS.lines "tools/vacuous_statements_known.txt"
  let knownSet : NameSet :=
    known.foldl (fun acc l =>
      let t := l.trim
      if t.isEmpty || t.startsWith "#" then acc else acc.insert t.toName) {}
  let vacSet : NameSet := vacuous.foldl (·.insert ·) {}
  let unlisted := vacuous.filter (fun n => !knownSet.contains n)
  let mut stale : Array Name := #[]
  for n in known do
    let t := n.trim
    if !t.isEmpty && !t.startsWith "#" && !vacSet.contains t.toName then
      stale := stale.push t.toName
  IO.println s!"recorded vacuous statements : {knownSet.size}"
  for n in unlisted do IO.println s!"  UNLISTED VACUOUS {n}"
  for n in stale do IO.println s!"  STALE ENTRY (no longer vacuous) {n}"
  if unlisted.size == 0 && stale.size == 0 && skipped.size == 0 then
    IO.println "VACUOUS STATEMENT CHECK PASSED"
  else
    IO.println "VACUOUS STATEMENT CHECK FAILED"

def main : IO Unit := do
  let env ← importModules #[{module := `ChoiceFreeMeasureDCTPublic}, {module := `Mathdemo}] {}
  let ctx : Core.Context :=
    { fileName := "vacuous_statement_check", fileMap := default, maxHeartbeats := 0 }
  let _ ← (report.run' {} {}).toIO ctx { env := env }
  pure ()
