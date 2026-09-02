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

/-- Returns `true` when every check passed.  ★The exit status must carry that, not
just the printed line: run standalone, the checker used to print FAILED and exit 0, so
anything reading the status rather than the text would have seen a pass. -/
def report : MetaM Bool := do
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
  -- ★Inductive types, constructors, recursors and quotient primitives are not
  -- statements, so they are not examined.  Counting them as examined would report a
  -- larger check than was performed; they are counted separately instead.
  let mut examined := 0
  let mut notStatements := 0
  for n in src do
    match env.find? n with
    | none => pure ()
    | some ci =>
      -- Inductive types, constructors and recursors are not statements.
      match ci with
      | ConstantInfo.inductInfo _ | ConstantInfo.ctorInfo _
      | ConstantInfo.recInfo _   | ConstantInfo.quotInfo _ =>
        notStatements := notStatements + 1
      | _ =>
        try
          if ← conclusionIsTrue ci.type then vacuous := vacuous.push n
          examined := examined + 1
        catch _ => skipped := skipped.push n
  IO.println s!"not statements (inductives, constructors, recursors, quotients) : {notStatements}"
  IO.println s!"declarations examined : {examined}"
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
  let passed := unlisted.size == 0 && stale.size == 0 && skipped.size == 0
  if passed then
    IO.println "VACUOUS STATEMENT CHECK PASSED"
  else
    IO.println "VACUOUS STATEMENT CHECK FAILED"
  return passed

def main : IO Unit := do
  -- ★A review asked why this reads two roots where the static audit has six.  The
  -- difference is real and cannot be closed here: the static audit reads source text,
  -- so it can scan `SupplementChoiceFreeMeasureDCT.lean`, whereas this check reads an
  -- elaborated environment and that file is not a library target, has no `.olean`, and
  -- cannot be imported.  Nothing is missed by it: the supplement declares nothing --- it
  -- is a file of `#check` and `#print axioms` commands, run by `lake env lean` --- so
  -- there is no statement in it for this check to examine.
  let env ← importModules #[{module := `ChoiceFreeMeasureDCTPublic}, {module := `Mathdemo}] {}
  let ctx : Core.Context :=
    { fileName := "vacuous_statement_check", fileMap := default, maxHeartbeats := 0 }
  let (passed, _) ← (report.run' {} {}).toIO ctx { env := env }
  if !passed then
    throw (IO.userError "VACUOUS STATEMENT CHECK FAILED")
