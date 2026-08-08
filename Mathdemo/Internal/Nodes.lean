import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecialFunctions.Sqrt   -- Technical note.
import Mathlib.Order.FixedPoints                -- Technical note.
import Mathlib.SetTheory.Ordinal.Basic          -- Technical note.
import Mathlib.SetTheory.Ordinal.Exponential    -- Technical note.
import Mathlib.Data.Set.Basic                    -- Technical note.
import Mathlib.Data.Finset.Basic                 -- Technical note.
import Mathlib.Data.Fintype.Basic                -- Technical note.
import Mathlib.Topology.Basic                    -- Technical note.
import Mathlib.Data.Set.Lattice                   -- Technical note.
import Mathlib.Algebra.Group.Basic                -- Technical note.
import Mathlib.Algebra.Group.MinimalAxioms         -- Technical note.
import Mathlib.Tactic.Group                        -- Technical note.
import Mathlib.Data.Set.Image                       -- Technical note.
import Mathlib.Order.Heyting.Basic                  -- Technical note.
import Mathlib.Algebra.Module.Basic                 -- Technical note.
import Mathlib.Tactic.Abel                           -- Technical note.
import Mathlib.Tactic.Ring                           -- Technical note.
import Mathlib.Data.ZMod.Basic                       -- Technical note.
import Mathlib.Algebra.Module.LinearMap.Defs         -- Technical note.
import Mathlib.Algebra.Field.Basic                   -- Technical note.
import Mathlib.Data.Fin.Basic                         -- Technical note.
import Mathlib.Algebra.Group.Hom.Defs                 -- Technical note.
import Mathlib.Logic.Relation                         -- Technical note.

/-!
Import aggregator for the historical internal algebra modules.

This module declares nothing of its own.  It only re-exports the Mathlib imports
that the early `Mathdemo.Internal` modules expect to receive transitively.
-/
