-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperR7FiniteCutRank
-- name    : ErdosProblems_Erdos269_PaperR7FiniteCutRank
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:11:50.545949+00:00
-- url     : https://prove2.me/theorems/f60e3703-4784-4bef-b282-8cf76e65c9bd
-- title:
--   PaperR7FiniteCutRank
-- statement:
--   Defines a finite cut vector with entries one before the cut and c after it, plus the span of a selected finite family of these vectors over a field.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR7FiniteCutRank.lean#L1-L191
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Paper-complete campaign, round 7: the complete finite cut-rank formula

Target: short-note `res:finite-cut-rank`.  This file generalises the supplied
rational interval-difference engine to an arbitrary field, proves independence
except for the two extreme columns, removes exactly that redundancy, and states
the result using `Matrix.rank`. Repetitions and permutations of columns are
handled by a column-range equality, not an extra independence assumption.

Authored against Lean 4.29.1 and the packet's Mathlib pin.
No admitted statements or additional axioms are introduced.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open Module Submodule

variable {F : Type*} [Field F]

/-- A cut at `k`, with `m` rows. -/
def cutVector (c : F) (m k : ℕ) : Fin m → F :=
  fun i => if (i : ℕ) < k then 1 else c









/-- Column-space description, independent of column ordering or repetitions. -/
noncomputable def cutSpan (c : F) (m : ℕ) (E : Finset ℕ) :
    Submodule F (Fin m → F) :=
  Submodule.span F (Set.range (fun k : E => cutVector c m k))







end ErdosProblems.Erdos269.PaperR7


