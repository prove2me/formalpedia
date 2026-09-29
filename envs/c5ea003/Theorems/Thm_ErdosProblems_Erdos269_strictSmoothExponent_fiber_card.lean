-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_strictSmoothExponent_fiber_card
-- name    : ErdosProblems.Erdos269.strictSmoothExponent_fiber_card
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:17:17.833166+00:00
-- url     : https://prove2.me/theorems/45ab78df-fd69-43af-8b7f-5c4a551a942b
-- title:
--   StrictSmoothExponent fiber card
-- statement:
--   A projection fiber of strict three-prime exponent triples has the same cardinality as its explicit p-exponent fiber.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L278-L312
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: restricted floor sums and local windows

Problem-owned landing surface for the exact true-shell floor sums and the
local-window residue reduction.  No declaration here asserts the open
cofinal anti-concentration theorem.
-/


open scoped BigOperators

/-! ## Exact finite strict counts -/

















/-! ## Exact two-dimensional fiber formula -/

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.strictSmoothExponent_fiber_card
    (p q r x : ℕ) {e : ℕ × ℕ} (he : e ∈ strictSmoothPairs q r x) :
    ((strictSmoothExponents p q r x).filter
      fun z => (z.2.1, z.2.2) = e).card =
      (strictPExponentFiber p q r x e).card := by sorry
