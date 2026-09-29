-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR9.mem_strictSmoothPairs_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:17:14.376509+00:00
-- url     : https://prove2.me/submissions/1e0c00a9-4e2a-4d32-bc77-f242f20241a6

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_PaperR9SourceCounts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
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
# Exact source-count normalisation for certificate reconstruction

This module does not certify a generated list by fiat. It starts with the
library's actual strictSmoothPairs / strictSmoothExponents and proves the
one-dimensional pair count, cumulative pure-power count, threshold difference,
and complete ordered dyadic digit formula.

The executable pair evaluator uses successive division. It does not enumerate
a box of side `x` or compute real logarithms. Its boundary sweep is linear in the two exponent bounds. No unproved
logarithmic-interval or Euclidean floor-sum optimisation is used by this return.

Source APIs reused: RestrictedFloorSum.lean, strictSmoothShell_card,
restrictedPurePowerCount_eq_restrictedLogFloorSum, restrictedLogFloorSum_succ_sub;
Mathlib/Data/Nat/Log.lean; Lean src/Init/Data/Nat/Div/Basic.lean.
Finset.card_eq_sum_card_fiberwise is reused exactly as in the supplied
RestrictedFloorSum.lean:332.

-/

namespace ErdosProblems.Erdos269.PaperR9
open Finset
end ErdosProblems.Erdos269.PaperR9

open Finset
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR9 in
theorem solution {q r x : ℕ} (hq : 1 < q) (hr : 1 < r)
    (e : ℕ × ℕ) :
    e ∈ strictSmoothPairs q r x ↔ q ^ e.1 * r ^ e.2 < x := by
  constructor
  · exact fun he => (mem_filter.mp he).2
  · intro h
    have hprod : 0 < q ^ e.1 * r ^ e.2 := by positivity
    have hqpow : q ^ e.1 ≤ q ^ e.1 * r ^ e.2 :=
      Nat.le_of_dvd hprod ⟨r ^ e.2, rfl⟩
    have hrpow : r ^ e.2 ≤ q ^ e.1 * r ^ e.2 :=
      Nat.le_of_dvd hprod ⟨q ^ e.1, by ring⟩
    have hi : e.1 < x := (Nat.lt_pow_self hq).trans_le (hqpow.trans h.le)
    have hj : e.2 < x := (Nat.lt_pow_self hr).trans_le (hrpow.trans h.le)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hi, mem_range.mpr hj⟩, h⟩
