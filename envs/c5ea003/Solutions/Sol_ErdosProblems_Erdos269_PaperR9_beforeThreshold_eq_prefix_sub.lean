-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR9.beforeThreshold_eq_prefix_sub
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:19:23.47087+00:00
-- url     : https://prove2.me/submissions/7cbda2e1-fed6-4394-8fd3-1dc3b5e65e10

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_PaperR9SourceCounts
import Theorems.Thm_ErdosProblems_Erdos269_strictSmoothExponents_mono
import Theorems.Thm_ErdosProblems_Erdos269_strictSmoothShell_card
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
theorem solution (p a : ℕ) :
    dyadicBeforeThresholdCount235 p a =
      smoothCountLT 2 3 5 (p ^ Nat.log p (2 ^ (a + 1))) -
        smoothCountLT 2 3 5 (2 ^ a) := by
  let t := p ^ Nat.log p (2 ^ (a + 1))
  have ht : t ≤ 2 ^ (a + 1) := Nat.pow_log_le_self p (by positivity)
  have hset : ((dyadicSmoothShell235 a).filter (fun e =>
      smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < t)) = strictSmoothShell 2 3 5 (2 ^ a) t := by
    ext e
    simp only [mem_filter, mem_dyadicSmoothShell235_iff, strictSmoothShell,
      mem_sdiff, mem_strictSmoothExponents235_iff]
    omega
  change ((dyadicSmoothShell235 a).filter (fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < t)).card = _
  rw [hset]
  by_cases h : 2 ^ a ≤ t
  · exact strictSmoothShell_card 2 3 5 h
  · have hs : strictSmoothExponents 2 3 5 t ⊆ strictSmoothExponents 2 3 5 (2 ^ a) :=
      strictSmoothExponents_mono 2 3 5 (by omega)
    have hc := Finset.card_le_card hs
    have hempty : strictSmoothShell 2 3 5 (2 ^ a) t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨het, hen⟩ := Finset.mem_sdiff.mp he
      exact hen (hs het)
    rw [hempty, card_empty]
    exact (Nat.sub_eq_zero_of_le hc).symm
