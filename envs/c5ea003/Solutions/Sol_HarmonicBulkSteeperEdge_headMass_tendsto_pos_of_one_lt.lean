-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headMass_tendsto_pos_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T05:01:45.189849+00:00
-- url     : https://prove2.me/submissions/64cdf600-32cd-46d1-9d68-55714f94a18c

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter Topology HarmonicBulkSteeperEdge in
theorem solution {a : ℝ} (ha : 1 < a) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => headMass a n m) atTop (nhds (headSum a m / ∑' k : ℕ, pw a k)) ∧
      0 < headSum a m / ∑' k : ℕ, pw a k := by
  have hsum : Summable (fun k : ℕ => pw a k) := by
    unfold pw
    exact Real.summable_nat_rpow.2 (by linarith)
  have hnn : ∀ k : ℕ, 0 ≤ pw a k := fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htpos : 0 < ∑' k : ℕ, pw a k := by
    refine hsum.tsum_pos hnn 1 ?_
    simp [pw]
  have hpw0 : pw a 0 = 0 := by
    unfold pw
    rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
  have hsumR : ∀ n : ℕ, headSum a n = ∑ i ∈ range (n + 1), pw a i := by
    intro n
    unfold headSum
    rw [Finset.sum_range_succ', hpw0, add_zero, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [add_comm]
  have hSm : 0 < headSum a m := by
    unfold headSum
    exact Finset.sum_pos (fun k hk => Real.rpow_pos_of_pos (by
      have := (Finset.mem_Icc.1 hk).1
      exact_mod_cast this) _) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hm⟩⟩
  refine ⟨?_, div_pos hSm htpos⟩
  have hlim : Tendsto (fun n : ℕ => headSum a n) atTop (𝓝 (∑' k : ℕ, pw a k)) := by
    have h := hsum.hasSum.tendsto_sum_nat
    have h' := h.comp (tendsto_add_atTop_nat 1)
    refine h'.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp, hsumR n]
  exact tendsto_const_nhds.div hlim htpos.ne'
