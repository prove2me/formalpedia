-- Prove2me | solution 1 for NeuroSymbolicRLHF.freeEnergy_le_max
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:17:48.50299+00:00
-- url     : https://prove2.me/submissions/e4ba2118-0c9b-4aaf-ba92-31f2876e78bb

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {β : ℝ} (hβ : 0 < β) {ref r : ι → ℝ}
    (href : IsPosProb ref) : freeEnergy β ref r ≤ univ.sup' univ_nonempty r := by
  set M := univ.sup' univ_nonempty r with hM
  -- every tilt weight is at most `exp (M / β)`, and the reference weights sum to `1`
  have hZ : tiltZ β ref r ≤ Real.exp (M / β) := by
    unfold tiltZ
    calc ∑ i, ref i * Real.exp (r i / β) ≤ ∑ i, ref i * Real.exp (M / β) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (href.pos i).le
          apply Real.exp_le_exp.mpr
          exact div_le_div_of_nonneg_right (Finset.le_sup' r (Finset.mem_univ i)) hβ.le
      _ = Real.exp (M / β) := by rw [← Finset.sum_mul, href.sum_one, one_mul]
  have hZpos : 0 < tiltZ β ref r := by
    unfold tiltZ
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact Finset.sum_pos (fun i _ => mul_pos (href.pos i) (Real.exp_pos _)) ⟨i, Finset.mem_univ i⟩
  have hlog : Real.log (tiltZ β ref r) ≤ M / β := by
    rw [← Real.log_exp (M / β)]
    exact Real.log_le_log hZpos hZ
  unfold freeEnergy
  calc β * Real.log (tiltZ β ref r) ≤ β * (M / β) := mul_le_mul_of_nonneg_left hlog hβ.le
    _ = M := by field_simp
