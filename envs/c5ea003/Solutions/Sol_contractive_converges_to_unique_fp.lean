-- Prove2me | solution 1 for contractive_converges_to_unique_fp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:54:44.818208+00:00
-- url     : https://prove2.me/submissions/a29f16ff-be8c-4240-8165-a051532f804d

import Mathlib
import Definitions.Def_Bridges_PosetTheory_NeuralPDEUniversality
theorem solution {α : Type*} (rg : RGSemigroup α)
    {c : ℝ} (hc : rg.IsContractive c) {fp : α}
    (hfp : rg.IsFixedPoint fp) (x : α) :
    rg.ConvergesToFixed x fp := by
  obtain ⟨hc0, hc1, hcon⟩ := hc
  have hfix : rg.coarsen fp = fp := hfp
  -- geometric decay of the distance to the fixed point
  have hbound : ∀ n, rg.dist (rg.iterate n x) fp ≤ c ^ n * rg.dist x fp := by
    intro n
    induction n with
    | zero => simp [RGSemigroup.iterate]
    | succ n ih =>
      have h1 := hcon (rg.iterate n x) fp
      rw [hfix] at h1
      show rg.dist (rg.coarsen (rg.iterate n x)) fp ≤ c ^ (n + 1) * rg.dist x fp
      calc rg.dist (rg.coarsen (rg.iterate n x)) fp ≤ c * rg.dist (rg.iterate n x) fp := h1
        _ ≤ c * (c ^ n * rg.dist x fp) := mul_le_mul_of_nonneg_left ih hc0
        _ = c ^ (n + 1) * rg.dist x fp := by ring
  refine ⟨hfp, fun ε hε => ?_⟩
  have hd : 0 ≤ rg.dist x fp := rg.dist_nonneg x fp
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < rg.dist x fp + 1)) hc1
  refine ⟨N, fun n hn => ?_⟩
  have hpow : c ^ n ≤ c ^ N := pow_le_pow_of_le_one hc0 hc1.le hn
  have hcN : 0 ≤ c ^ N := pow_nonneg hc0 N
  have h2 : c ^ N * (rg.dist x fp + 1) < ε := by rwa [lt_div_iff₀ (by linarith)] at hN
  calc rg.dist (rg.iterate n x) fp ≤ c ^ n * rg.dist x fp := hbound n
    _ ≤ c ^ N * rg.dist x fp := mul_le_mul_of_nonneg_right hpow hd
    _ ≤ c ^ N * (rg.dist x fp + 1) := mul_le_mul_of_nonneg_left (by linarith) hcN
    _ < ε := h2
