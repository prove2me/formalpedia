-- Prove2me | solution 1 for RGSemigroup.contractive_implies_same_class
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:31:58.69934+00:00
-- url     : https://prove2.me/submissions/5e66b368-8fc0-4c35-bfe3-6bca34f1c56b

import Mathlib
import Definitions.Def_Bridges_PosetTheory_NeuralPDEUniversality
theorem solution {α : Type*} (rg : RGSemigroup α)
    {c : ℝ} (hc : rg.IsContractive c) (x y : α) : rg.SameClass x y := by
  obtain ⟨hc0, hc1, hcon⟩ := hc
  -- `d(Tⁿx, Tⁿy) ≤ cⁿ d(x, y)`
  have hiter : ∀ n : ℕ, rg.dist (rg.iterate n x) (rg.iterate n y) ≤ c ^ n * rg.dist x y := by
    intro n
    induction n with
    | zero => simp [RGSemigroup.iterate]
    | succ n ih =>
      calc rg.dist (rg.iterate (n + 1) x) (rg.iterate (n + 1) y)
          = rg.dist (rg.coarsen (rg.iterate n x)) (rg.coarsen (rg.iterate n y)) := rfl
        _ ≤ c * rg.dist (rg.iterate n x) (rg.iterate n y) := hcon _ _
        _ ≤ c * (c ^ n * rg.dist x y) := mul_le_mul_of_nonneg_left ih hc0
        _ = c ^ (n + 1) * rg.dist x y := by ring
  intro ε hε
  have hd := rg.dist_nonneg x y
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < rg.dist x y + 1))
    hc1
  refine ⟨N, fun n hn => ?_⟩
  have hpow : c ^ n ≤ c ^ N := pow_le_pow_of_le_one hc0 hc1.le hn
  have hcN : 0 ≤ c ^ N := pow_nonneg hc0 N
  calc rg.dist (rg.iterate n x) (rg.iterate n y) ≤ c ^ n * rg.dist x y := hiter n
    _ ≤ c ^ N * (rg.dist x y + 1) := by nlinarith [pow_nonneg hc0 n]
    _ < ε / (rg.dist x y + 1) * (rg.dist x y + 1) :=
        mul_lt_mul_of_pos_right hN (by linarith)
    _ = ε := by field_simp
