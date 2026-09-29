-- Prove2me | solution 1 for mme_CW_coupled_floor_pruning
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T14:49:30.382866+00:00
-- url     : https://prove2.me/submissions/f1a540c5-b3c1-4acf-8a3e-7868ac630c32

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_mme_CW_coupled_pruning_ratio

open MME Filter

namespace CWCoupledFloorPruning

noncomputable def lambda (q : ℕ) (tau : ℝ) : ℝ :=
  2 / ((q : ℝ) ^ (3 * tau) + 2)

noncomputable def L (q : ℕ) (tau : ℝ) (N : ℕ) : ℕ :=
  ⌊lambda q tau * (N : ℝ)⌋₊

noncomputable def G (q : ℕ) (tau : ℝ) (N : ℕ) : ℕ :=
  N - L q tau N

lemma lambda_pos (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) : 0 < lambda q tau := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  unfold lambda
  positivity

lemma lambda_le_one (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) : lambda q tau ≤ 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  unfold lambda
  have hpow : 0 ≤ (q : ℝ) ^ (3 * tau) := by positivity
  rw [div_le_one (by positivity : (0 : ℝ) < (q : ℝ) ^ (3 * tau) + 2)]
  linarith

lemma L_le (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (N : ℕ) : L q tau N ≤ N := by
  unfold L
  apply Nat.floor_le_of_le
  calc
    lambda q tau * (N : ℝ) ≤ 1 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (lambda_le_one q hq tau) (by positivity)
    _ = (N : ℝ) := one_mul _

lemma L_add_G (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (N : ℕ) :
    L q tau N + G q tau N = N := by
  unfold G
  exact Nat.add_sub_of_le (L_le q hq tau N)

lemma tendsto_L_div (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) :
    Tendsto (fun N : ℕ => (L q tau N : ℝ) / (N : ℝ)) atTop
      (nhds (lambda q tau)) := by
  have hreal :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) (le_of_lt (lambda_pos q hq tau)))
  simpa only [L] using hreal.comp tendsto_natCast_atTop_atTop

lemma tendsto_G_div (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) :
    Tendsto (fun N : ℕ => (G q tau N : ℝ) / (N : ℝ)) atTop
      (nhds (1 - lambda q tau)) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub := hone.sub (tendsto_L_div q hq tau)
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hLN : L q tau N ≤ N := L_le q hq tau N
  rw [G, Nat.cast_sub hLN, sub_div,
    div_self (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0)]

lemma limit_pruning_margin_pos (q : ℕ) (hq : 3 ≤ q) (tau : ℝ)
    (htau : 2 ≤ 3 * tau) :
    0 < 100 * (1 - lambda q tau) - 341 * lambda q tau := by
  have hQ : (341 : ℝ) / 100 < (q : ℝ) ^ (3 * tau) / 2 :=
    mme_CW_coupled_pruning_ratio q hq tau htau
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hden : 0 < (q : ℝ) ^ (3 * tau) + 2 := by positivity
  unfold lambda
  rw [div_eq_mul_inv]
  field_simp
  nlinarith

lemma eventually_ratio (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop, 341 * L q tau N < 100 * G q tau N := by
  have htend : Tendsto
      (fun N : ℕ =>
        100 * ((G q tau N : ℝ) / (N : ℝ)) -
          341 * ((L q tau N : ℝ) / (N : ℝ)))
      atTop (nhds (100 * (1 - lambda q tau) - 341 * lambda q tau)) :=
    (tendsto_const_nhds.mul (tendsto_G_div q hq tau)).sub
      (tendsto_const_nhds.mul (tendsto_L_div q hq tau))
  have hpos : 0 < 100 * (1 - lambda q tau) - 341 * lambda q tau :=
    limit_pruning_margin_pos q hq tau htau
  have hevent : ∀ᶠ N : ℕ in atTop,
      0 < 100 * ((G q tau N : ℝ) / (N : ℝ)) -
        341 * ((L q tau N : ℝ) / (N : ℝ)) :=
    (tendsto_order.1 htend).1 0 hpos
  filter_upwards [hevent, eventually_gt_atTop 0] with N hmargin hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hreal : (341 : ℝ) * L q tau N < 100 * G q tau N := by
    rw [div_eq_mul_inv, div_eq_mul_inv] at hmargin
    nlinarith [inv_pos.mpr hNreal]
  exact_mod_cast hreal

lemma eventually_L_pos (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 < L q tau N := by
  exact (tendsto_nat_floor_mul_atTop (lambda q tau)
    (lambda_pos q hq tau)).eventually (eventually_gt_atTop 0)

end CWCoupledFloorPruning

theorem solution
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((q : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      0 < L ∧ 0 < G ∧ L + G = N ∧ 341 * L < 100 * G := by
  filter_upwards
    [CWCoupledFloorPruning.eventually_L_pos q hq tau,
      CWCoupledFloorPruning.eventually_ratio q hq tau htau]
    with N hL hratio
  dsimp only [CWCoupledFloorPruning.L, CWCoupledFloorPruning.G,
    CWCoupledFloorPruning.lambda] at hL hratio ⊢
  exact ⟨hL, by omega, CWCoupledFloorPruning.L_add_G q hq tau N, hratio⟩
