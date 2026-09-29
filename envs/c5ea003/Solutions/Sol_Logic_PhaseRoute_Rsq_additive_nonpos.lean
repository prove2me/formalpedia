-- Prove2me | solution 1 for Logic.PhaseRoute.Rsq_additive_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:35:07.659651+00:00
-- url     : https://prove2.me/submissions/f8e57a9c-4b49-4c64-a3eb-e7d9c06a0624

import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment
import Definitions.Def_Logic_PhaseRouteLeastSquares
open Logic.PhaseRoute Finset in
theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]
    (σ : α ≃ β) (hcard : 2 ≤ Fintype.card α) (u : α → ℝ) (v : β → ℝ) :
    Rsq (graphInd σ) (additive u v) ≤ 0 := by
  classical
  set n : ℝ := (Fintype.card α : ℝ) with hn
  have hβ : Fintype.card β = Fintype.card α := (Fintype.card_congr σ).symm
  have hN : (Fintype.card (α × β) : ℝ) = n * n := by
    rw [Fintype.card_prod, hβ]; push_cast; ring
  have hn2 : (2 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hcard
  have hnpos : 0 < n := by linarith
  set U := ∑ a, u a with hU
  set W := ∑ b, v b with hW
  -- the target has exactly one `1` in each row: its sums
  have hsum_y : ∑ x : α × β, graphInd σ x = n := by
    rw [Fintype.sum_prod_type]
    simp [graphInd, hn]
  have hyy : ∀ x, graphInd σ x * graphInd σ x = graphInd σ x := by
    intro x; unfold graphInd; split_ifs <;> norm_num
  have hsum_yy : ∑ x : α × β, graphInd σ x * graphInd σ x = n := by
    simp only [hyy]; exact hsum_y
  have hsum_yh : ∑ x : α × β, graphInd σ x * additive u v x = U + W := by
    rw [Fintype.sum_prod_type]
    simp only [graphInd, additive, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_ite_eq' Finset.univ (σ a) (fun b => u a + v b)]
    simp only [Finset.mem_univ, if_true, Finset.sum_add_distrib]
    rw [Equiv.sum_comp σ v]
  have hsum_h : ∑ x : α × β, additive u v x = n * U + n * W := by
    rw [Fintype.sum_prod_type]
    simp only [additive, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hβ, ← Finset.mul_sum]
    ring
  set H := ∑ x : α × β, additive u v x * additive u v x with hH
  -- expand the squared error
  have hexp : ∑ x : α × β, (graphInd σ x - additive u v x) * (graphInd σ x - additive u v x)
      = n - 2 * (U + W) + H := by
    have e : ∀ x : α × β, (graphInd σ x - additive u v x) * (graphInd σ x - additive u v x)
        = graphInd σ x * graphInd σ x - 2 * (graphInd σ x * additive u v x)
          + additive u v x * additive u v x := by intro x; ring
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hsum_yy, hsum_yh]
  -- the deviation of the predictor from the constant `1/n` has nonnegative square sum
  have hT : 0 ≤ ∑ x : α × β, (additive u v x - 1 / n) * (additive u v x - 1 / n) :=
    Finset.sum_nonneg fun x _ => mul_self_nonneg _
  have hTexp : ∑ x : α × β, (additive u v x - 1 / n) * (additive u v x - 1 / n)
      = H - 2 / n * ∑ x : α × β, additive u v x
        + (Fintype.card (α × β) : ℝ) * (1 / n * (1 / n)) := by
    have e : ∀ x : α × β, (additive u v x - 1 / n) * (additive u v x - 1 / n)
        = additive u v x * additive u v x - 2 / n * additive u v x + 1 / n * (1 / n) := by
      intro x; ring
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hTexp, hsum_h, hN] at hT
  have hT' : 0 ≤ H - 2 * (U + W) + 1 := by
    have e1 : 2 / n * (n * U + n * W) = 2 * (U + W) := by field_simp
    have e2 : n * n * (1 / n * (1 / n)) = 1 := by field_simp
    linarith [e1, e2]
  have hvar : varr (graphInd σ) = (n - 1) / (n * n) := by
    simp only [varr, cov, avg]
    rw [hsum_yy, hsum_y, hN]
    field_simp
  have hmsse : msse (graphInd σ) (additive u v) = (n - 2 * (U + W) + H) / (n * n) := by
    simp only [msse, avg]
    rw [hexp, hN]
  have hvpos : 0 < varr (graphInd σ) := by
    rw [hvar]; apply div_pos <;> nlinarith
  have hle : varr (graphInd σ) ≤ msse (graphInd σ) (additive u v) := by
    rw [hvar, hmsse]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have h1 := (one_le_div hvpos).mpr hle
  simp only [Rsq]
  linarith
