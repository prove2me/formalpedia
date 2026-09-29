-- Prove2me | solution 1 for EmergentGeometry.cutWeight_comb
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T16:54:23.305017+00:00
-- url     : https://prove2.me/submissions/7671adc3-1716-40ed-816d-99eeac85652b

import Mathlib
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

open EmergentGeometry Finset

variable {V : Type*} [Fintype V]

theorem solution (G : BulkGraph V) {m n : ℕ} (F : Fin m → Region V)
    (H : Fin n → Region V)
    (h : ∀ u v : V, G.weight u v ≠ 0 →
      ∑ i, sepBit (H i u) (H i v) ≤ ∑ j, sepBit (F j u) (F j v)) :
    ∑ i, cutWeight G (H i) ≤ ∑ j, cutWeight G (F j) := by
  classical
  -- Clear the common factor `1/2`.
  simp_rw [cutWeight, div_eq_inv_mul]
  rw [← mul_sum, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
  -- Reorder: ∑_i ∑_u ∑_v = ∑_u ∑_v ∑_i
  have hswap {k : ℕ} (R : Fin k → Region V) :
      ∑ i : Fin k, ∑ u, ∑ v, (sepBit (R i u) (R i v) : ℝ) * G.weight u v =
        ∑ u, ∑ v, (∑ i : Fin k, (sepBit (R i u) (R i v) : ℝ)) * G.weight u v := by
    rw [sum_comm]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [sum_comm]
    refine Fintype.sum_congr _ _ fun v => ?_
    rw [← sum_mul]
  rw [hswap H, hswap F]
  refine sum_le_sum fun u _ => sum_le_sum fun v _ => ?_
  by_cases hw : G.weight u v = 0
  · simp [hw]
  · have hineq := h u v hw
    have hineqR :
        (∑ i : Fin n, (sepBit (H i u) (H i v) : ℝ)) ≤
          ∑ j : Fin m, (sepBit (F j u) (F j v) : ℝ) := by
      exact_mod_cast hineq
    exact mul_le_mul_of_nonneg_right hineqR (G.weight_nonneg u v)
