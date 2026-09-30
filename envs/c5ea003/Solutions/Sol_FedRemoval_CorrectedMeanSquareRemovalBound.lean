-- Prove2me | solution 1 for FedRemoval.CorrectedMeanSquareRemovalBound
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-29T19:51:50.295088+00:00
-- url     : https://prove2.me/submissions/7acff4d7-cdab-4608-832b-a8861a27f005

import Theorems.Thm_FedRemoval_RemovalErrorIdentity
import Theorems.Thm_FedRemoval_SurrogateGap
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Conditional reduction to the signed removal identity and surrogate-gap milestones.
Source: Jin et al., arXiv:2306.02216v3, Section III-C, PDF pp. 5--6, Theorem 2;
supplementary Section C5, PDF p. 16, unnumbered displays; Section III-B, PDF p. 5,
equation (6). This proves the corrected finite-law formulation from those milestones.
-/

noncomputable section

open scoped BigOperators
open FedRemoval

set_option autoImplicit false

private lemma three_term_sq {d : ℕ} (a b c : E d) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have hnorm : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le a b) le_rfl)
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ ‖a‖ + ‖b‖ + ‖c‖)).2 hnorm
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖),
    sq_nonneg (‖b‖ - ‖c‖)]

private lemma split_distance_sq {d : ℕ} (w uD uS : E d) :
    ‖w - uS‖ ^ 2 ≤ 2 * (‖w - uD‖ ^ 2 + ‖uD - uS‖ ^ 2) := by
  have hsplit : w - uS = (w - uD) + (uD - uS) := by abel
  have hnorm : ‖w - uS‖ ≤ ‖w - uD‖ + ‖uD - uS‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ ‖w - uD‖ + ‖uD - uS‖)).2 hnorm
  nlinarith [sq_nonneg (‖w - uD‖ - ‖uD - uS‖)]

theorem solution :
    ∀ (n q d k N : ℕ) (D : Data n d k) (s : Finset (Fin n)) (P : Data q d k)
      (μ : ℝ) (p : Law N) (w v r : Fin N → E d),
      s.Nonempty → 0 < q → 0 < μ →
      mean p (fun i ↦ ‖w i - v i - r i‖ ^ 2) ≤
        (6 / μ) * mean p (fun i ↦ solverGap D s P μ (w i) (v i)) +
        6 * mismatch D s P μ ^ 2 *
          (mse p w (optimum D Finset.univ μ) +
            ‖optimum D Finset.univ μ - optimum D s μ‖ ^ 2) +
        3 * mse p r (optimum D s μ) := by
  intro n q d k N D s P μ p w v r hs hq hμ
  have hκ : 0 ≤ mismatch D s P μ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpoint (i : Fin N) :
      ‖w i - v i - r i‖ ^ 2 ≤
        (6 / μ) * solverGap D s P μ (w i) (v i) +
        6 * mismatch D s P μ ^ 2 *
          (‖w i - optimum D Finset.univ μ‖ ^ 2 +
            ‖optimum D Finset.univ μ - optimum D s μ‖ ^ 2) +
        3 * ‖r i - optimum D s μ‖ ^ 2 := by
    let a := inverseHessian P Finset.univ μ
      ((gram P Finset.univ - gram D s) (w i - optimum D s μ))
    have ha : ‖a‖ ≤ mismatch D s P μ * ‖w i - optimum D s μ‖ := by
      dsimp [a, mismatch]
      calc
        _ ≤ ‖inverseHessian P Finset.univ μ‖ *
            ‖(gram P Finset.univ - gram D s) (w i - optimum D s μ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖inverseHessian P Finset.univ μ‖ *
            (‖gram P Finset.univ - gram D s‖ * ‖w i - optimum D s μ‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ = _ := by ring
    have ha_sq : ‖a‖ ^ 2 ≤ mismatch D s P μ ^ 2 * ‖w i - optimum D s μ‖ ^ 2 := by
      simpa [mul_pow] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hκ (norm_nonneg _))).2 ha
    have hsplit := split_distance_sq (w i) (optimum D Finset.univ μ) (optimum D s μ)
    have ha_bound : ‖a‖ ^ 2 ≤ 2 * mismatch D s P μ ^ 2 *
        (‖w i - optimum D Finset.univ μ‖ ^ 2 +
          ‖optimum D Finset.univ μ - optimum D s μ‖ ^ 2) := by
      calc
        _ ≤ mismatch D s P μ ^ 2 * ‖w i - optimum D s μ‖ ^ 2 := ha_sq
        _ ≤ mismatch D s P μ ^ 2 *
            (2 * (‖w i - optimum D Finset.univ μ‖ ^ 2 +
              ‖optimum D Finset.univ μ - optimum D s μ‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsplit (sq_nonneg _)
        _ = _ := by ring
    have hgap := (FedRemoval.SurrogateGap n q d k D s P μ hs hq hμ (w i) (v i)).2
    have hb_bound : ‖surrogateOptimum D s P μ (w i) - v i‖ ^ 2 ≤
        (2 / μ) * solverGap D s P μ (w i) (v i) := by
      rw [norm_sub_rev]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hμ).2
      nlinarith [hgap]
    have hthree := three_term_sq a (surrogateOptimum D s P μ (w i) - v i)
      (optimum D s μ - r i)
    rw [← FedRemoval.RemovalErrorIdentity n q d k D s P μ hs hq hμ (w i) (v i)
      (r i), norm_sub_rev (optimum D s μ) (r i)] at hthree
    calc
      _ ≤ 3 * (‖a‖ ^ 2 + ‖surrogateOptimum D s P μ (w i) - v i‖ ^ 2 +
          ‖r i - optimum D s μ‖ ^ 2) := hthree
      _ ≤ 3 * (2 * mismatch D s P μ ^ 2 *
          (‖w i - optimum D Finset.univ μ‖ ^ 2 +
            ‖optimum D Finset.univ μ - optimum D s μ‖ ^ 2) +
          (2 / μ) * solverGap D s P μ (w i) (v i) +
          ‖r i - optimum D s μ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha_bound hb_bound) le_rfl)
          (by norm_num)
      _ = _ := by ring
  unfold mse mean
  calc
    _ ≤ ∑ i, p.mass i *
        ((6 / μ) * solverGap D s P μ (w i) (v i) +
          6 * mismatch D s P μ ^ 2 *
            (‖w i - optimum D Finset.univ μ‖ ^ 2 +
              ‖optimum D Finset.univ μ - optimum D s μ‖ ^ 2) +
          3 * ‖r i - optimum D s μ‖ ^ 2) := by
      exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hpoint i) (p.nonneg i)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      simp_rw [mul_left_comm (p.mass _) (6 / μ),
        mul_left_comm (p.mass _) (6 * mismatch D s P μ ^ 2),
        mul_left_comm (p.mass _) (3 : ℝ)]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [← Finset.sum_mul, p.total, one_mul]
