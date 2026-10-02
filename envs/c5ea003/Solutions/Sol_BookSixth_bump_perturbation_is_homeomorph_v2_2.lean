-- Prove2me | solution 2 for BookSixth.bump_perturbation_is_homeomorph_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T07:06:15.745848+00:00
-- url     : https://prove2.me/submissions/90b0e68c-8f26-4d3e-8094-f9b474b0841f

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_small_displacement_is_homeomorph
open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) (L : ℝ) (hL : 0 ≤ L) (q : ℝ) (hq : 0 ≤ q)
    (hLip : n * (2 * L + q) < 1) (chi : Fin n → Space3 → ℝ)
    (S : Fin n → Space3 → Space3) (hchi : ∀ i, LipschitzWith 1 (chi i))
    (hchiL : ∀ i x, ‖chi i x‖ ≤ L) (hS : ∀ i, LipschitzWith 1 (S i))
    (hqL : ∀ i x, ‖S i x - x‖ ≤ q) (hcont : ∀ i, Continuous (S i))
    (hchiC : ∀ i, Continuous (chi i)) :
    ∃ F : Space3 → Space3,
      Continuous F ∧ ∃ Finv : Space3 → Space3, Continuous Finv ∧
        ∀ x, Finv (F x) = x ∧ ∀ x, F (Finv x) = x ∧
          ∀ x, F x = x + ∑ i, chi i x • (S i x - x) := by
  classical
  set E : Space3 → Space3 := fun x => ∑ i, chi i x • (S i x - x) with hEdef
  have hEcont : Continuous E := by
    show Continuous (fun x : Space3 => ∑ i, chi i x • (S i x - x))
    fun_prop
  have hchi1 : ∀ (i : Fin n) (a b : Space3), ‖chi i a - chi i b‖ ≤ ‖a - b‖ := by
    intro i a b
    have h := (hchi i).dist_le_mul a b
    rw [NNReal.coe_one, one_mul] at h
    calc ‖chi i a - chi i b‖ = |chi i a - chi i b| := (Real.norm_eq_abs _).symm
      _ = dist (chi i a) (chi i b) := (Real.dist_eq _ _).symm
      _ ≤ dist a b := h
      _ = ‖a - b‖ := (dist_eq_norm a b).symm
  have hS1 : ∀ (i : Fin n) (a b : Space3), ‖S i a - S i b‖ ≤ ‖a - b‖ := by
    intro i a b
    have h := (hS i).dist_le_mul a b
    rw [NNReal.coe_one, one_mul] at h
    calc ‖S i a - S i b‖ = dist (S i a) (S i b) := (dist_eq_norm _ _).symm
      _ ≤ dist a b := h
      _ = ‖a - b‖ := (dist_eq_norm a b).symm
  have hkey : ∀ (i : Fin n) (x y : Space3),
      chi i x • (S i x - x) - chi i y • (S i y - y)
        = (chi i x - chi i y) • (S i x - x)
          + chi i y • ((S i x - x) - (S i y - y)) := by
    intro i x y
    funext j
    simp only [smul_sub, sub_smul, smul_add, add_smul, sub_eq_add_neg,
      Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul]
    ring
  have hEbound : ∀ x y : Space3, ‖E x - E y‖ ≤ n * (2 * L + q) * ‖x - y‖ := by
    intro x y
    have hstep : ∀ i : Fin n,
        ‖chi i x • (S i x - x) - chi i y • (S i y - y)‖
          ≤ (2 * L + q) * ‖x - y‖ := by
      intro i
      have hdiff : ‖(S i x - x) - (S i y - y)‖ ≤ 2 * ‖x - y‖ := by
        rw [show (S i x - x) - (S i y - y) = (S i x - S i y) - (x - y) by abel]
        calc ‖(S i x - S i y) - (x - y)‖ ≤ ‖S i x - S i y‖ + ‖x - y‖ := norm_sub_le _ _
          _ ≤ ‖x - y‖ + ‖x - y‖ := add_le_add_left (hS1 i x y) _
          _ = 2 * ‖x - y‖ := by ring
      have htri := norm_add_le ((chi i x - chi i y) • (S i x - x))
        (chi i y • ((S i x - x) - (S i y - y)))
      rw [norm_smul, norm_smul] at htri
      rw [hkey i x y]
      have h1 : ‖(chi i x - chi i y) • (S i x - x)
            + chi i y • ((S i x - x) - (S i y - y))‖
          ≤ ‖chi i x - chi i y‖ * ‖S i x - x‖
            + ‖chi i y‖ * ‖(S i x - x) - (S i y - y)‖ := htri
      have h2 : ‖chi i x - chi i y‖ * ‖S i x - x‖
            + ‖chi i y‖ * ‖(S i x - x) - (S i y - y)‖
          ≤ ‖x - y‖ * q + L * ‖(S i x - x) - (S i y - y)‖ := by
        exact add_le_add
          (mul_le_mul (hchi1 i x y) (hqL i x) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hchiL i y) (norm_nonneg _))
      have h3 : ‖x - y‖ * q + L * ‖(S i x - x) - (S i y - y)‖
          ≤ (2 * L + q) * ‖x - y‖ := by
        have h4 := mul_le_mul_of_nonneg_left hdiff hL
        nlinarith [h4]
      exact h1.trans (h2.trans h3)
    calc ‖E x - E y‖
        ≤ ∑ i, ‖chi i x • (S i x - x) - chi i y • (S i y - y)‖ := by
          simp only [hEdef]
          rw [← Finset.sum_sub_distrib]
          exact norm_sum_le _ _
      _ ≤ ∑ i, (2 * L + q) * ‖x - y‖ := Finset.sum_le_sum fun i _ => hstep i
      _ = (∑ i : Fin n, (2 * L + q)) * ‖x - y‖ := by rw [Finset.sum_mul]
      _ = n * (2 * L + q) * ‖x - y‖ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hFcont : Continuous (fun x : Space3 => x + E x) := by
    fun_prop
  obtain ⟨Sinv, hSicont, hleft, hright, _⟩ :=
    BookSixth.small_displacement_is_homeomorph (n * (2 * L + q))
      ⟨by positivity, hLip⟩ (fun x : Space3 => x + E x) hFcont (by
        intro x y
        simpa only [hEdef, add_sub_cancel_left] using hEbound x y)
  exact ⟨fun x : Space3 => x + E x, hFcont, Sinv, hSicont,
    fun x => ⟨hleft x, fun x => ⟨hright x, fun x => by simp only [hEdef]⟩⟩⟩
