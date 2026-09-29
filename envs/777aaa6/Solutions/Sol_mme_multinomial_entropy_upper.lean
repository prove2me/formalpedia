-- Prove2me | solution 1 for mme_multinomial_entropy_upper
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T05:14:32.43468+00:00
-- url     : https://prove2.me/submissions/e0f74e73-4e39-4015-a8e6-cbca1d6027dc

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_modern_entropy_data

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {R : Type*} [Fintype R] [DecidableEq R] [Nonempty R] (w : R → ℕ) (m : ℕ)
    (hw : ∀ i, 0 < w i) :
    (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) ≤
      Real.exp ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
        mme_modern_entropyBits
          (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) := by
  classical
  set W : ℕ := ∑ i, w i with hW
  have hWpos : 0 < W := by
    rw [hW]
    exact Finset.sum_pos (fun j _ => hw j)
      ⟨Classical.arbitrary R, Finset.mem_univ _⟩
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  set p : R → ℝ := fun i ↦ (w i : ℝ) / (W : ℝ) with hp
  have hppos : ∀ i, 0 < p i := by
    intro i
    have : (0 : ℝ) < (w i : ℝ) := by exact_mod_cast hw i
    exact div_pos this hWR
  have hpsum : ∑ i, p i = 1 := by
    have : ∑ i, p i = (∑ i, (w i : ℝ)) / (W : ℝ) := by
      simp only [hp, div_eq_mul_inv, ← Finset.sum_mul]
    rw [this, div_eq_one_iff_eq hWR.ne']
    rw [hW]
    push_cast
    rfl
  set k : R → ℕ := fun i ↦ w i * m with hk
  have hksum : ∑ i, k i = W * m := by
    rw [hk, hW, ← Finset.sum_mul]
  have hmem : k ∈ Finset.piAntidiag (Finset.univ : Finset R) (W * m) := by
    rw [Finset.mem_piAntidiag]
    exact ⟨hksum, fun i _ => Finset.mem_univ i⟩
  have hexp := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset R) p (W * m)
  rw [hpsum, one_pow] at hexp
  have hnonneg : ∀ k' ∈ Finset.piAntidiag (Finset.univ : Finset R) (W * m),
      0 ≤ (Nat.multinomial Finset.univ k' : ℝ) * ∏ i, p i ^ k' i := by
    intro k' _
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (hppos i).le _)
  have hkey : (Nat.multinomial Finset.univ k : ℝ) * ∏ i, p i ^ k i ≤ 1 := by
    rw [hexp]
    exact Finset.single_le_sum hnonneg hmem
  have hprodpos : (0 : ℝ) < ∏ i, p i ^ k i :=
    Finset.prod_pos fun i _ => pow_pos (hppos i) _
  have hlog2 : Real.log 2 ≠ 0 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact (Real.log_pos this).ne'
  have hWp : ∀ i, (W : ℝ) * p i = (w i : ℝ) := by
    intro i
    show (W : ℝ) * ((w i : ℝ) / (W : ℝ)) = (w i : ℝ)
    rw [mul_comm]
    exact div_mul_cancel₀ _ hWR.ne'
  have hlogprod : Real.log (∏ i, p i ^ k i) = ∑ i, (k i : ℝ) * Real.log (p i) := by
    rw [Real.log_prod]
    · exact Finset.sum_congr rfl (fun i _ => Real.log_pow _ _)
    · exact fun i _ => (pow_pos (hppos i) _).ne'
  have hEeq :
      (m : ℝ) * ((W : ℝ) * Real.log 2 *
        mme_modern_entropyBits p) = -∑ i, (k i : ℝ) * Real.log (p i) := by
    have hstep : (W : ℝ) * Real.log 2 * mme_modern_entropyBits p =
        ∑ i, -((w i : ℝ) * Real.log (p i)) := by
      simp only [mme_modern_entropyBits, Real.negMulLog]
      have hcollapse :
          (W : ℝ) * Real.log 2 * ((∑ x, -p x * Real.log (p x)) / Real.log 2) =
            (W : ℝ) * ∑ x, -p x * Real.log (p x) := by
        field_simp
      rw [hcollapse, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← hWp i]
      ring
    rw [hstep, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hk]
    push_cast
    ring
  have hprodexp : (∏ i, p i ^ k i) =
      Real.exp (∑ i, (k i : ℝ) * Real.log (p i)) := by
    rw [← hlogprod, Real.exp_log hprodpos]
  have hEexp :
      Real.exp ((m : ℝ) * ((W : ℝ) * Real.log 2 * mme_modern_entropyBits p)) *
        (∏ i, p i ^ k i) = 1 := by
    rw [hprodexp, hEeq, ← Real.exp_add]
    simp
  have hfinal :
      (Nat.multinomial Finset.univ k : ℝ) * (∏ i, p i ^ k i) ≤
        Real.exp ((m : ℝ) * ((W : ℝ) * Real.log 2 * mme_modern_entropyBits p)) *
          (∏ i, p i ^ k i) := by
    rw [hEexp]; exact hkey
  exact le_of_mul_le_mul_right hfinal hprodpos
