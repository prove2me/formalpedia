-- Prove2me | solution 1 for mme_six_restricted_kron_exponential_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:07:00.441052+00:00
-- url     : https://prove2.me/submissions/87d058b2-2c6e-42dc-a502-f4e639d3d5fc

import Theorems.Thm_mme_six_product_exponential_extraction
import Theorems.Thm_mme_sixSymmetrization_restrict

open BigOperators MME MME.TensorObj
universe u
set_option autoImplicit false

/-- Matrix families from two extracted tensor factors combine with the sum of
their logarithmic rates and transfer back to the original source tensor. -/
theorem solution
    {K : Type u} [Field K] {X Y T : TensorObj K 3}
    (hsource : Restrict (kron X Y) T) (tau rateX rateY : ℝ)
    (hX : ∃ (q : ℕ) (a b c : Fin q → ℕ),
      Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j))) (sixSymmetrization X) ∧
      Real.exp rateX ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau))
    (hY : ∃ (q : ℕ) (a b c : Fin q → ℕ),
      Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j))) (sixSymmetrization Y) ∧
      Real.exp rateY ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ), 0 < q ∧
      Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j))) (sixSymmetrization T) ∧
      Real.exp (rateX + rateY) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  have hparts : ∀ i : Fin 2, ∃ (q : ℕ) (a b c : Fin q → ℕ),
      Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (![X, Y] i)) ∧
      Real.exp (![rateX, rateY] i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    intro i
    fin_cases i
    · exact hX
    · exact hY
  obtain ⟨q, a, b, c, hq, hr, hw⟩ :=
    mme_six_product_exponential_extraction ![X, Y] tau ![rateX, rateY] hparts
  have hiso : Isomorphic (kronFin 2 ![X, Y]) (kron X Y) := by
    rw [← TensorQ.toQ_eq_iff]
    simp only [mme_toQ_kronFin, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, TensorQ.toQ_kron]
  refine ⟨q, a, b, c, hq,
    hr.trans (mme_sixSymmetrization_restrict (hiso.1.trans hsource)), ?_⟩
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hw


#print axioms solution
