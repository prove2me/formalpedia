-- Prove2me | solution 1 for mme_complete_split_interface_restrict_common_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T21:20:18.94785+00:00
-- url     : https://prove2.me/submissions/79614097-7412-4cad-b49d-6332d73424c3

import Theorems.Thm_mme_complete_split_power_projection_certificate
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_toQ_kronFin

open MME MME.CompleteSplit Module BigOperators
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem quotient_mul_mono
    {K : Type u} [Field K] {a b c d : TensorQ K 3}
    (hab : TensorQ.le a b) (hcd : TensorQ.le c d) :
    TensorQ.le (a * c) (b * d) := by
  let P := TensorQ.tensorStrassen K 3 (by decide)
  exact TensorQ.le_trans _ _ _ (P.mul_right a b hab c)
    (by simpa only [mul_comm] using P.mul_right c d hcd b)

private theorem quotient_fin_prod_mono
    {K : Type u} [Field K] {n : ℕ}
    (a b : Fin n → TensorQ K 3) (h : ∀ i, TensorQ.le (a i) (b i)) :
    TensorQ.le (∏ i, a i) (∏ i, b i) := by
  induction n with
  | zero =>
      simpa only [Fin.prod_univ_zero] using
        (TensorQ.le_refl (1 : TensorQ K 3))
  | succ n ih =>
      simp only [Fin.prod_univ_succ]
      exact quotient_mul_mono (h 0)
        (ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ))

/-- A complete-profile interface built from restrictions of a common
source is an actual restriction of that source to the summed power. -/
theorem solution
    {K : Type u} [Field K] {r ell : ℕ}
    (source : TensorObj K 3) (T : Fin r → TensorObj K 3)
    {ι : Fin r → Fin 3 → Type u}
    (b : (t : Fin r) → (i : Fin 3) → Basis (ι t i) K ((T t).V i))
    (label : (t : Fin r) → (i : Fin 3) → ι t i → CompleteWord ell)
    (beta : Fin r → Fin 3 → Profile ell) (epsilon : ℝ≥0)
    (n : Fin r → ℕ) (hsource : ∀ t, TensorObj.Restrict (T t) source) :
    TensorObj.Restrict
      (TensorObj.kronFin r
        (fun t => restrictedPower (T t) (b t) (label t) (beta t) epsilon (n t)))
      (source.kronPow (∑ t, n t)) := by
  apply (TensorQ.le_toQ _ _).mp
  rw [mme_toQ_kronFin, TensorQ.toQ_kronPow]
  have hprod := quotient_fin_prod_mono
    (fun t => TensorQ.toQ
      (restrictedPower (T t) (b t) (label t) (beta t) epsilon (n t)))
    (fun t => TensorQ.toQ (source.kronPow (n t)))
    (fun t => (TensorQ.le_toQ _ _).mpr
      (((mme_complete_split_power_projection_certificate
        (T t) (b t) (label t) (beta t) epsilon (n t)).1).trans
          (mme_restrict_kronPow (hsource t) (n t))))
  simpa only [TensorQ.toQ_kronPow, Finset.prod_pow_eq_pow_sum] using hprod
