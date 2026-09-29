-- Prove2me | Theorems.Thm_mme_six_product_exponential_extraction
-- name    : mme_six_product_exponential_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:54:04.952817+00:00
-- url     : https://prove2.me/theorems/9d699702-2d84-4f40-95f1-5b7722149e4d
-- title:
--   Finite matrix families attain the sum of their exponential rates
-- statement:
--   Matrix-family extractions from six-fold symmetrized tensors combine over any finite product with the sum of their exponential weight rates and a positive number of output copies. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_toQ_kronFin
open MME BigOperators
universe u

theorem mme_six_product_exponential_extraction
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3)
    (tau : ℝ) (rate : Fin n → ℝ)
    (hextract : ∀ i, ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (T i)) ∧
      Real.exp (rate i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ), 0 < q ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (TensorObj.kronFin n T)) ∧
      Real.exp (∑ i, rate i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by sorry
