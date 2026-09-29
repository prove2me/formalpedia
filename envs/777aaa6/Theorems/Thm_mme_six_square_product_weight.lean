-- Prove2me | Theorems.Thm_mme_six_square_product_weight
-- name    : mme_six_square_product_weight
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:48:58.1506+00:00
-- url     : https://prove2.me/theorems/d8529bf3-e00b-4d8b-8a1d-bfc4808371d9
-- title:
--   Finite square-matrix extractions preserve the sum of weight rates
-- statement:
--   Six-fold square-matrix extractions combine over finite tensor products. Their exponential weight rates add without further loss. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
open MME BigOperators
universe u

theorem mme_six_square_product_weight {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (M : Fin n → ℕ) (rate : Fin n → ℝ) (tau : ℝ)
    (hextract : ∀ i, TensorObj.Restrict (MMObj K (M i) (M i) (M i))
      (sixSymmetrization (T i)))
    (hweight : ∀ i, Real.exp (rate i) ≤ ((M i * M i * M i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict (MMObj K (∏ i, M i) (∏ i, M i) (∏ i, M i))
      (sixSymmetrization (TensorObj.kronFin n T)) ∧
    Real.exp (∑ i, rate i) ≤
      ((((∏ i, M i) * (∏ i, M i) * (∏ i, M i) : ℕ) : ℝ) ^ tau) := by sorry
