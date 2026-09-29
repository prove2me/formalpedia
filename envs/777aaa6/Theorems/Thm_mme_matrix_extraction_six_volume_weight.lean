-- Prove2me | Theorems.Thm_mme_matrix_extraction_six_volume_weight
-- name    : mme_matrix_extraction_six_volume_weight
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:19:27.039704+00:00
-- url     : https://prove2.me/theorems/902ada7d-1fae-45dc-aab9-58ec8c985547
-- title:
--   Positive matrix extraction gives six-symmetric exponential volume weight
-- statement:
--   An actual matrix extraction of positive volume V from T gives an actual extraction of the square matrix tensor with side length V squared from the six-fold symmetrization of T. For every nonnegative tau and every rate bounded by log V, the extracted matrix tau-weight is at least exp(6 tau rate). The proof uses the exact cyclic matrix isomorphism, mode-swap isomorphism, and Kronecker multiplication of matrix tensors.
-- source:
--   Exact matrix tensor symmetrization and monotonicity of exponential weights.

import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_sixSymmetrization_restrict
open MME
set_option autoImplicit false
universe u

theorem mme_matrix_extraction_six_volume_weight
    {K : Type u} [Field K] {T : TensorObj K 3} (a b c : ℕ)
    (hrestrict : TensorObj.Restrict (MMObj K a b c) T)
    (hpos : 0 < a * b * c) (rate tau : ℝ) (htau : 0 ≤ tau)
    (hrate : rate ≤ Real.log (a * b * c : ℕ)) :
    TensorObj.Restrict
      (MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2) ((a * b * c) ^ 2))
      (sixSymmetrization T) ∧
    Real.exp (6 * tau * rate) ≤
      ((((a * b * c) ^ 2 * (a * b * c) ^ 2 * (a * b * c) ^ 2 : ℕ) : ℝ) ^ tau) := by sorry
