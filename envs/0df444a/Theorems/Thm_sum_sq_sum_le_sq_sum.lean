-- Prove2me | Theorems.Thm_sum_sq_sum_le_sq_sum
-- name    : sum_sq_sum_le_sq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:01.782799+00:00
-- url     : https://prove2.me/theorems/ae7f684e-20f1-4372-8e19-c88f491c6b48
-- title:
--   sum sq sum le sq sum: sum sq sum le sq sum
-- statement:
--   **Minkowski's inequality** for a finite family of vectors, in sum-of-squares form: if the
--   `ℓ²`-norm of each `F y` is at most `t y`, then the `ℓ²`-norm of `∑ y, F y` is at most
--   `∑ y, t y`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L60-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L60-L72

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
set_option autoImplicit true
@[expose] public section
public section

theorem sum_sq_sum_le_sq_sum {X Y : Type*} [Fintype X] [Fintype Y] (F : Y → X → ℝ) (t : Y → ℝ)
    (ht0 : ∀ y, 0 ≤ t y) (ht : ∀ y, ∑ x, F y x ^ 2 ≤ t y ^ 2) :
    ∑ x, (∑ y, F y x) ^ 2 ≤ (∑ y, t y) ^ 2 := by sorry
