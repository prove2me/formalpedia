-- Prove2me | Theorems.Thm_mme_MMObj_square_scalar_value_below
-- name    : mme_MMObj_square_scalar_value_below
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T07:55:11.735465+00:00
-- url     : https://prove2.me/theorems/997408dd-433f-4573-93e6-f7b7dd50d39b
-- title:
--   Scalar extraction gives square matrix tensors every value below the squared side
-- statement:
--   Let $K$ be a field and let $H$ be a nonnegative integer. For every real exponent $\tau$ and every real number $V$ satisfying $0\le V<H^2$, the square matrix-multiplication tensor $\langle H,H,H\rangle$ has $\tau$-value at least $V$: $$\operatorname{HasTauValueAtLeast}(\langle H,H,H\rangle,\tau,V).$$ The bound is independent of the exponent because it is witnessed by scalar matrix blocks, each of volume one. It applies to negative exponents as well as positive ones, without using zero-volume blocks. The statement retains the strict inequality at the squared-side endpoint.
-- source:
--   Induced-matching scalar extraction from square matrix tensors, with subexponential-loss absorption.

import Definitions.Def_mme_tau_value
open MME
universe u
set_option autoImplicit false

theorem mme_MMObj_square_scalar_value_below
    {K : Type u} [Field K]
    (H : ℕ) (tau V : ℝ) (hV : 0 ≤ V) (hVH : V < (H : ℝ) ^ 2) :
    HasTauValueAtLeast (MMObj K H H H) tau V := by sorry
