-- Prove2me | Theorems.Thm_invGamma_neg_nat_deriv_ne_zero
-- name    : invGamma_neg_nat_deriv_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:28:54.76763+00:00
-- url     : https://prove2.me/theorems/6c3933cb-2248-4400-8876-33879a6599e3
-- title:
--   Reciprocal Gamma has simple zeros at nonpositive integers
-- statement:
--   The reciprocal Gamma function has a simple zero at every nonpositive integer $-n$: its complex derivative there is nonzero. This is the local analytic input for proving simplicity of the trivial zeros of completed $L$-function factors.
-- source:
--   Classical reciprocal Gamma recurrence $1/\Gamma(s)=s/\Gamma(s+1)$; see standard treatments of the Gamma function and Mathlib’s reciprocal-Gamma API.

import Mathlib

open Complex

theorem invGamma_neg_nat_deriv_ne_zero (n : ℕ) :
    deriv (fun s : ℂ => (Gamma s)⁻¹) (-(n : ℂ)) ≠ 0 := by sorry
