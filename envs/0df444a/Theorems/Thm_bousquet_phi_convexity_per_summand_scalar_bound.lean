-- Prove2me | Theorems.Thm_bousquet_phi_convexity_per_summand_scalar_bound
-- name    : bousquet_phi_convexity_per_summand_scalar_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-24T02:29:24.287453+00:00
-- url     : https://prove2.me/theorems/48355a38-5bb7-42f9-949c-5e56696063de
-- title:
--   Bousquet eq. (6): $\varphi(-\lambda y)\le y\,\varphi(-\lambda)$ for $y\in[0,1]$
-- statement:
--   Bousquet 2002 eq(6) per-summand scalar core. The function phi(x)=e^x-x-1 is convex with phi(0)=0, so by convexity through the origin, for 0<=y<=1, phi(-lam*y) <= y*phi(-lam). Applied to the modified-LSI summand phi(-lam*(Z-Z_k)) with 0<=Z-Z_k<=1 this separates the telescoping (Z-Z_k) part (which sums to E[Z] via condition (3)) from the variance part.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic
open Real

theorem bousquet_phi_convexity_per_summand_scalar_bound (lam y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (Real.exp (-(lam * y)) - (-(lam * y)) - 1)
      ≤ y * (Real.exp (-lam) - (-lam) - 1) := by
  sorry
