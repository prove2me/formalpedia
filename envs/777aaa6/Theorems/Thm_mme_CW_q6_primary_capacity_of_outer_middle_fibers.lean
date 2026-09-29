-- Prove2me | Theorems.Thm_mme_CW_q6_primary_capacity_of_outer_middle_fibers
-- name    : mme_CW_q6_primary_capacity_of_outer_middle_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:41:15.001594+00:00
-- url     : https://prove2.me/theorems/543c500d-5911-4082-8f5d-4899240e89f8
-- title:
--   Combine outer-family and common-fiber losses into finite C-tensor capacity
-- statement:
--   Let \(N,Z,X,B,A,H\) be natural numbers with \(X>0\), and let \(\delta\in\mathbb R\). Suppose the retained outer family and common middle fiber satisfy
--   \[
--   Z e^{-N\delta/12}\le A,\qquad
--   B e^{-N\delta/8}\le 4X^2H.
--   \]
--   Then
--   \[
--   \frac{Z^3B^2}{16X^4}e^{-N\delta/2}\le A^3H^2.
--   \]
--
--   This is the exact algebraic normalization used by the q=6 primary C-tensor estimate. Cubing the outer bound and squaring the middle bound makes the loss coefficients add to \(3/12+2/8=1/2\); the factor \(16X^4\) then cancels. The statement contains no tensor or independence assertion.
-- source:
--   Elementary algebraic consequence of the finite outer-family and middle-fiber estimates in Coppersmith--Winograd (1990), journal p. 271.

import Mathlib.Analysis.SpecialFunctions.Exp
open Real

theorem mme_CW_q6_primary_capacity_of_outer_middle_fibers
    (N Z X B A H : ℕ) (loss : ℝ)
    (hX : 0 < X)
    (houter :
      (Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤ (A : ℝ))
    (hmiddle :
      (B : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
        4 * (X : ℝ) ^ 2 * (H : ℝ)) :
    (((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) /
        (16 * (X : ℝ) ^ 4)) *
          Real.exp (-((N : ℝ) * loss / 2)) ≤
      ((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2 := by sorry
