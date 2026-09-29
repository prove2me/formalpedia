-- Prove2me | Theorems.Thm_mme_dwz_table2_retained_and_hole_denominator_le_exp_sqrt
-- name    : mme_dwz_table2_retained_and_hole_denominator_le_exp_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:26:24.831178+00:00
-- url     : https://prove2.me/theorems/f6d97ca2-91ba-49fb-b5db-6b9c9fa84fee
-- title:
--   Retained hashing and Hole grouping share one square-root loss envelope
-- statement:
--   Let $L$ be the Table-2 word length and let $D_{\rm hash}$ be the exact polynomial denominator in the retained-copy estimate. With the concrete Hole-Lemma parameter $N=4$, one complete repair group has size $g=8(4L+1)$. For
--
--   $$
--   B=32\cdot6^{20}\cdot70!,
--   $$
--
--   the combined hashing and integer-grouping denominator satisfies
--
--   $$
--   D_{\rm hash}\,2g\le e^{B\sqrt{L+1}}.
--   $$
--
--   Thus the factor needed when taking the integer number of complete Hole-repair groups is explicitly carried by the same square-root-exponential envelope; it is not omitted from the finite Equation-(24) count.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Corollary 5.11 and the finite polynomial/hash losses leading to Equations (24)--(25), printed pp. 48--58; elementary Taylor-series absorption of the displayed factors.

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_dwz_table2_retained_and_hole_denominator_le_exp_sqrt
    (L : ℕ) :
    let x : ℝ := (((L + 1 : ℕ) : ℝ))
    let jointPoly : ℝ := (6 * x) ^ 15
    let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
    let zPoly : ℝ := (6 * x) ^ 5
    let compatibilityPoly : ℝ := (6 * x) ^ 9
    let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
    (32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)) *
        (16 * (((4 * L + 1 : ℕ) : ℝ))) ≤
      Real.exp (B * Real.sqrt x) := by
  sorry
