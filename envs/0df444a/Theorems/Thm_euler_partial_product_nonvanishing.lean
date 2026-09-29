-- Prove2me | Theorems.Thm_euler_partial_product_nonvanishing
-- name    : euler_partial_product_nonvanishing
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T06:26:33.237885+00:00
-- url     : https://prove2.me/theorems/6dbac92a-ab5d-49ad-bc67-dcf68e39df90
-- title:
--   Finite Euler products of the corrector are analytic and non-vanishing
-- statement:
--   On any disk where $\Re z > 1/2$, the finite Euler product $g(s) = \prod_{2 \le p \le K,\ p \text{ prime}} (1 - X_p(p,P,\omega) p^{-s})$ is analytic and nowhere zero: each factor is analytic in $s$, and each factor is non-zero because $\|X_p p^{-z}\| = p^{-\Re z} < 1$.

import Mathlib
import Definitions.Def_timepiece_corrector
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

theorem euler_partial_product_nonvanishing (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z ∈ Metric.ball c r, z.re > 1 / 2)
    (P : ℕ) (ω : Ω_infty) (K : ℕ) :
    let g : ℂ → ℂ := fun s => ∏ p ∈ (Finset.Icc 2 K).filter Nat.Prime,
      (1 - X_p p P ω / (p : ℂ) ^ s)
    AnalyticOnNhd ℂ g (Metric.ball c r) ∧
    ∀ z ∈ Metric.ball c r, g z ≠ 0 := by sorry
