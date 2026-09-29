-- Prove2me | Theorems.Thm_sum_eq_integral_add_integral_deriv
-- name    : sum_eq_integral_add_integral_deriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:26:54.013807+00:00
-- url     : https://prove2.me/theorems/bfc44a54-cecc-430a-851f-f34ef8e4e09d
-- title:
--   Euler–Maclaurin summation with the periodized Bernoulli weight $B_1$
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{C}$ (a fixed function of the ambient development) and let $0 \le a \le b$ be real numbers. Assume $f$ is differentiable at every point of $[a, b]$ and that its derivative $f'$ is continuous on $[a, b]$. Write $B_1$ for the periodized first Bernoulli polynomial
--
--   $$B_1(t) \;=\; t - \lfloor t \rfloor - \tfrac12 \;=\; \{t\} - \tfrac12.$$
--
--   Then the sum of $f$ over the integers $k$ with $\lfloor a \rfloor < k \le \lfloor b \rfloor$ (natural-number floors) satisfies
--
--   $$\sum_{\lfloor a \rfloor < k \le \lfloor b \rfloor} f(k) \;=\; f(a)\,B_1(a) \;-\; f(b)\,B_1(b) \;+\; \int_a^b f(t)\,dt \;+\; \int_a^b f'(t)\,B_1(t)\,dt.$$
--
--   This is the first-order Euler--Maclaurin formula in its standard Bernoulli-weight normalization, expressing a lattice sum as the corresponding integral plus $B_1$-boundary terms and a $B_1$-weighted integral of the derivative.
--
--   It is the foundational identity of the PNT+ Euler--Maclaurin module: iterating or specializing it yields the analytic continuation and growth estimates for Dirichlet series ($\zeta$ in particular), Stirling-type asymptotics, and the comparison of arithmetic sums with integrals that pervades the error-term analysis in the Prime Number Theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/EulerMaclaurin.lean#L67-L79

import Mathlib.NumberTheory.AbelSummation
import Definitions.Def_EulerMaclaurin_defs

/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by sorry
