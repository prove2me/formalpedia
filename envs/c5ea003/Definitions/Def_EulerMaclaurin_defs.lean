-- Prove2me | Definitions.Def_EulerMaclaurin_defs
-- name    : EulerMaclaurin_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:48:32.905172+00:00
-- url     : https://prove2.me/theorems/31dad85f-f1fe-4761-8761-fd383156de21
-- title:
--   First Bernoulli function $B_1(x) = \{x\} - \tfrac{1}{2}$ for the first-order Euler–Maclaurin formula
-- statement:
--   This bundle provides the basic kernel for the first-order Euler–Maclaurin summation formula, developed by specializing Abel summation and manipulating the resulting integrals.
--
--   **Main definition.**
--
--   - `B1 x` — the first Bernoulli (sawtooth) function $B_1(x) = x - \lfloor x \rfloor - \tfrac{1}{2} = \{x\} - \tfrac{1}{2}$, where $\lfloor x\rfloor$ is the floor of $x$ and $\{x\}$ its fractional part. It is the $1$-periodic, mean-zero kernel appearing as the weight in the integral remainder term of the Euler–Maclaurin formula $\sum_{a < n \le b} f(n) = \int_a^b f(t)\,dt + \int_a^b B_1(t) f'(t)\,dt + \text{boundary terms}$.
--
--   **Downstream use.** The kernel $B_1$ underlies the truncated Euler–Maclaurin representation of the Riemann zeta function $\zeta_0(N, s)$ used in the zeta-bounds files, which extends $\zeta$ to the left of the line $\Re s = 1$ and yields the explicit growth estimates on $\zeta$ and $\zeta'/\zeta$ needed for the prime number theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/EulerMaclaurin.lean (definitions vendored from this file)

import Mathlib.NumberTheory.AbelSummation

/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

section

open Finset Interval MeasureTheory


variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2


