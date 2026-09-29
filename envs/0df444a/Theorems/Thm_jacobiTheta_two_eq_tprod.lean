-- Prove2me | Theorems.Thm_jacobiTheta_two_eq_tprod
-- name    : jacobiTheta_two_eq_tprod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/391c5635-fc4a-561b-b0b0-4b15720de46d
-- title:
--   Jacobi triple product for vartheta₂(z,τ)
-- statement:
--   Let $z$ and $\tau$ be complex numbers and assume $\operatorname{Im}\tau > 0$. The assertion is that the two-variable Jacobi theta function $\vartheta(z,\tau) = \sum_{n \in \mathbb{Z}} e^{2\pi i n z + \pi i n^2 \tau}$, denoted `jacobiTheta₂` in Mathlib, is equal to the infinite product (in the sense of Mathlib's unconditional `∏'` over the index type $\mathbb{N}$, so over $n = 0, 1, 2, \dots$) of the triple factors
--   $$\bigl(1 - e^{2\pi i (n+1)\tau}\bigr)\bigl(1 + e^{\pi i (2n+1)\tau + 2\pi i z}\bigr)\bigl(1 + e^{\pi i (2n+1)\tau - 2\pi i z}\bigr).$$
--   In the classical variables $q = e^{2\pi i \tau}$ and $w = e^{2\pi i z}$ the $n$-th factor is $(1-q^{n+1})(1+q^{n+1/2}w)(1+q^{n+1/2}w^{-1})$, so the conclusion is exactly Jacobi's triple product identity. The hypothesis $\operatorname{Im}\tau > 0$ is needed for both sides to converge; outside the upper half-plane the two sides are governed by the conventional values assigned to divergent sums and products and the identity is not asserted.
--
--   This is Jacobi's triple product identity, written for the two-variable theta function of the upper half-plane. It is used in the construction of Siegel units on modular curves, where the product expansion gives the analytic input for [`ModularCurve.SiegelUnit.differentiableOn_siegelFun`](thm.html#ModularCurve.SiegelUnit.differentiableOn_siegelFun) and for the transformation behaviour of [`ModularCurve.siegelFun_specialLinearGroup_smul`](thm.html#ModularCurve.siegelFun_specialLinearGroup_smul) under $\mathrm{SL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_jacobiTheta_two_eq_tprod.lean

import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
open Complex

theorem jacobiTheta_two_eq_tprod (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ = ∏' n : ℕ,
      ((1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z))) := by sorry
