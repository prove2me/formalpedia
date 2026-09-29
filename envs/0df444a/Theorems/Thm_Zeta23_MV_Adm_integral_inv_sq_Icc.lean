-- Prove2me | Theorems.Thm_Zeta23_MV_Adm_integral_inv_sq_Icc
-- name    : Zeta23.MV.Adm.integral_inv_sq_Icc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:50:27.130622+00:00
-- url     : https://prove2.me/theorems/6d82beb4-f679-4944-a1b0-96c113bc5f00
-- title:
--   Closed form: $\int_a^b (u-c)^{-2}\,du = (a-c)^{-1} - (b-c)^{-1}$ for $c \notin [a,b]$
-- statement:
--   Let $a \le b$ be real numbers and let $c$ lie outside the interval $[a, b]$ (that is, $c < a$ or $b < c$). Then the Lebesgue integral over $[a,b]$ of the inverse-square kernel has the closed form
--
--   $$\int_{[a,\,b]} \frac{du}{(u-c)^2} \;=\; \frac{1}{a-c} \;-\; \frac{1}{b-c}.$$
--
--   The hypothesis $c \notin [a,b]$ keeps the integrand bounded on the interval, so the antiderivative $-(u-c)^{-1}$ applies without any singularity.
--
--   **Role.** A closed-form tail integral used in the sum-versus-integral comparison of the spacing module: it is consumed by `Zeta23.MV.Adm.spacing_sq`, the $\sigma = 2$ spacing lemma $\sum_{t \ne s} \delta_t/(\mathrm{freq}_s - \mathrm{freq}_t)^2 \le 9/\delta_s$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Spacing.lean#L89-L104

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Adm
variable {freq δ : ι → ℝ} (h : Adm freq δ)

theorem Zeta23.MV.Adm.integral_inv_sq_Icc {a b c : ℝ} (hab : a ≤ b) (hc : c < a ∨ b < c) :
    ∫ u in Set.Icc a b, ((u - c) ^ 2)⁻¹ = (a - c)⁻¹ - (b - c)⁻¹ := by sorry
