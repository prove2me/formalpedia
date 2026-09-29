-- Prove2me | Theorems.Thm_Zeta23_LeafIntegrals_W3_core
-- name    : Zeta23.LeafIntegrals.W3_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:49:10.911793+00:00
-- url     : https://prove2.me/theorems/1cede6e7-874d-4135-b969-f9384267ccfe
-- title:
--   Leaf (W3): $\int \psi(r)^2 (2+|r|)^2\,dr \le 18L^2 + 18(c/w)^2$
-- statement:
--   Let $\psi \colon \mathbb{R} \to \mathbb{R}$ and let $L, c, w$ be real constants with $w > 0$. Assume $\psi$ is even in the form $\psi(|r|) = \psi(r)$, satisfies $0 \le \psi \le L$ pointwise, obeys the quadratic decay $\psi(r) \le c/(w r^2)$ for all $r \ne 0$, and $\psi^2$ is integrable. Then $r \mapsto \psi(r)^2 (2+|r|)^2$ is integrable and
--
--   $$\int_{\mathbb{R}} \psi(r)^2\,(2+|r|)^2\,dr \;\le\; 18 L^2 + 18\,(c/w)^2.$$
--
--   The proof uses the majorant $9L^2$ on $|r| \le 1$ and $9(c/w)^2/r^2$ on $|r| \ge 1$.
--
--   **Role.** This is the abstract form of the leaf (W3) of lem:ends: in the project it is applied to the paper's envelope $\psi(r) = \min(L,\ 2/|r|,\ c_\varrho/(w r^2))$ of [eq:psidef], which dominates $|\hat\varphi|$. It is consumed by `Zeta23.PrimeSide.setIntegral_rho_div_gwt_le` in the Section 5 prime-side estimates.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Defs/LeafIntegrals.lean#L115-L204, docstring tags [lem:ends], (W3)

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Real Set

theorem Zeta23.LeafIntegrals.W3_core (ψ : ℝ → ℝ) (L c w : ℝ) (hw : 0 < w)
    (habs : ∀ r, ψ |r| = ψ r) (hnn : ∀ r, 0 ≤ ψ r) (hleL : ∀ r, ψ r ≤ L)
    (hdecay : ∀ r, r ≠ 0 → ψ r ≤ c / (w * r ^ 2)) (hint : Integrable (fun r => ψ r ^ 2)) :
    Integrable (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) ∧
    ∫ r, ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 18 * L ^ 2 + 18 * (c / w) ^ 2 := by sorry
