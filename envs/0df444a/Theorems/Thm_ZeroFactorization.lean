-- Prove2me | Theorems.Thm_ZeroFactorization
-- name    : ZeroFactorization
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:25:37.735117+00:00
-- url     : https://prove2.me/theorems/622372f0-73d6-4bcd-bf38-9f8d667c884b
-- title:
--   Local factorization $f(z) = (z-\rho)^{m} h(z)$ at a zero, with $h$ analytic and nonvanishing
-- statement:
--   Let $R < 1$, let $f : \mathbb{C} \to \mathbb{C}$ be analytic on a neighbourhood of the closed unit disk $\overline{D}(0,1)$ with $f(0) \ne 0$, and let $\rho$ be a zero of $f$ with $\|\rho\| \le R$ (that is, $\rho$ belongs to `SetOfZeros R f`).
--
--   **Statement.** There exists a function $h_\rho : \mathbb{C} \to \mathbb{C}$, analytic at $\rho$ with $h_\rho(\rho) \ne 0$, such that
--   $$f(z) = (z - \rho)^{m_\rho}\, h_\rho(z) \quad \text{for all } z \text{ in a neighbourhood of } \rho,$$
--   where $m_\rho$ is the order of vanishing of $f$ at $\rho$ (Mathlib's `analyticOrderNatAt f ρ`), and moreover the project's canonical local unit satisfies $\operatorname{ZeroFactor} f\, \rho = h_\rho(\rho)$. (Here `ZeroFactor f z` is defined by choice from the Mathlib factorization when $f$ is analytic at $z$ of finite order, and $0$ otherwise; the theorem shows this choice is realized by an actual local factorization.)
--
--   In the module `Zeta23.FromPNTPlus.StrongPNTPrefix` this is the local input to the construction of the zero-removed factor $C_f$: it is consumed by `CfAnalytic` (analyticity of $C_f$ across the removed zeros) and by `Zeta23.WeilEF.Cf_ne_zero`, both used in the Landau-type lemmas of the Weil explicit-formula side of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/StrongPNTPrefix.lean#L214-L239

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical

theorem ZeroFactorization {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by sorry
