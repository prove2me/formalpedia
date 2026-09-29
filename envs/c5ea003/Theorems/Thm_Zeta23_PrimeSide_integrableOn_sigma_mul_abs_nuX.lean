-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_integrableOn_sigma_mul_abs_nuX
-- name    : Zeta23.PrimeSide.integrableOn_sigma_mul_abs_nuX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:16:03.69077+00:00
-- url     : https://prove2.me/theorems/d955dec6-2272-4586-81f3-ea983d62352f
-- title:
--   Integrability of $\sigma \cdot |\nu|$ off the window
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. Write $\sigma(\tau) = \sum_{0 \le k < d} \psi(\tau - \tau_k)$ for the grid sum of the taper majorant $\psi(r) = \min(L, 2/|r|, c_\varrho/(wr^2))$ [eq:psidef]. Assume $\nu$ continuous, the taper facts `LocalHypsCoreW`, the density bound `NuBound` ($|\nu(\tau)| \le B + \log^+(|\tau|/4T)$), and $T \ge 1$. The theorem asserts that the function
--   $$\tau \;\longmapsto\; \Bigl(\sum_{0 \le k < d} \psi(\tau - \tau_k)\Bigr)\, |\nu(\tau)|$$
--   is Lebesgue integrable on the complement $\mathbb{R} \setminus I$ of the window $I = [T, 2T]$. The proof dominates the integrand by the one-variable half-line majorant $M_{\mathrm{tot}}$ via `dom_left` and `dom_right`: near the window the near-regime majorant is integrable because $\psi$ is, and far from it the $c_\varrho/(w\Delta^2)$ decay beats the $\sqrt{\Delta/T}$ growth absorbed from $\log^+$.
--
--   This is the integrability of the $N_2$ integrand in the ends analysis; it is consumed by `nu_grid_bound_raw`, the quantitative off-window bound feeding [lem:ends] (module `Zeta23.PrimeSideA.EndsNu`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L571-L601

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsNu

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.integrableOn_sigma_mul_abs_nuX (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hT : 1 ≤ p.T) :
    IntegrableOn (fun τ : ℝ =>
      (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|) (p.I)ᶜ := by sorry
