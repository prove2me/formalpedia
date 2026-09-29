-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_dom_left
-- name    : Zeta23.PrimeSide.dom_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:14:54.385054+00:00
-- url     : https://prove2.me/theorems/b9d0b372-0f63-4809-94fa-5f329eac67c1
-- title:
--   Half-line domination left of the window: $\sigma(\tau)\,|\nu(\tau)| \le M_{\mathrm{tot}}(T - \tau)$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. Write $\sigma(\tau) = \sum_{0 \le k < d} \psi(\tau - \tau_k)$ for the grid sum of the taper majorant $\psi(r) = \min(L, 2/|r|, c_\varrho/(wr^2))$ [eq:psidef], and let $\nu$ satisfy `NuBound` ($|\nu(\tau)| \le B + \log^+(|\tau|/4T)$, [eq:Bdef]). The half-line majorant $M_{\mathrm{tot}}(\Delta)$ (as a function of the distance $\Delta$ to the window) is defined piecewise: for $0 < \Delta \le 2T$ it is $B\bigl(\psi(\Delta) + \tfrac{L}{2\pi}\min(\int_0^\infty \psi,\, c_\varrho/(w\Delta))\bigr)$ (the near regime), and for $\Delta > 2T$ it is $d\, \tfrac{c_\varrho}{w \Delta^2}\bigl(B + 2\sqrt{\Delta/T}\bigr)$ (the far regime, where the $\log^+$ growth of $\nu$ is absorbed by a square root). The theorem asserts: assuming `LocalHypsCoreW`, `NuBound`, and $T > 0$, for every $\tau < T$,
--   $$\Bigl(\sum_{0 \le k < d} \psi(\tau - \tau_k)\Bigr)\, |\nu(\tau)| \;\le\; M_{\mathrm{tot}}(T - \tau),$$
--   i.e. to the left of $I = [T, 2T]$ the weighted density is dominated by the one-variable majorant evaluated at the distance $T - \tau$ to the window.
--
--   Together with its mirror `dom_right`, it reduces the two-dimensional off-square tail estimates of the ends analysis to one-dimensional integrals of $M_{\mathrm{tot}}$; it is consumed by `integrableOn_sigma_mul_abs_nuX` and `nu_grid_bound_raw` in module `Zeta23.PrimeSideA.EndsNu` (part of [lem:ends]).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L346-L365

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

theorem Zeta23.PrimeSide.dom_left (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 0 < p.T) {τ : ℝ} (hτ : τ < p.T) :
    (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ Mtot cϱ p B (p.T - τ) := by sorry
