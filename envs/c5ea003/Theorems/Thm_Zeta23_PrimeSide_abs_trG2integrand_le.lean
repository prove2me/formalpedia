-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_trG2integrand_le
-- name    : Zeta23.PrimeSide.abs_trG2integrand_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:14:08.779875+00:00
-- url     : https://prove2.me/theorems/96ffe4c4-109e-4646-8d02-8eecea5fa106
-- title:
--   Pointwise $\psi$-majorization of $K^2 \nu \nu'$ [eq:Kbounds]
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The kernels are $K(\tau,\tau') = \sum_{0 \le k < d} \hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau'-\tau_k)$ [eq:Kdef] and its full-lattice completion $K_\infty(\tau,\tau') = L\,\Phi(\tau-\tau')$ (the value of the sum over all $k \in \mathbb{Z}$, by Poisson summation [lem:poisson]). Let $\psi(r) = \min\bigl(L,\, 2/|r|,\, c_\varrho/(w r^2)\bigr)$ (with $\psi(0) = L$) be the taper majorant of [eq:psidef], and let $\nu : \mathbb{R} \to \mathbb{R}$ be an arbitrary density. The theorem asserts, for every $q = (\tau, \tau') \in \mathbb{R}^2$,
--   $$\bigl|K(\tau,\tau')^2\, \nu(\tau)\, \nu(\tau')\bigr| \;\le\; L^2 \Bigl(\sum_{0 \le k < d} \psi(\tau - \tau_k)\, \psi(\tau' - \tau_k)\Bigr)\, |\nu(\tau)|\, |\nu(\tau')|.$$
--   The proof combines the uniform bound $|K| \le L^2$ (`abs_Kfun_le`, one factor of $K$) with the termwise majorization $|\hat\varphi| \le \psi$ (the other factor); the right-hand side is exactly the $\mathcal{E}_2$ majorant kernel $\mathrm{majK2}$.
--
--   Integrated over the complement of $I \times I$, this is the pointwise input to the off-square error bound $\mathcal{E}_2$ in `lem_ends_nu_W`, the ends lemma [lem:ends] of the prime side (module `Zeta23.PrimeSideA.EndsE2`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE2.lean#L27-L49, docstring tag [eq:Kbounds]

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
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.abs_trG2integrand_le (hF : LocalHypsCoreW cϱ p F) (q : ℝ × ℝ) :
    |trG2integrand p F ν q| ≤ p.L ^ 2 *
      (∑ k ∈ Finset.range p.d, psiA cϱ p (q.1 - p.tau k) * psiA cϱ p (q.2 - p.tau k))
      * (|ν q.1| * |ν q.2|) := by sorry
