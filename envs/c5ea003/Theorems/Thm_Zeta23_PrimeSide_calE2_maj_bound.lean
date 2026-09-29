-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_calE2_maj_bound
-- name    : Zeta23.PrimeSide.calE2_maj_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:20:01.270558+00:00
-- url     : https://prove2.me/theorems/af0b1c59-9cd3-424c-a1a6-8f2042430bb2
-- title:
--   The $\mathcal{E}_2$ majorant integral is $O(L^3 B^2\, l \log l)$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The off-square majorant kernel is
--   $$\mathrm{majK2}(\tau,\tau') \;=\; L^2 \Bigl(\sum_{0 \le k < d} \psi(\tau - \tau_k)\, \psi(\tau' - \tau_k)\Bigr)\, |\nu(\tau)|\, |\nu(\tau')|,$$
--   where $\psi(r) = \min(L, 2/|r|, c_\varrho/(wr^2))$ is the taper majorant [eq:psidef]. Fix the profile constant $c_\varrho$ and the bandwidth ratio $\lambda$. The theorem asserts the existence of constants $C$ and $T_0$ such that for every setting $p$ with $p.\mathrm{lam} = \lambda$ and $T \ge T_0$, every taper datum $F$ satisfying `LocalHypsCoreW`, and every continuous density $\nu$ with `NuBound` ($|\nu(\tau)| \le B + \log^+(|\tau|/4T)$), provided also $L \le 2l$ and $l \le B$,
--   $$\iint_{(I \times I)^{\mathsf{c}}} \mathrm{majK2}(\tau, \tau')\, d\tau\, d\tau' \;\le\; C\, L^3\, B^2\, l\, \log l.$$
--   This is the Section 5.3 bound for $\mathcal{E}_2$: the $\nu$-dependence sits in a nonnegative bilinear kernel, so the Cauchy–Schwarz step (in the character-family application) can be pushed inside this single majorant estimate; the $\log l$ arises from the $2/|r|$ regime of $\psi$.
--
--   It disposes of the off-square error $\mathcal{E}_2$ in `lem_ends_nu_W`, the $\nu$-generic ends lemma [lem:ends] of the prime side (module `Zeta23.PrimeSideA.EndsE2`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE2.lean#L263-L349

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
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.calE2_maj_bound :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q ≤ C * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by sorry
