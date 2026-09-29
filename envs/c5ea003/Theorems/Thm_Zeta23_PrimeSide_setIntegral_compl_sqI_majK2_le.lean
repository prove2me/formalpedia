-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_setIntegral_compl_sqI_majK2_le
-- name    : Zeta23.PrimeSide.setIntegral_compl_sqI_majK2_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:19:45.87745+00:00
-- url     : https://prove2.me/theorems/1f8ba808-e754-4aa2-bad5-a89d750597f1
-- title:
--   Fubini core of the $\mathcal{E}_2$ majorant bound: $\iint_{(I\times I)^c} \mathrm{maj}K_2 \le 2 L^2 M_1 M_2$
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef].
--
--   $\psi(r) := \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ is the taper majorant [eq:psidef], with the explicit value $\psi(0) = L$ guarding Lean's convention $2/0 = 0$; $c_\varrho \ge 4$ is the profile constant of [eq:phinorms]. The $\mathcal{E}_2$ majorant kernel with its $\nu$-weights is
--   $$\mathrm{maj}K_2(\tau, \tau') := L^2 \Bigl(\sum_{k < d} \psi(\tau - \tau_k)\, \psi(\tau' - \tau_k)\Bigr)\, |\nu(\tau)|\, |\nu(\tau')|,$$
--   and `NuBound` $p\ B\ \nu$ means $|\nu(\tau)| \le B + \log^+(|\tau|/4T)$ for all $\tau$ [eq:Bdef].
--
--   **Statement.** Let $\nu$ be continuous, assume the weak core hypotheses `LocalHypsCoreW`, `NuBound` with $B \ge 1$, and $T \ge 1$. Suppose $M_1 \ge 0$ and the two one-dimensional estimates hold:
--   $$\int_{\mathbb{R}} \psi(\tau - a)\, |\nu(\tau)|\, d\tau \le M_1 \ \ \text{for every } a \in [T, 2T], \qquad \int_{I^c} \Bigl(\sum_{k<d} \psi(\tau - \tau_k)\Bigr) |\nu(\tau)|\, d\tau \le M_2.$$
--   Then
--   $$\iint_{(I \times I)^c} \mathrm{maj}K_2 \le 2\, L^2\, M_1\, M_2.$$
--   The proof is the Fubini argument of §5.3: $(I \times I)^c \subseteq (I^c \times \mathbb{R}) \cup (\mathbb{R} \times I^c)$, and each piece is an iterated integral bounded by $L^2 M_1 M_2$.
--
--   **Role.** Reduces the two-dimensional off-window error $\mathcal{E}_2$ of [lem:ends] to the two abstracted 1-D estimates; consumed by `Zeta23.PrimeSide.calE2_maj_bound` in the proof that $\operatorname{tr}\tilde{G}^2 = \mathcal{M} + O(L\, l \log l\, (l^2 + X))$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE2.lean#L98-L255

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

theorem Zeta23.PrimeSide.setIntegral_compl_sqI_majK2_le (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hB1 : 1 ≤ B) (hT1 : 1 ≤ p.T) {M1 M2 : ℝ} (hM1nn : 0 ≤ M1)
    (hN1 : ∀ a ∈ Icc p.T (2 * p.T), ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ| ≤ M1)
    (hN2 : ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ| ≤ M2) :
    ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q ≤ 2 * (p.L ^ 2 * M1 * M2) := by sorry
