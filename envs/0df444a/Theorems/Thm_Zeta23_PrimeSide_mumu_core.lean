-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_mumu_core
-- name    : Zeta23.PrimeSide.mumu_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:22:46.515481+00:00
-- url     : https://prove2.me/theorems/d5b530cd-6614-4a1f-a331-0a2af26ed0c4
-- title:
--   Core estimate of [prop:mumu]: $\mathcal{M}[\mu,\mu] = 2\pi b L\int_T^{2T}\mu^2 + $ explicit error
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $l=\log(T/2\pi)$, $L=\lambda l$, window $I=[T,2T]$, and taper data $F$ with core hypotheses `LocalHypsCore` (in particular $\int\Phi^2=2\pi bL$). Let $\mu$ be the archimedean density [eq:mudef], and let $\mathcal{M}[\mu,\mu]:=\iint_{I\times I}\Phi(\tau-\tau')^2\mu(\tau)\mu(\tau')\,d\tau\,d\tau'$ be the diagonal $\mu$-block of the seam form.
--
--   Assume H-$\Gamma$, $T\ge 2$, the window bound $|\mu(\tau)|\le l$ on $I$, and an increment constant $K\ge 0$ with $|\mu(t+r)-\mu(t)|\le(K|r|+10r^2)/t$ for $t\ge 2$. Then
--   $$\Bigl|\mathcal{M}[\mu,\mu]-2\pi b L\int_T^{2T}\mu(\tau)^2\,d\tau\Bigr|\ \le\ (1+K)\,l^2\int_{\mathbb{R}}\Phi(x)^2|x|\,dx\ +\ 10\,l\int_{\mathbb{R}}\Phi(x)^2x^2\,dx.$$
--   With $\int\Phi^2|x|\ll\log L$ and $\int\Phi^2x^2=O(1)$ [eq:psiints] this is the paper's $\mathcal{M}[\mu,\mu]=2\pi bL\int_T^{2T}\mu^2+O(l^2\log L)$ (§5.4). The proof shears $\tau=\tau'+x$, replaces $\mu(x+\tau')$ by $\mu(\tau')$ via the increment bound, and completes the truncated window $I\cap(I-x)$ to $I$.
--
--   In module `Zeta23.PrimeSideA.MuMu` this is the entire analytic content of [prop:mumu]; its consumer `prop_mumu` packages it in the uniform for-large-$T$ form used by [thm:traces].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/MuMu.lean#L159-L212, docstring tag [prop:mumu]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ}
variable {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.mumu_core (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (hT2 : 2 ≤ p.T)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t) :
    |Mform F.Phi p.T Zeta23.mu Zeta23.mu
        - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2|
      ≤ (1 + K) * p.l ^ 2 * (∫ x, F.Phi x ^ 2 * |x|)
        + 10 * p.l * ∫ x, F.Phi x ^ 2 * x ^ 2 := by sorry
