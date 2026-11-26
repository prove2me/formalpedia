-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianTaylorApproximant_apply
-- name    : ReweightedNPMLE.gaussianTaylorApproximant_apply
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:12.004785+00:00
-- url     : https://prove2.me/theorems/bc6b36bf-4f0f-47aa-a94f-1e6fa6ea164c
-- title:
--   Coordinate formula for the Gaussian Taylor approximant
-- statement:
--   For observations $x_1,\ldots,x_n\in\mathbb R^d$ and reference coordinates $v_{0i}$, define $a_i(\theta)=e^{\langle x_i,\theta\rangle-\|\theta\|^2/2}/v_{0i}-1$. For every integer $L\ge0$, location $\theta\in\mathbb R^d$, and coordinate $i$, the approximant defined through monomial coefficient vectors satisfies $$T_L(\theta)_i=\frac{e^{-\|\theta\|^2/2}}{v_{0i}}\sum_{\ell=0}^L\frac{\langle x_i,\theta\rangle^\ell}{\ell!}-1.$$ No positivity hypothesis on $v_0$ is needed for this algebraic identity; division follows Lean’s total field convention. This identifies the coefficient-space construction with the ordinary exponential Taylor polynomial.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianWidth.lean#L152-L179

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

open ReweightedNPMLE







/-! ## The concrete Gaussian Taylor subspace -/

theorem ReweightedNPMLE.gaussianTaylorApproximant_apply {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) (i : Fin n) :
    gaussianTaylorApproximant L x v₀ θ i =
      Real.exp (-‖θ‖ ^ 2 / 2) *
          (∑ ell ∈ Finset.range (L + 1),
            (inner ℝ (x i) θ) ^ ell / ell.factorial) / v₀ i - 1 := by sorry
