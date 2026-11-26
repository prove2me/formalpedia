-- Prove2me | Definitions.Def_ReweightedNPMLE_GaussianWidth
-- name    : ReweightedNPMLE_GaussianWidth
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:22:58.489206+00:00
-- url     : https://prove2.me/theorems/1aec63b6-bafc-5673-85ed-2a61e8af345f
-- title:
--   The Gaussian Taylor subspace and relative-atom approximants
-- statement:
--   For observations \(x_i\in\mathbb R^d\) and order \(L\), choose coefficients \(c_{i,m}\) satisfying
--   \[
--   \sum_{\ell=0}^L\frac{\langle x_i,\theta\rangle^\ell}{\ell!}
--   =\sum_m c_{i,m}\theta^m
--   \]
--   over the monomials of total degree at most \(L\). For a reference fitted vector \(v_0\), let \(g_m\in\mathbb R^n\) have coordinates \(g_{m,i}=c_{i,m}/v_{0,i}\). Define
--   \[
--   V_L=\operatorname{span}\bigl(\{\mathbf1\}\cup\{g_m\}_m\bigr),\qquad
--   a(\theta)_i=\frac{e^{\langle x_i,\theta\rangle-\|\theta\|^2/2}}{v_{0,i}}-1.
--   \]
--   The Taylor approximant to the relative atom is
--   \[
--   \widetilde a_L(\theta)
--   =e^{-\|\theta\|^2/2}\sum_m\theta^m g_m-\mathbf1\in V_L.
--   \]
--   The separate constant generator ensures that subtraction of the reference vector remains inside the approximation subspace. The construction is used with positive \(v_0\).
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianWidth.lean#L76-L139

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
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

namespace ReweightedNPMLE







/-! ## The concrete Gaussian Taylor subspace -/

/-- Chosen monomial coefficients for the Taylor polynomial of
`exp ⟪xᵢ, θ⟫`. -/
noncomputable def truncatedInnerCoeff {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (i : Fin n) : MonomialCoord d L → ℝ :=
  Classical.choose (truncatedInnerExp_isPointMonomialCombination L (x i))



/-- Generators of the paper's Gaussian approximation space.  `none` is the
constant vector and `some m` is the normalized coefficient vector of the
monomial `m`. -/
noncomputable def gaussianWidthGenerator {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) :
    Option (MonomialCoord d L) → EuclideanSpace ℝ (Fin n)
  | none => WithLp.toLp 2 (fun _ ↦ 1)
  | some m => WithLp.toLp 2 (fun i ↦ truncatedInnerCoeff L x i m / v₀ i)

/-- The explicit Taylor subspace used in the Gaussian relative-width proof. -/
noncomputable def gaussianTaylorSubspace {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range (gaussianWidthGenerator L x v₀))





/-- Relative Gaussian atom after cancelling the common centered density. -/
noncomputable def relativeGaussianAtom {d n : ℕ}
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ Real.exp (gaussianScore (x i) θ) / v₀ i - 1)

/-- Taylor approximant to one relative Gaussian atom. -/
noncomputable def gaussianTaylorApproximant {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) :
    EuclideanSpace ℝ (Fin n) :=
  (∑ m : MonomialCoord d L,
      (Real.exp (-‖θ‖ ^ 2 / 2) * pointMonomialEval θ m) •
        gaussianWidthGenerator L x v₀ (some m)) -
    gaussianWidthGenerator L x v₀ none













end ReweightedNPMLE


