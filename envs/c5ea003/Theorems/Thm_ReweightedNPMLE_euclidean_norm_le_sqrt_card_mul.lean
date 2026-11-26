-- Prove2me | Theorems.Thm_ReweightedNPMLE_euclidean_norm_le_sqrt_card_mul
-- name    : ReweightedNPMLE.euclidean_norm_le_sqrt_card_mul
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:45:42.418723+00:00
-- url     : https://prove2.me/theorems/e1b7f23e-0c02-469f-a304-75622f051768
-- title:
--   Euclidean norm from a uniform coordinate bound
-- statement:
--   For $x\in\mathbb R^n$ and $\varepsilon\ge0$, if $|x_i|\le\varepsilon$ for every coordinate, then $$\|x\|_2\le\sqrt n\,\varepsilon.$$ The statement includes $n=0$. It converts coordinatewise Taylor errors into a Euclidean residual bound.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianWidth.lean#L22-L39

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

theorem ReweightedNPMLE.euclidean_norm_le_sqrt_card_mul {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    {eps : ℝ} (heps : 0 ≤ eps) (hx : ∀ i, |x i| ≤ eps) :
    ‖x‖ ≤ Real.sqrt n * eps := by sorry
