-- Prove2me | Theorems.Thm_ReweightedNPMLE_relativeDictionary_weighted_sum_eq_zero_of_contact
-- name    : ReweightedNPMLE.relativeDictionary_weighted_sum_eq_zero_of_contact
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:38:53.068804+00:00
-- url     : https://prove2.me/theorems/dde81884-138f-48b9-9c70-fb7bc5154581
-- title:
--   Contact identities annihilate mass-preserving relative directions
-- statement:
--   Let $A_1,\ldots,A_k\in\mathbb R^n$ and $v,w\in\mathbb R^n$. Suppose $\sum_iw_iA_{ji}/v_i=\sum_iw_i$ for each $j$. For every coefficient vector $c$ with $\sum_jc_j=0$, define $u_i=\sum_jc_jA_{ji}/v_i$. Then $$\sum_iw_iu_i=0.$$ No positivity or nonzero-coordinate hypothesis is needed for this algebraic implication, using total field division. It cancels the first-order fitted-value term in sensitivity expansions.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivity.lean#L121-L152

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

open ReweightedNPMLE

theorem ReweightedNPMLE.relativeDictionary_weighted_sum_eq_zero_of_contact {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ)
    (hcontact : ∀ j, ∑ i, w i * (A j i / v i) = total w)
    (c : zeroSumCoefficients k) :
    ∑ i, w i * relativeDictionaryMap A v c i = 0 := by sorry
