-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_uniform_positive_coordinate_bounds
-- name    : ReweightedNPMLE.exists_uniform_positive_coordinate_bounds
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:37.056023+00:00
-- url     : https://prove2.me/theorems/bd5fc533-2aa1-463d-a452-41420d737a8b
-- title:
--   Uniform positive coordinate bounds on a compact subset of the positive orthant
-- statement:
--   Let $C$ be a compact subset of the strictly positive orthant in $\mathbb R^n$. There exist constants $c,B>0$, depending only on $C$, such that
--   $$
--   c\le v_i\le B
--   \qquad\text{for every }v\in C\text{ and every coordinate }i.
--   $$
--   Nonemptiness of $C$ is not required, and the finite-dimensional statement also permits a zero-dimensional ambient space.
--
--   The conclusion provides a common distance from the logarithmic coordinate singularities and a common upper bound. These constants turn compact positive fitted-value geometry into the uniform hypotheses needed for explicit Lipschitz and envelope estimates.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L336-L357

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.exists_uniform_positive_coordinate_bounds {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCcompact : IsCompact C)
    (hCpos : C ⊆ positiveVectors n) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ ∀ v ∈ C, ∀ i, c ≤ v i ∧ v i ≤ B := by sorry
