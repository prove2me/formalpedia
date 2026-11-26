-- Prove2me | Theorems.Thm_ReweightedNPMLE_eventually_mem_finiteSimplex_add_smul_zeroSum
-- name    : ReweightedNPMLE.eventually_mem_finiteSimplex_add_smul_zeroSum
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:38:38.010505+00:00
-- url     : https://prove2.me/theorems/f5641380-3f0b-57e6-8b86-6482af7ab83d
-- title:
--   Small mass-preserving perturbations remain in the simplex
-- statement:
--   Let $p\in\mathbb R^k$ have strictly positive coordinates and $\sum_jp_j=1$, and let $c\in\mathbb R^k$ satisfy $\sum_jc_j=0$. Then $$p+tc\in\Delta_{k-1}\quad\text{for all sufficiently small }|t|.$$ The neighborhood is two-sided. This supplies feasible active-support perturbations for the likelihood expansion.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivityAnalytic.lean#L97-L119

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.eventually_mem_finiteSimplex_add_smul_zeroSum
    {k : ℕ} (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k)
    (hpfull : ∀ j, 0 < p j) (c : zeroSumCoefficients k) :
    ∀ᶠ t : ℝ in nhds 0, p + t • c.1 ∈ finiteSimplex k := by sorry
