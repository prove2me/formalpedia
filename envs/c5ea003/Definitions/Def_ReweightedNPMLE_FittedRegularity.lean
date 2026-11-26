-- Prove2me | Definitions.Def_ReweightedNPMLE_FittedRegularity
-- name    : ReweightedNPMLE_FittedRegularity
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:18:02.624802+00:00
-- url     : https://prove2.me/theorems/a64b0a7b-cff0-5359-bd5c-41a3315859cc
-- title:
--   Canonical fitted values, fitted logs, and their displacement
-- statement:
--   Let \(C\subseteq\mathbb R_{++}^n\) be nonempty and compact. For every real weight vector \(w\), choose a maximizer
--   \[
--   \widehat v_C(w)\in\operatorname*{arg\,max}_{v\in C}\sum_iw_i\log v_i,
--   \qquad
--   \widehat z_C(w)_i=\log\widehat v_C(w)_i.
--   \]
--   Existence makes these selections defined for all weights; convexity of \(C\) and strictly positive weights are additional hypotheses used to establish uniqueness. For a reference vector \(z_0\), define the extended log displacement
--   \[
--   g(w)=
--   \begin{cases}
--   \widehat z_C(w)-z_0,&w\in\mathbb R_{++}^n,\\
--   0,&\text{otherwise}.
--   \end{cases}
--   \]
--   The extension allows global measurable formulations while retaining the fitted-log displacement on the positive orthant.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L21-L455

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

namespace ReweightedNPMLE

/-- A canonical fitted-value maximizer over a nonempty compact positive set.
For positive weights it is the unique fitted vector, but the definition is
available for all weights because existence only uses compactness. -/
noncomputable def fittedValueSelection {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) : Fin n → ℝ :=
  Classical.choose (exists_fittedValue_maximizer hCcompact hCnonempty hCpos w)



/-- Coordinatewise logarithm of the canonical fitted vector. -/
noncomputable def fittedLogSelection {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ Real.log (fittedValueSelection C hCcompact hCnonempty hCpos w i)



























/-- The canonical fitted-log displacement, extended by zero outside the
positive orthant so that it is globally measurable. -/
noncomputable def fittedLogDisplacement {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (z₀ : Fin n → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) := by
  classical
  exact (positiveVectors n).piecewise
    (fun w ↦ fittedLogSelection C hCcompact hCnonempty hCpos w - z₀) (fun _ ↦ 0)









end ReweightedNPMLE


