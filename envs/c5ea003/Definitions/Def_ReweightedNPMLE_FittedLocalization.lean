-- Prove2me | Definitions.Def_ReweightedNPMLE_FittedLocalization
-- name    : ReweightedNPMLE_FittedLocalization
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:23:01.99078+00:00
-- url     : https://prove2.me/theorems/48650b65-c0ae-54bc-ae58-a694da9b1ca9
-- title:
--   Relative fitted values and coordinatewise log ratios
-- statement:
--   Given a reference fitted vector \(v_0\) and another fitted vector \(v\), define
--   \[
--   u(v_0,v)_i=\frac{v_i}{v_{0,i}}-1,\qquad
--   z(v_0,v)_i=\log v_i-\log v_{0,i}.
--   \]
--   For a feasible set \(C\subseteq\mathbb R^n\), its relative fitted set is the image \(U(C,v_0)=\{u(v_0,v):v\in C\}\). On positive fitted vectors, \(1+u_i>0\), \(z_i=\log(1+u_i)\), and
--   \(\ell_w(v)-\ell_w(v_0)=\sum_iw_i z_i\).
--   Thus relative deviations used in localization correspond directly to log-likelihood differences. When \(v_0\in C\), the relative set contains zero.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedLocalization.lean#L17-L24

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
# Likelihood-facing radial localization

Relative feasible fitted vectors and their log-ratios translate the radial
localization inequalities into ordinary likelihood loss and fitted-log
error.  The theorem applies simultaneously to every near-optimal fit.
-/

open Set Filter MeasureTheory Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def relativeFittedVector {n : ℕ} (v₀ v : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ v i / v₀ i - 1

def relativeFittedSet {n : ℕ} (C : Set (Fin n → ℝ)) (v₀ : Fin n → ℝ) :
    Set (Fin n → ℝ) := relativeFittedVector v₀ '' C

noncomputable def fittedLogRatio {n : ℕ} (v₀ v : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ Real.log (v i) - Real.log (v₀ i)















end ReweightedNPMLE


