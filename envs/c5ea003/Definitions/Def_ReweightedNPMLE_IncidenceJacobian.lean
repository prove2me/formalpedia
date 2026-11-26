-- Prove2me | Definitions.Def_ReweightedNPMLE_IncidenceJacobian
-- name    : ReweightedNPMLE_IncidenceJacobian
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:25:04.993936+00:00
-- url     : https://prove2.me/theorems/665802cf-8879-407a-b698-0f9bad69a37f
-- title:
--   Separated incidence equations and their assembled derivative
-- statement:
--   Let \(E,Y\) be real normed spaces and let \(H_i:E\times Y\to\mathbb R\), \(i=1,\ldots,n\), be scalar families sharing a parameter \(\eta\in E\). For \(p=(\eta,y_1,\ldots,y_n)\), define the row projection \(\pi_i(p)=(\eta,y_i)\) and the incidence map
--   \[
--   \mathcal H(p)=(H_i(\eta,y_i))_{i=1}^n.
--   \]
--   The assembled continuous linear map has \(i\)-th component
--   \[
--   v\longmapsto D H_i(\eta,y_i)[\pi_i(v)].
--   \]
--   Thus each equation depends on the common parameter and a single observation row. This expression is defined using the Fréchet derivative of each scalar family; when those families are differentiable, it is the derivative of the incidence map.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/IncidenceJacobian.lean#L18-L35

import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Full row rank of separated incidence equations

Each scalar equation depends on the common parameter and one observation row.
Nonzero selected observation derivatives give an explicit right inverse for
the full incidence derivative, without constraining the parameter derivative.
-/

open Set Filter
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def incidenceRowProjection {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ} (i : Fin n) :
    (E × (Fin n → Y)) →L[ℝ] E × Y :=
  (ContinuousLinearMap.fst ℝ E (Fin n → Y)).prod
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ E (Fin n → Y)))

noncomputable def incidenceEquations {E Y : Type*} {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y)) : Fin n → ℝ :=
  fun i ↦ H i p.1 (p.2 i)

noncomputable def incidenceDerivative {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y)) :
    (E × (Fin n → Y)) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦
    (fderiv ℝ (Function.uncurry (H i)) (p.1, p.2 i)).comp (incidenceRowProjection i))











end ReweightedNPMLE


