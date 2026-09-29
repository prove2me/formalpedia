-- Prove2me | solution 1 for Erdos1041.Counterexample.s3_bottleneck_isCoveringMap
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:43:42.999325+00:00
-- url     : https://prove2.me/submissions/daa5464f-c787-4246-a3d6-9de62b913543

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_isClosedEmbedding_slitDomain
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_isLocalHomeomorph_projection
import Theorems.Thm_Erdos1041_Counterexample_s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section
open Topology

namespace Erdos1041.Counterexample
/-- The restriction of `p` to the slit complement is a proper map. -/
theorem bottleneck_isProperMap_projection (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) (hdeg : 0 < p.natDegree) :
    IsProperMap (bottleneckSlitProjection p cc) := by
  have hpdegree : 0 < p.degree := by
    apply lt_of_not_ge
    intro hle
    exact (not_le_of_gt hdeg) (Polynomial.natDegree_le_of_degree_le hle)
  have hglobal : IsProperMap p.eval := p.isProperMap_eval hpdegree
  exact (hglobal.restrictPreimage (bottleneckSlitBase (p.eval cc))).comp
    (bottleneck_isClosedEmbedding_slitDomain p cc hcc).isProperMap
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) (hv : p.eval cc ≠ 0) (hdeg : 0 < p.natDegree)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc) :
    IsCoveringMap (bottleneckSlitProjection p cc) :=
  s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    (bottleneck_isProperMap_projection p cc hcc hdeg)
    (bottleneck_isLocalHomeomorph_projection p cc hcc hv huniq)
