-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_isLocalHomeomorph_projection
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:36:51.673112+00:00
-- url     : https://prove2.me/submissions/76a723da-d480-4aa8-9a4d-06b7cc10e934

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitBase_isOpen
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitDomain_isOpen
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
/-- The initial point belongs to the slit when it lies in the unit disc. -/
theorem bottleneckSlit_self (v : ℂ) (hv : ‖v‖ < 1) :
    v ∈ bottleneckSlit v := by
  refine ⟨0, le_rfl, by linarith, ?_⟩
  simp
/-- The polynomial derivative does not vanish on the slit-complement domain. -/
theorem bottleneck_regular_on_slitDomain (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (z : bottleneckSlitDomain p cc) :
    (Polynomial.derivative p).eval (z : ℂ) ≠ 0 := by
  intro hzero
  have heq : (z : ℂ) = cc := huniq z z.2.1 hzero
  apply z.2.2
  rw [heq]
  exact bottleneckSlit_self (p.eval cc) hcc
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) (hv : p.eval cc ≠ 0)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc) :
    IsLocalHomeomorph (bottleneckSlitProjection p cc) := by
  have hderiv : ∀ u ∈ bottleneckSlitDomain p cc,
      (Polynomial.derivative p).eval u ≠ 0 := by
    intro u hu
    exact bottleneck_regular_on_slitDomain p cc hcc huniq ⟨u, hu⟩
  have hpLocal : IsLocalHomeomorphOn p.eval (bottleneckSlitDomain p cc) := by
    intro u hu
    have hd := (p.hasStrictDerivAt u).hasStrictFDerivAt_equiv (hderiv u hu)
    exact ⟨hd.toOpenPartialHomeomorph p.eval,
      hd.mem_toOpenPartialHomeomorph_source, rfl⟩
  have hDomInc : IsLocalHomeomorph
      (Subtype.val : bottleneckSlitDomain p cc → ℂ) :=
    (bottleneckSlitDomain_isOpen p cc hv).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hscalar : IsLocalHomeomorph
      (fun z : bottleneckSlitDomain p cc => p.eval (z : ℂ)) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hpLocal.comp hDomInc.isLocalHomeomorphOn (fun z _ => z.property))
  have hBaseInc : IsLocalHomeomorph
      (Subtype.val : bottleneckSlitBase (p.eval cc) → ℂ) :=
    (bottleneckSlitBase_isOpen (p.eval cc) hv).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcont : Continuous (bottleneckSlitProjection p cc) :=
    (p.continuous.comp continuous_subtype_val).subtype_mk _
  exact hscalar.of_comp hBaseInc hcont
