-- Prove2me | solution 1 for Erdos1041.Counterexample.erdos1041_counterexample_hausdorff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T01:30:30.473438+00:00
-- url     : https://prove2.me/submissions/51f9f78f-39aa-4847-b81e-68f557b58105

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_HausdorffLength
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_barrier_excludes
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_epsilon_pos
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_rational_margin
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_sqrt_le_scaled
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_u_six
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_u_three
import Theorems.Thm_Erdos1041_Counterexample_s2_two_zeros_gives_critical_point
import Theorems.Thm_Erdos1041_Counterexample_s4_f_monic_degree
import Theorems.Thm_Erdos1041_Counterexample_s4_instance_critical
import Theorems.Thm_Erdos1041_Counterexample_s5_roots_connected_to_critical
import Theorems.Thm_Erdos1041_Counterexample_s7_barriers
import Theorems.Thm_Erdos1041_Counterexample_s3_bottleneck_hausdorff
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026. -/

/-!
# Erdős #1041 with length as one-dimensional Hausdorff measure

Formal Conjectures states Erdős #1041 with the length of a path defined as the
one-dimensional Hausdorff measure `μH[1]` of its image. `erdos1041_counterexample`
bounds the total variation of a parametrisation instead. This module proves the
Hausdorff form for the same polynomial `f`, and in a stronger shape: every
preconnected subset of the strict lemniscate `Ω(f)` that contains two distinct
roots has one-dimensional Hausdorff measure greater than two
(`erdos1041_counterexample_hausdorff`). The image of any path joining two roots
is such a set.

The argument reuses the bottleneck geometry of `Bottleneck.lean` and adds no
arc-extraction, rectifiability or length-of-arc lemma. Removing the slit
preimage from the component of `Ω(f)` through the critical point leaves an open
set in which no preconnected subset contains both roots, because the polynomial
restricted there is a covering of a simply connected base. So a preconnected
set `K` through both roots must, for every radius between the slit preimage and
a root, meet the circle of that radius about the critical point inside the
connected component of that root (`bottleneck_sheet_crossing`). The two
components are disjoint open sets, the distance to the critical point is
1-Lipschitz, and on the real line `μH[1]` is Lebesgue measure, so `μH[1] K` is at
least the sum of the two radial lengths (`s3_bottleneck_hausdorff`). That is the
same bound `s3_bottleneck_length` gives for total variation, so the numerical
margin of `Assembly.lean` applies unchanged.

`erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false` state the
Formal Conjectures parent `Erdos1041.erdos_1041` in its own vocabulary, with
`fcLength` its `length`, and refute it.

The mathematics of the counterexample is ani's. The polynomial is the single
member `s = 10⁻⁶` of ani's family fixed in `Defs.lean`.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Polynomial Metric

namespace Erdos1041.Counterexample
/-! ## The slit domain separates the two roots -/





/-! ## Crossing every circle inside each sheet -/



/-! ## From radial crossings to Hausdorff measure -/





/-! ## The instance `f` -/
end Erdos1041.Counterexample

open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K := by
  obtain ⟨zs, b₃, b₆, aHat, h, hzs_mem, hzs_crit, -, hzs_uniq,
      hv_pos, hδ_pos, hδ_le, haHat, hh, haHat_lo, hdisk, hδ_small,
      hzs_near, hb₃_root, hb₆_root, hb_ne, hb₃_near, hb₆_near,
      hroot_near, hb₃_uniq, hb₆_uniq, hproj⟩ := s4_instance_critical
  obtain ⟨g₁, g₂, hg₁cont, hg₂cont, hg₁zero, hg₂zero,
      hg₁zs, hg₂zs, hg₁pos, hg₂pos⟩ := s7_barriers zs hzs_near
  have hzeros : ∀ w ∈ connectedComponentIn (Omega f) zs,
      f.IsRoot w → w = b₃ ∨ w = b₆ := by
    intro w hw hwroot
    obtain ⟨j, hnear⟩ := hroot_near w hwroot
    by_cases hj3 : j.val = 3
    · left
      apply hb₃_uniq w hwroot
      simpa only [hj3, AssemblyAux.u_three] using hnear
    by_cases hj6 : j.val = 6
    · right
      apply hb₆_uniq w hwroot
      simpa only [hj6, AssemblyAux.u_six] using hnear
    have hjlt : j.val < 7 := j.isLt
    have hjother : (j.val = 0 ∨ j.val = 1 ∨ j.val = 2) ∨
        (j.val = 4 ∨ j.val = 5) := by omega
    rcases hjother with hjleft | hjright
    · exact False.elim
        (AssemblyAux.barrier_excludes f zs w hzs_mem hw g₁
          hg₁cont hg₁zero hg₁zs (hg₁pos j hjleft w hnear))
    · exact False.elim
        (AssemblyAux.barrier_excludes f zs w hzs_mem hw g₂
          hg₂cont hg₂zero hg₂zs (hg₂pos j hjright w hnear))
  obtain ⟨hb₃_mem, hb₆_mem⟩ :=
    s5_roots_connected_to_critical zs b₃ b₆ hzs_mem hzs_crit hb₃_root hb₆_root
      hb₃_near hb₆_near
  have huniq : ∀ c' ∈ connectedComponentIn (Omega f) zs,
      (Polynomial.derivative f).IsRoot c' → c' = zs := by
    intro c' hc' hcrit
    exact hzs_uniq c' (connectedComponentIn_subset (Omega f) zs hc') hcrit
  have hv : f.eval zs ≠ 0 := norm_pos_iff.mp hv_pos
  have hsqrt : Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) ≤
      (ρ : ℝ) * (ε : ℝ) / 5000 :=
    AssemblyAux.sqrt_le_scaled AssemblyAux.rho_pos AssemblyAux.epsilon_pos
      hδ_le haHat_lo
  have hloss : (8 / 3 : ℝ) * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) ≤
      8 / 3 * ((ρ : ℝ) * (ε : ℝ) / 5000) :=
    mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have hreal : (2 : ℝ) < ‖b₃ - zs‖ + ‖b₆ - zs‖ -
      8 / 3 * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) :=
    lt_of_lt_of_le AssemblyAux.rational_margin (sub_le_sub hproj hloss)
  have henn : (2 : ℝ≥0∞) < ENNReal.ofReal (‖b₃ - zs‖ + ‖b₆ - zs‖ -
      8 / 3 * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖)) := by
    have hpositive : 0 < ‖b₃ - zs‖ + ‖b₆ - zs‖ -
        8 / 3 * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) :=
      lt_trans (by norm_num) hreal
    simpa using (ENNReal.ofReal_lt_ofReal_iff hpositive).2 hreal
  intro z₁ z₂ hr₁ hr₂ hne K hK hz₁K hz₂K hKsub
  have hK_component : K ⊆ connectedComponentIn (Omega f) z₁ :=
    hK.subset_connectedComponentIn hz₁K hKsub
  have hz₁_mem : z₁ ∈ connectedComponentIn (Omega f) z₁ := hK_component hz₁K
  have hz₂_mem : z₂ ∈ connectedComponentIn (Omega f) z₁ := hK_component hz₂K
  have hz₁_Omega : z₁ ∈ Omega f := hKsub hz₁K
  have hdegree : 0 < f.natDegree := by
    rw [s4_f_monic_degree.2]
    norm_num
  obtain ⟨cc, hcc_mem, hcc_root⟩ :=
    s2_two_zeros_gives_critical_point f hdegree z₁ hz₁_Omega z₁ z₂ hz₁_mem hz₂_mem
      hne hr₁ hr₂
  have hcc_eq : cc = zs :=
    hzs_uniq cc (connectedComponentIn_subset (Omega f) z₁ hcc_mem) hcc_root
  have hzs_component : zs ∈ connectedComponentIn (Omega f) z₁ := by
    simpa only [hcc_eq] using hcc_mem
  have hcomponent : connectedComponentIn (Omega f) z₁ =
      connectedComponentIn (Omega f) zs := connectedComponentIn_eq hzs_component
  have hKzs : K ⊆ connectedComponentIn (Omega f) zs := by
    rw [← hcomponent]
    exact hK_component
  have hz₁_zs : z₁ ∈ connectedComponentIn (Omega f) zs := hKzs hz₁K
  have hz₂_zs : z₂ ∈ connectedComponentIn (Omega f) zs := hKzs hz₂K
  rcases hzeros z₁ hz₁_zs hr₁ with h13 | h16
  · rcases hzeros z₂ hz₂_zs hr₂ with h23 | h26
    · exact False.elim (hne (h13.trans h23.symm))
    · have hb₃K : b₃ ∈ K := by rw [← h13]; exact hz₁K
      have hb₆K : b₆ ∈ K := by rw [← h26]; exact hz₂K
      have hbound := s3_bottleneck_hausdorff f zs hzs_mem hzs_crit hv b₃ b₆ hb_ne
        hb₃_mem hb₆_mem hb₃_root hb₆_root hzeros huniq
        aHat haHat h hh hdisk (1 - ‖f.eval zs‖) rfl hδ_pos hδ_small
        K hK hKzs hb₃K hb₆K
      exact lt_of_lt_of_le henn hbound
  · rcases hzeros z₂ hz₂_zs hr₂ with h23 | h26
    · have hzeros_rev : ∀ w ∈ connectedComponentIn (Omega f) zs,
          f.IsRoot w → w = b₆ ∨ w = b₃ := by
        intro w hw hr
        exact (hzeros w hw hr).symm
      have hb₆K : b₆ ∈ K := by rw [← h16]; exact hz₁K
      have hb₃K : b₃ ∈ K := by rw [← h23]; exact hz₂K
      have hbound := s3_bottleneck_hausdorff f zs hzs_mem hzs_crit hv b₆ b₃ hb_ne.symm
        hb₆_mem hb₃_mem hb₆_root hb₃_root hzeros_rev huniq
        aHat haHat h hh hdisk (1 - ‖f.eval zs‖) rfl hδ_pos hδ_small
        K hK hKzs hb₆K hb₃K
      exact lt_of_lt_of_le henn (by simpa only [add_comm] using hbound)
    · exact False.elim (hne (h16.trans h26.symm))
