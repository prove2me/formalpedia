-- Prove2me | solution 1 for Erdos1041.Counterexample.erdos1041_counterexample_of_slices
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:31:47.410414+00:00
-- url     : https://prove2.me/submissions/5e4c5959-c01e-4d9c-920e-0615f4e7810a

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_barrier_excludes
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_epsilon_pos
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_rational_margin
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_rho_lt_one
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_rho_pos
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_sqrt_le_scaled
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_u_six
import Theorems.Thm_Erdos1041_Counterexample_AssemblyAux_u_three
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

noncomputable section
open scoped ComplexConjugate ENNReal

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution
    (hS2 :
      ∀ (p : Polynomial ℂ) (hp : 0 < p.natDegree) (z : ℂ) (hz : z ∈ Omega p)
          (w₁ w₂ : ℂ) (hw₁ : w₁ ∈ connectedComponentIn (Omega p) z)
          (hw₂ : w₂ ∈ connectedComponentIn (Omega p) z) (hne : w₁ ≠ w₂)
          (hr₁ : p.IsRoot w₁) (hr₂ : p.IsRoot w₂),
      ∃ cc ∈ connectedComponentIn (Omega p) z, (Polynomial.derivative p).IsRoot cc)
    (hS3 :
      ∀ (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
          (hcrit : (Polynomial.derivative p).IsRoot cc)
          (hv : p.eval cc ≠ 0)
          (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂)
          (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
          (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
          (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
          (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
          (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
            (Polynomial.derivative p).IsRoot c' → c' = cc)
          (hsimple : Polynomial.rootMultiplicity cc (Polynomial.derivative p) = 1)
          (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
          (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
          (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
          (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
          (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc 0 1))
          (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
          (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc),
      ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
            ≤ pathLength γ)
    (hS4degree :
      f.Monic ∧ f.natDegree = 7)
    (hS4circle :
      ∀ z, f.IsRoot z → ‖z‖ = (ρ : ℝ))
    (hS4nodup :
      f.roots.Nodup)
    (hS4critical :
      ∃ (zs b₃ b₆ aHat : ℂ) (h : ℝ),
            zs ∈ Omega f ∧
            (Polynomial.derivative f).IsRoot zs ∧
            Polynomial.rootMultiplicity zs (Polynomial.derivative f) = 1 ∧
            (∀ c' ∈ Omega f, (Polynomial.derivative f).IsRoot c' → c' = zs) ∧
            0 < ‖f.eval zs‖ ∧
            0 < 1 - ‖f.eval zs‖ ∧
            1 - ‖f.eval zs‖ ≤ (ρ : ℝ) ^ 7 * (ε : ℝ) ^ 7 * (36 / 5 / 10 ^ 6) ∧
            aHat ≠ 0 ∧ 0 < h ∧
            180 * (ρ : ℝ) ^ 5 * (ε : ℝ) ^ 5 ≤ ‖aHat‖ ∧
            (∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad f zs).eval z / aHat - 1‖ ≤ 1 / 4) ∧
            1 - ‖f.eval zs‖ < ‖aHat‖ * h ^ 2 / 4 ∧
            ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
              < (ρ : ℝ) * (ε : ℝ) / 1000 ∧
            f.IsRoot b₃ ∧ f.IsRoot b₆ ∧ b₃ ≠ b₆ ∧
            ‖b₃ - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 ∧
            ‖b₆ - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 ∧
            (∀ w, f.IsRoot w → ∃ j : Fin 7, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10) ∧
            (∀ w, f.IsRoot w →
              ‖w - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
              w = b₃) ∧
            (∀ w, f.IsRoot w →
              ‖w - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10 →
              w = b₆) ∧
            (ρ : ℝ) * (2 + (ε : ℝ) * (143 / 1000)) ≤ ‖b₃ - zs‖ + ‖b₆ - zs‖)
    (hS5 :
      ∀ (zs b₃ b₆ : ℂ) (hzs : zs ∈ Omega f)
          (hcrit : (Polynomial.derivative f).IsRoot zs)
          (hr₃ : f.IsRoot b₃) (hr₆ : f.IsRoot b₆)
          (hnear₃ : ‖b₃ - (ρ : ℂ) * Complex.exp (6 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10)
          (hnear₆ : ‖b₆ - (ρ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I / 7)‖ < (ρ : ℝ) / 10),
      b₃ ∈ connectedComponentIn (Omega f) zs ∧ b₆ ∈ connectedComponentIn (Omega f) zs)
    (hS7 :
      ∀ (zs : ℂ)
          (hnear : ‖zs - (ρ : ℂ) * (ε : ℂ) * (((823247 / 1000000 : ℚ) : ℂ)) * Complex.I‖
            < (ρ : ℝ) * (ε : ℝ) / 1000),
      ∃ g₁ g₂ : ℂ → ℝ, Continuous g₁ ∧ Continuous g₂ ∧
            (∀ z, g₁ z = 0 → 1 ≤ ‖f.eval z‖) ∧ (∀ z, g₂ z = 0 → 1 ≤ ‖f.eval z‖) ∧
            g₁ zs < 0 ∧ g₂ zs < 0 ∧
            (∀ j : Fin 7, j.val = 0 ∨ j.val = 1 ∨ j.val = 2 →
              ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₁ w) ∧
            (∀ j : Fin 7, j.val = 4 ∨ j.val = 5 →
              ∀ w, ‖w - (ρ : ℂ) * u j.val‖ < (ρ : ℝ) / 10 → 0 < g₂ w)) :
    f.Monic ∧ f.natDegree = 7 ∧
    (∀ z, f.IsRoot z → ‖z‖ < 1) ∧
    f.roots.Nodup ∧
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) → γ 0 = z₁ → γ 1 = z₂ →
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖f.eval (γ τ)‖ < 1) →
        (2 : ENNReal) < pathLength γ := by
  obtain ⟨zs, b₃, b₆, aHat, h, hzs_mem, hzs_crit, hzs_simple, hzs_uniq,
      hv_pos, hδ_pos, hδ_le, haHat, hh, haHat_lo, hdisk, hδ_small,
      hzs_near, hb₃_root, hb₆_root, hb_ne, hb₃_near, hb₆_near,
      hroot_near, hb₃_uniq, hb₆_uniq, hproj⟩ := hS4critical
  obtain ⟨g₁, g₂, hg₁cont, hg₂cont, hg₁zero, hg₂zero,
      hg₁zs, hg₂zs, hg₁pos, hg₂pos⟩ := hS7 zs hzs_near

  -- The replacement for the deleted zero-counting obligation: IVT plus S7.
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
    hS5 zs b₃ b₆ hzs_mem hzs_crit hb₃_root hb₆_root hb₃_near hb₆_near
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
  have henn : (2 : ENNReal) < ENNReal.ofReal (‖b₃ - zs‖ + ‖b₆ - zs‖ -
      8 / 3 * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖)) := by
    have hpositive : 0 < ‖b₃ - zs‖ + ‖b₆ - zs‖ -
        8 / 3 * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) :=
      lt_trans (by norm_num) hreal
    simpa using (ENNReal.ofReal_lt_ofReal_iff hpositive).2 hreal

  refine ⟨hS4degree.1, hS4degree.2, ?_, hS4nodup, ?_⟩
  · intro z hz
    rw [hS4circle z hz]
    exact AssemblyAux.rho_lt_one
  · intro z₁ z₂ hr₁ hr₂ hne γ hcont hγ0 hγ1 hγOmega
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hpath_subset : γ '' Set.Icc (0 : ℝ) 1 ⊆ Omega f := by
      rintro w ⟨τ, hτ, rfl⟩
      exact hγOmega τ hτ
    have hstart : z₁ ∈ γ '' Set.Icc (0 : ℝ) 1 := ⟨0, h0, hγ0⟩
    have hpre : IsPreconnected (γ '' Set.Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image γ hcont
    have hpath_component : γ '' Set.Icc (0 : ℝ) 1 ⊆
        connectedComponentIn (Omega f) z₁ :=
      hpre.subset_connectedComponentIn hstart hpath_subset
    have hz₁_mem : z₁ ∈ connectedComponentIn (Omega f) z₁ :=
      hpath_component hstart
    have hz₂_mem : z₂ ∈ connectedComponentIn (Omega f) z₁ :=
      hpath_component ⟨1, h1, hγ1⟩
    have hz₁_Omega : z₁ ∈ Omega f := hpath_subset hstart
    have hdegree : 0 < f.natDegree := by
      rw [hS4degree.2]
      norm_num
    obtain ⟨cc, hcc_mem, hcc_root⟩ :=
      hS2 f hdegree z₁ hz₁_Omega z₁ z₂ hz₁_mem hz₂_mem hne hr₁ hr₂
    have hcc_eq : cc = zs :=
      hzs_uniq cc (connectedComponentIn_subset (Omega f) z₁ hcc_mem) hcc_root
    have hzs_component : zs ∈ connectedComponentIn (Omega f) z₁ := by
      simpa only [hcc_eq] using hcc_mem
    have hcomponent : connectedComponentIn (Omega f) z₁ =
        connectedComponentIn (Omega f) zs := connectedComponentIn_eq hzs_component
    have hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        γ τ ∈ connectedComponentIn (Omega f) zs := by
      intro τ hτ
      rw [← hcomponent]
      exact hpath_component ⟨τ, hτ, rfl⟩
    have hz₁_zs : z₁ ∈ connectedComponentIn (Omega f) zs := by
      rw [← hγ0]
      exact hγmem 0 h0
    have hz₂_zs : z₂ ∈ connectedComponentIn (Omega f) zs := by
      rw [← hγ1]
      exact hγmem 1 h1

    -- Use S3 in each endpoint order. The path itself is never reversed.
    rcases hzeros z₁ hz₁_zs hr₁ with h13 | h16
    · rcases hzeros z₂ hz₂_zs hr₂ with h23 | h26
      · exact False.elim (hne (h13.trans h23.symm))
      · have hbound := hS3 f zs hzs_mem hzs_crit hv b₃ b₆ hb_ne
          hb₃_mem hb₆_mem hb₃_root hb₆_root hzeros huniq hzs_simple
          aHat haHat h hh hdisk (1 - ‖f.eval zs‖) rfl hδ_pos hδ_small
          γ hcont (hγ0.trans h13) (hγ1.trans h26) hγmem
        exact lt_of_lt_of_le henn hbound
    · rcases hzeros z₂ hz₂_zs hr₂ with h23 | h26
      · have hzeros_rev : ∀ w ∈ connectedComponentIn (Omega f) zs,
            f.IsRoot w → w = b₆ ∨ w = b₃ := by
          intro w hw hr
          exact (hzeros w hw hr).symm
        have hbound := hS3 f zs hzs_mem hzs_crit hv b₆ b₃ hb_ne.symm
          hb₆_mem hb₃_mem hb₆_root hb₃_root hzeros_rev huniq hzs_simple
          aHat haHat h hh hdisk (1 - ‖f.eval zs‖) rfl hδ_pos hδ_small
          γ hcont (hγ0.trans h16) (hγ1.trans h23) hγmem
        exact lt_of_lt_of_le henn (by simpa only [add_comm] using hbound)
      · exact False.elim (hne (h16.trans h26.symm))
