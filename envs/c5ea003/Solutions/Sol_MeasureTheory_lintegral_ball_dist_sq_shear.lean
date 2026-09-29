-- Prove2me | solution 1 for MeasureTheory.lintegral_ball_dist_sq_shear
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T09:42:46.106895+00:00
-- url     : https://prove2.me/submissions/3dfa602c-6019-4aff-81d3-1f906c34998c

import Mathlib

open MeasureTheory

universe u

theorem solution {X : Type u} [PseudoMetricSpace X] (B : Set ℂ) (hB : IsOpen B)
    (f : ℂ → X) (hf : ContinuousOn f B) (eps : ℝ) :
    (∫⁻ z in B, ∫⁻ w in B ∩ Metric.ball z eps,
        ENNReal.ofReal (dist (f w) (f z) ^ 2))
      = ∫⁻ h in Metric.ball (0:ℂ) eps,
          ∫⁻ z in B ∩ (fun y : ℂ => y + h) ⁻¹' B,
            ENNReal.ofReal (dist (f (z + h)) (f z) ^ 2) := by
  classical
  set W : Set (ℂ × ℂ) := {p : ℂ × ℂ | p.1 ∈ B ∧ p.1 + p.2 ∈ B ∧ ‖p.2‖ < eps} with hWdef
  have hWopen : IsOpen W := by
    have h1 : IsOpen {p : ℂ × ℂ | p.1 ∈ B} := hB.preimage continuous_fst
    have h2 : IsOpen {p : ℂ × ℂ | p.1 + p.2 ∈ B} :=
      hB.preimage (continuous_fst.add continuous_snd)
    have h3 : IsOpen {p : ℂ × ℂ | ‖p.2‖ < eps} :=
      isOpen_lt (continuous_snd.norm) continuous_const
    exact h1.inter (h2.inter h3)
  have hWm : MeasurableSet W := hWopen.measurableSet
  set g : ℂ × ℂ → ENNReal :=
    fun p => ENNReal.ofReal (dist (f (p.1 + p.2)) (f p.1) ^ 2) with hgdef
  set G : ℂ × ℂ → ENNReal := W.indicator g with hGdef
  have hgcont : ContinuousOn g W := by
    have hc1 : ContinuousOn (fun p : ℂ × ℂ => f p.1) W :=
      hf.comp continuousOn_fst (fun p hp => hp.1)
    have hc2 : ContinuousOn (fun p : ℂ × ℂ => f (p.1 + p.2)) W :=
      hf.comp (continuousOn_fst.add continuousOn_snd) (fun p hp => hp.2.1)
    have hd : ContinuousOn (fun p : ℂ × ℂ => dist (f (p.1 + p.2)) (f p.1)) W :=
      continuous_dist.comp_continuousOn (hc2.prodMk hc1)
    exact ENNReal.continuous_ofReal.comp_continuousOn (hd.pow 2)
  have hGmeas : AEMeasurable G (volume.prod volume) := by
    rw [hGdef, aemeasurable_indicator_iff hWm]
    exact hgcont.aemeasurable hWm
  have hBm : MeasurableSet B := hB.measurableSet
  -- the `z`-slice
  have hslice1 : ∀ z : ℂ, (∫⁻ h, G (z, h))
      = B.indicator (fun z => ∫⁻ w in B ∩ Metric.ball z eps,
          ENNReal.ofReal (dist (f w) (f z) ^ 2)) z := by
    intro z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      set Fz : ℂ → ENNReal := (B ∩ Metric.ball z eps).indicator
        (fun w => ENNReal.ofReal (dist (f w) (f z) ^ 2)) with hFzdef
      have hFeq : (fun h : ℂ => G (z, h)) = fun h : ℂ => Fz (z + h) := by
        funext h
        by_cases hmem : z + h ∈ B ∧ ‖h‖ < eps
        · rw [hGdef, Set.indicator_of_mem (by exact ⟨hz, hmem.1, hmem.2⟩), hFzdef,
            Set.indicator_of_mem]
          refine ⟨hmem.1, ?_⟩
          simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
          exact hmem.2
        · rw [hGdef, Set.indicator_of_notMem (by
            intro hc; exact hmem ⟨hc.2.1, hc.2.2⟩), hFzdef,
            Set.indicator_of_notMem]
          intro hc
          refine hmem ⟨hc.1, ?_⟩
          have := hc.2
          simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] at this
          exact this
      rw [hFeq, lintegral_add_left_eq_self Fz z, hFzdef,
        lintegral_indicator (hBm.inter measurableSet_ball)]
    · rw [Set.indicator_of_notMem hz]
      have hzero : ∀ h : ℂ, G (z, h) = 0 := by
        intro h
        rw [hGdef, Set.indicator_of_notMem]
        intro hmem
        exact hz hmem.1
      simp only [hzero, lintegral_const, zero_mul]
  -- the `h`-slice
  have hslice2 : ∀ h : ℂ, (∫⁻ z, G (z, h))
      = (Metric.ball (0:ℂ) eps).indicator
          (fun h => ∫⁻ z in B ∩ (fun y : ℂ => y + h) ⁻¹' B,
            ENNReal.ofReal (dist (f (z + h)) (f z) ^ 2)) h := by
    intro h
    by_cases hh : ‖h‖ < eps
    · have hhmem : h ∈ Metric.ball (0:ℂ) eps := by
        simpa [Metric.mem_ball, dist_eq_norm] using hh
      rw [Set.indicator_of_mem hhmem]
      have hEq : (fun z : ℂ => G (z, h))
          = (B ∩ (fun y : ℂ => y + h) ⁻¹' B).indicator
              (fun z => ENNReal.ofReal (dist (f (z + h)) (f z) ^ 2)) := by
        funext z
        by_cases hmem : z ∈ B ∧ z + h ∈ B
        · rw [hGdef, Set.indicator_of_mem (by exact ⟨hmem.1, hmem.2, hh⟩),
            Set.indicator_of_mem (by exact ⟨hmem.1, hmem.2⟩)]
        · rw [hGdef, Set.indicator_of_notMem (by
            intro hc; exact hmem ⟨hc.1, hc.2.1⟩),
            Set.indicator_of_notMem (by intro hc; exact hmem ⟨hc.1, hc.2⟩)]
      rw [hEq, lintegral_indicator
        (hBm.inter (hBm.preimage (by fun_prop)))]
    · have hhnot : h ∉ Metric.ball (0:ℂ) eps := by
        simpa [Metric.mem_ball, dist_eq_norm] using hh
      rw [Set.indicator_of_notMem hhnot]
      have hzero : ∀ z : ℂ, G (z, h) = 0 := by
        intro z
        rw [hGdef, Set.indicator_of_notMem]
        intro hmem
        exact hh hmem.2.2
      simp only [hzero, lintegral_const, zero_mul]
  calc (∫⁻ z in B, ∫⁻ w in B ∩ Metric.ball z eps,
          ENNReal.ofReal (dist (f w) (f z) ^ 2))
      = ∫⁻ z, B.indicator (fun z => ∫⁻ w in B ∩ Metric.ball z eps,
          ENNReal.ofReal (dist (f w) (f z) ^ 2)) z := by
        rw [lintegral_indicator hBm]
    _ = ∫⁻ z, ∫⁻ h, G (z, h) := by
        exact (lintegral_congr fun z => (hslice1 z)).symm
    _ = ∫⁻ h, ∫⁻ z, G (z, h) := by
        exact lintegral_lintegral_swap (by exact hGmeas)
    _ = ∫⁻ h, (Metric.ball (0:ℂ) eps).indicator
          (fun h => ∫⁻ z in B ∩ (fun y : ℂ => y + h) ⁻¹' B,
            ENNReal.ofReal (dist (f (z + h)) (f z) ^ 2)) h :=
        lintegral_congr fun h => hslice2 h
    _ = ∫⁻ h in Metric.ball (0:ℂ) eps,
          ∫⁻ z in B ∩ (fun y : ℂ => y + h) ⁻¹' B,
            ENNReal.ofReal (dist (f (z + h)) (f z) ^ 2) := by
        rw [lintegral_indicator measurableSet_ball]
