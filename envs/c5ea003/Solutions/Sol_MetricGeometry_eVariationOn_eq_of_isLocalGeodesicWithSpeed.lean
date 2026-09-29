-- Prove2me | solution 1 for MetricGeometry.eVariationOn_eq_of_isLocalGeodesicWithSpeed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:03:06.123789+00:00
-- url     : https://prove2.me/submissions/bc390e13-a7dd-4886-8370-65165907cd9e

import Definitions.Def_metric_npc_cone
import Theorems.Thm_MetricGeometry_dist_le_of_isLocalGeodesicWithSpeed

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (c : ℝ → X) (k delta : ℝ)
    (h : IsLocalGeodesicWithSpeed c k delta) (a b : ℝ) (hab : a ≤ b) :
    eVariationOn c (Set.Icc a b) = ENNReal.ofReal (k * (b - a)) := by
  have lip : ∀ s t : ℝ, dist (c s) (c t) ≤ k * |s - t| :=
    fun s t => MetricGeometry.dist_le_of_isLocalGeodesicWithSpeed c k delta h s t
  obtain ⟨hd, hgeo⟩ := h
  have hk : 0 ≤ k := by
    have := hgeo delta 0 (by rw [sub_zero, abs_of_pos hd])
    rw [sub_zero, abs_of_pos hd] at this
    nlinarith [dist_nonneg (x := c delta) (y := c 0)]
  refine le_antisymm ?_ ?_
  · -- upper bound: c is k-Lipschitz, so every partition sum telescopes
    refine iSup_le ?_
    rintro ⟨n, ⟨u, hu, us⟩⟩
    calc (∑ i ∈ Finset.range n, edist (c (u (i + 1))) (c (u i)))
        ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (k * u (i + 1) - k * u i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [edist_dist]
          refine ENNReal.ofReal_le_ofReal ?_
          have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
          have := lip (u (i + 1)) (u i)
          rw [abs_of_nonneg (by linarith)] at this
          linarith
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (k * u (i + 1) - k * u i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _
          have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
          nlinarith
      _ = ENNReal.ofReal (k * u n - k * u 0) := by
          rw [Finset.sum_range_sub fun i => k * u i]
      _ ≤ ENNReal.ofReal (k * (b - a)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : u n ≤ b := (us n).2
          have h2 : a ≤ u 0 := (us 0).1
          nlinarith
  · -- lower bound: a uniform partition of mesh at most delta realizes the value
    rcases eq_or_lt_of_le hab with rfl | hab'
    · simp
    set n : ℕ := ⌈(b - a) / delta⌉₊ + 1 with hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := Nat.succ_pos _
      exact_mod_cast this
    have hstep : (b - a) / n ≤ delta := by
      rw [div_le_iff₀ hnR]
      have h1 : (b - a) / delta ≤ (n : ℝ) := by
        rw [hn]; push_cast; linarith [Nat.le_ceil ((b - a) / delta)]
      rw [div_le_iff₀ hd] at h1
      linarith
    set u : ℕ → ℝ := fun i => a + (b - a) * (min i n : ℕ) / n with hu_def
    have hmono : Monotone u := by
      intro i j hij
      have : ((min i n : ℕ) : ℝ) ≤ ((min j n : ℕ) : ℝ) := by
        exact_mod_cast min_le_min hij (le_refl n)
      simp only [hu_def]
      have hba : (0:ℝ) ≤ b - a := by linarith
      gcongr
    have hmem : ∀ i, u i ∈ Set.Icc a b := by
      intro i
      have h0 : (0:ℝ) ≤ ((min i n : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 : ((min i n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.min_le_right i n
      have hba : (0:ℝ) ≤ b - a := by linarith
      constructor
      · simp only [hu_def]
        have : (0:ℝ) ≤ (b - a) * ((min i n : ℕ) : ℝ) / n := by positivity
        linarith
      · simp only [hu_def]
        have : (b - a) * ((min i n : ℕ) : ℝ) / n ≤ (b - a) := by
          rw [div_le_iff₀ hnR]; nlinarith
        linarith
    have hval : ∀ i ∈ Finset.range n,
        edist (c (u (i + 1))) (c (u i)) = ENNReal.ofReal (k * ((b - a) / n)) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      have e1 : min (i + 1) n = i + 1 := min_eq_left hi
      have e2 : min i n = i := min_eq_left (le_of_lt hi)
      have hdiff : u (i + 1) - u i = (b - a) / n := by
        simp only [hu_def, e1, e2]; push_cast; field_simp; ring
      have habs : |u (i + 1) - u i| = (b - a) / n := by
        rw [hdiff, abs_of_nonneg (by positivity)]
      have := hgeo (u (i + 1)) (u i) (by rw [habs]; exact hstep)
      rw [edist_dist, this, habs]
    calc ENNReal.ofReal (k * (b - a))
        = ∑ i ∈ Finset.range n, ENNReal.ofReal (k * ((b - a) / n)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ = ∑ i ∈ Finset.range n, edist (c (u (i + 1))) (c (u i)) :=
          (Finset.sum_congr rfl hval).symm
      _ ≤ eVariationOn c (Set.Icc a b) := eVariationOn.sum_le hmono hmem
