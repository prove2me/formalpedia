-- Prove2me | solution 1 for MetricGeometry.eVariationOn_eq_of_localChordLaw
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:32:23.711167+00:00
-- url     : https://prove2.me/submissions/70838cd5-3577-4da4-b2a6-ad5edebd4cbc

import Definitions.Def_metric_npc_cone

open MetricGeometry Filter Topology

theorem solution {X : Type*} [PseudoMetricSpace X] (c : ℝ → X) (k L delta : ℝ)
    (hk : 0 ≤ k) (hL : 0 ≤ L) (hd : 0 < delta)
    (hchord : ∀ s t : ℝ, |s - t| ≤ delta →
      dist (c s) (c t) = 2 * L * |Real.sin (k * (s - t) / 2)|)
    (a b : ℝ) (hab : a ≤ b) :
    eVariationOn c (Set.Icc a b) = ENNReal.ofReal (k * L * (b - a)) := by
  have hkL : 0 ≤ k * L := mul_nonneg hk hL
  -- Step 1: the chord law makes `c` globally `k*L`-Lipschitz.
  have loc : ∀ s t : ℝ, |s - t| ≤ delta → dist (c s) (c t) ≤ k * L * |s - t| := by
    intro s t hst
    rw [hchord s t hst]
    have h1 : |Real.sin (k * (s - t) / 2)| ≤ |k * (s - t) / 2| := Real.abs_sin_le_abs
    have h2 : |k * (s - t) / 2| = k * |s - t| / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg hk]
      norm_num
    rw [h2] at h1
    nlinarith [abs_nonneg (s - t)]
  have main : ∀ n : ℕ, ∀ x y : ℝ, x ≤ y → y - x ≤ n * delta →
      dist (c x) (c y) ≤ k * L * (y - x) := by
    intro n
    induction n with
    | zero =>
      intro x y hxy hle
      have : y = x := by simp at hle; linarith
      subst this; simp
    | succ n ih =>
      intro x y hxy hle
      by_cases hs : y - x ≤ delta
      · have := loc x y (by rw [abs_of_nonpos (by linarith)]; linarith)
        rw [abs_of_nonpos (by linarith : x - y ≤ 0)] at this
        linarith
      · rw [not_le] at hs
        have e1 : dist (c x) (c (x + delta)) ≤ k * L * delta := by
          have := loc x (x + delta) (by rw [show x - (x + delta) = -delta by ring,
            abs_neg, abs_of_pos hd])
          rw [show x - (x + delta) = -delta by ring, abs_neg, abs_of_pos hd] at this
          exact this
        have e2 : dist (c (x + delta)) (c y) ≤ k * L * (y - (x + delta)) := by
          refine ih _ _ (by linarith) ?_
          push_cast at hle ⊢
          nlinarith
        calc dist (c x) (c y) ≤ dist (c x) (c (x + delta)) + dist (c (x + delta)) (c y) :=
              dist_triangle _ _ _
          _ ≤ k * L * delta + k * L * (y - (x + delta)) := by linarith
          _ = k * L * (y - x) := by ring
  have lip : ∀ x y : ℝ, x ≤ y → dist (c x) (c y) ≤ k * L * (y - x) := by
    intro x y hxy
    obtain ⟨n, hn⟩ : ∃ n : ℕ, y - x ≤ n * delta :=
      ⟨⌈(y - x) / delta⌉₊, by rw [← div_le_iff₀ hd]; exact Nat.le_ceil _⟩
    exact main n x y hxy hn
  refine le_antisymm ?_ ?_
  · -- Step 2: upper bound by telescoping any partition
    refine iSup_le ?_
    rintro ⟨n, ⟨u, hu, us⟩⟩
    calc (∑ i ∈ Finset.range n, edist (c (u (i + 1))) (c (u i)))
        ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (k * L * u (i + 1) - k * L * u i) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [edist_dist]
          refine ENNReal.ofReal_le_ofReal ?_
          have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
          have := lip (u i) (u (i + 1)) hle
          rw [dist_comm] at this
          linarith
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (k * L * u (i + 1) - k * L * u i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _
          have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
          nlinarith
      _ = ENNReal.ofReal (k * L * u n - k * L * u 0) := by
          rw [Finset.sum_range_sub fun i => k * L * u i]
      _ ≤ ENNReal.ofReal (k * L * (b - a)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : u n ≤ b := (us n).2
          have h2 : a ≤ u 0 := (us 0).1
          nlinarith
  · -- Step 3: lower bound by uniform partitions, whose chord sums tend to the arclength
    rcases eq_or_lt_of_le hab with rfl | hab'
    · simp
    set S : ℕ → ℝ := fun n => (n : ℝ) * (2 * L * |Real.sin (k * (b - a) / (2 * n))|) with hS
    have hpart : ∀ n : ℕ, 0 < n → (b - a) / n ≤ delta →
        ENNReal.ofReal (S n) ≤ eVariationOn c (Set.Icc a b) := by
      intro n hn0 hstep
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
      set u : ℕ → ℝ := fun i => a + (b - a) * (min i n : ℕ) / n with hu_def
      have hmono : Monotone u := by
        intro i j hij
        have hc : ((min i n : ℕ) : ℝ) ≤ ((min j n : ℕ) : ℝ) := by
          exact_mod_cast min_le_min hij (le_refl n)
        have hba : (0:ℝ) ≤ b - a := by linarith
        simp only [hu_def]; gcongr
      have hmem : ∀ i, u i ∈ Set.Icc a b := by
        intro i
        have h0 : (0:ℝ) ≤ ((min i n : ℕ) : ℝ) := Nat.cast_nonneg _
        have h1 : ((min i n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.min_le_right i n
        have hba : (0:ℝ) ≤ b - a := by linarith
        refine ⟨?_, ?_⟩
        · simp only [hu_def]
          have : (0:ℝ) ≤ (b - a) * ((min i n : ℕ) : ℝ) / n := by positivity
          linarith
        · simp only [hu_def]
          have : (b - a) * ((min i n : ℕ) : ℝ) / n ≤ (b - a) := by
            rw [div_le_iff₀ hnR]; nlinarith
          linarith
      have hval : ∀ i ∈ Finset.range n,
          edist (c (u (i + 1))) (c (u i))
            = ENNReal.ofReal (2 * L * |Real.sin (k * (b - a) / (2 * n))|) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        have e1 : min (i + 1) n = i + 1 := min_eq_left hi
        have e2 : min i n = i := min_eq_left (le_of_lt hi)
        have hdiff : u (i + 1) - u i = (b - a) / n := by
          simp only [hu_def, e1, e2]; push_cast; field_simp; ring
        have habs : |u (i + 1) - u i| = (b - a) / n := by
          rw [hdiff, abs_of_nonneg (by positivity)]
        have hch := hchord (u (i + 1)) (u i) (by rw [habs]; exact hstep)
        rw [edist_dist, hch, hdiff]
        congr 3
        field_simp
      calc ENNReal.ofReal (S n)
          = ∑ i ∈ Finset.range n, ENNReal.ofReal (2 * L * |Real.sin (k * (b - a) / (2 * n))|) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity)]
        _ = ∑ i ∈ Finset.range n, edist (c (u (i + 1))) (c (u i)) :=
            (Finset.sum_congr rfl hval).symm
        _ ≤ eVariationOn c (Set.Icc a b) := eVariationOn.sum_le hmono hmem
    -- the chord sums converge to the arclength
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (S n)) atTop
        (𝓝 (ENNReal.ofReal (k * L * (b - a)))) := by
      refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
      set c0 : ℝ := k * (b - a) / 2 with hc0
      have hrw : ∀ n : ℕ, 0 < n → S n = 2 * L * |c0 * Real.sinc (c0 / n)| := by
        intro n hn
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hx : k * (b - a) / (2 * (n:ℝ)) = c0 / (n:ℝ) := by rw [hc0]; ring
        simp only [hS, hx]
        by_cases h0 : c0 = 0
        · simp [h0]
        · have hne : c0 / (n:ℝ) ≠ 0 := div_ne_zero h0 (ne_of_gt hnR)
          rw [Real.sinc_of_ne_zero hne,
            show c0 * (Real.sin (c0 / (n:ℝ)) / (c0 / (n:ℝ))) = (n : ℝ) * Real.sin (c0 / (n:ℝ))
              from by field_simp,
            abs_mul, abs_of_nonneg (le_of_lt hnR)]
          ring
      have htend : Tendsto (fun n : ℕ => 2 * L * |c0 * Real.sinc (c0 / n)|) atTop
          (𝓝 (k * L * (b - a))) := by
        have h1 : Tendsto (fun n : ℕ => c0 / (n : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun n : ℕ => Real.sinc (c0 / n)) atTop (𝓝 1) := by
          have := (Real.continuous_sinc.tendsto 0).comp h1
          simpa using this
        have h3 : Tendsto (fun n : ℕ => 2 * L * |c0 * Real.sinc (c0 / n)|) atTop
            (𝓝 (2 * L * |c0 * 1|)) := by
          exact tendsto_const_nhds.mul ((tendsto_const_nhds.mul h2).abs)
        have hval : 2 * L * |c0 * 1| = k * L * (b - a) := by
          rw [mul_one, hc0, abs_of_nonneg (by positivity : (0:ℝ) ≤ k * (b - a) / 2)]
          ring
        rwa [hval] at h3
      refine htend.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (hrw n hn).symm
    refine le_of_tendsto hlim ?_
    obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → 0 < n ∧ (b - a) / n ≤ delta := by
      refine ⟨⌈(b - a) / delta⌉₊ + 1, fun n hn => ⟨by omega, ?_⟩⟩
      have hnR : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      have hkey : (b - a) / delta ≤ (n : ℝ) := by
        calc (b - a) / delta ≤ (⌈(b - a) / delta⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) hn
      rw [div_le_iff₀ hd] at hkey
      rw [div_le_iff₀ hnR]
      linarith
    filter_upwards [eventually_ge_atTop n0] with n hn
    exact hpart n (hn0 n hn).1 (hn0 n hn).2
