-- Prove2me | solution 1 for MetricGeometry.dist_le_of_isLocalGeodesicWithSpeed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:03:05.55604+00:00
-- url     : https://prove2.me/submissions/40973fae-7549-4559-bf58-4a1279b51b95

import Definitions.Def_metric_npc_cone

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (c : ℝ → X) (k delta : ℝ)
    (h : IsLocalGeodesicWithSpeed c k delta) (s t : ℝ) :
    dist (c s) (c t) ≤ k * |s - t| := by
  obtain ⟨hd, hgeo⟩ := h
  have hk : 0 ≤ k := by
    have := hgeo delta 0 (by rw [sub_zero, abs_of_pos hd])
    rw [sub_zero, abs_of_pos hd] at this
    nlinarith [dist_nonneg (x := c delta) (y := c 0)]
  -- monotone version, by induction on the number of steps
  have main : ∀ n : ℕ, ∀ x y : ℝ, x ≤ y → y - x ≤ n * delta →
      dist (c x) (c y) ≤ k * (y - x) := by
    intro n
    induction n with
    | zero =>
      intro x y hxy hle
      have : y = x := by simp at hle; linarith
      subst this; simp
    | succ n ih =>
      intro x y hxy hle
      by_cases hs : y - x ≤ delta
      · have := hgeo x y (by rw [abs_of_nonpos (by linarith)]; linarith)
        rw [this, abs_of_nonpos (by linarith : x - y ≤ 0)]
        linarith
      · rw [not_le] at hs
        have e1 : dist (c x) (c (x + delta)) = k * delta := by
          have := hgeo x (x + delta) (by rw [show x - (x + delta) = -delta by ring,
            abs_neg, abs_of_pos hd])
          rw [this, show x - (x + delta) = -delta by ring, abs_neg, abs_of_pos hd]
        have e2 : dist (c (x + delta)) (c y) ≤ k * (y - (x + delta)) := by
          refine ih _ _ (by linarith) ?_
          push_cast
          have : (n : ℝ) * delta = (n + 1) * delta - delta := by ring
          rw [this]
          push_cast at hle
          linarith
        calc dist (c x) (c y) ≤ dist (c x) (c (x + delta)) + dist (c (x + delta)) (c y) :=
              dist_triangle _ _ _
          _ ≤ k * delta + k * (y - (x + delta)) := by linarith
          _ = k * (y - x) := by ring
  have gen : ∀ x y : ℝ, x ≤ y → dist (c x) (c y) ≤ k * (y - x) := by
    intro x y hxy
    obtain ⟨n, hn⟩ : ∃ n : ℕ, y - x ≤ n * delta :=
      ⟨⌈(y - x) / delta⌉₊, by
        rw [← div_le_iff₀ hd]
        exact Nat.le_ceil _⟩
    exact main n x y hxy hn
  rcases le_total s t with hst | hst
  · rw [abs_of_nonpos (by linarith)]
    have := gen s t hst; linarith
  · rw [abs_of_nonneg (by linarith), dist_comm]
    have := gen t s hst; linarith
