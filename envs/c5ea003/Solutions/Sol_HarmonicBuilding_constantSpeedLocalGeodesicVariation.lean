-- Prove2me | solution 1 for HarmonicBuilding.constantSpeedLocalGeodesicVariation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T15:05:44.18162+00:00
-- url     : https://prove2.me/submissions/a758bd79-82c0-4d76-aa43-9eaaa50222cd

import Mathlib

open Set

theorem solution {X : Type*} [PseudoMetricSpace X]
    (c : ℝ → X) (k delta : ℝ) (hk : 0 ≤ k) (hdelta : 0 < delta)
    (hloc : ∀ s t : ℝ, |s - t| ≤ delta → dist (c s) (c t) = k * |s - t|)
    (a b : ℝ) (hab : a ≤ b) :
    eVariationOn c (Set.Icc a b) = ENNReal.ofReal (k * (b - a)) := by
  -- On an interval no longer than `delta` the curve is a genuine geodesic,
  -- so every partition sum telescopes exactly.
  have short : ∀ x y : ℝ, x ≤ y → y - x ≤ delta →
      eVariationOn c (Set.Icc x y) = ENNReal.ofReal (k * (y - x)) := by
    intro x y hxy hlen
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      rintro ⟨n, u, hu, us⟩
      have tel : ∀ m : ℕ,
          ∑ i ∈ Finset.range m, (k * (u (i + 1) - u i)) = k * (u m - u 0) := by
        intro m
        induction m with
        | zero => simp
        | succ p ih => rw [Finset.sum_range_succ, ih]; ring
      have hterm : ∀ i : ℕ,
          edist (c (u (i + 1))) (c (u i)) = ENNReal.ofReal (k * (u (i + 1) - u i)) := by
        intro i
        have hmono : u i ≤ u (i + 1) := hu (Nat.le_succ i)
        have hlo : x ≤ u i := (us i).1
        have hhi : u (i + 1) ≤ y := (us (i + 1)).2
        have habs : |u (i + 1) - u i| = u (i + 1) - u i := abs_of_nonneg (by linarith)
        rw [edist_dist, hloc _ _ (by rw [habs]; linarith), habs]
      simp only [hterm]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        have : u i ≤ u (i + 1) := hu (Nat.le_succ i); nlinarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [tel n]
      have h0 : x ≤ u 0 := (us 0).1
      have hn : u n ≤ y := (us n).2
      nlinarith
    · have hmono : Monotone (fun i : ℕ => if i = 0 then x else y) := by
        intro i j hij
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi; by_cases hj : j = 0 <;> simp [hj, hxy]
        · have hj : j ≠ 0 := by omega
          have hi' : i ≠ 0 := by omega
          simp [hi', hj]
      have hmem : ∀ i : ℕ, (if i = 0 then x else y) ∈ Set.Icc x y := by
        intro i; by_cases hi : i = 0 <;> simp [hi, hxy]
      have hsum := eVariationOn.sum_le (f := c) (s := Set.Icc x y) (n := 1) hmono hmem
      have habs : |y - x| = y - x := abs_of_nonneg (by linarith)
      simpa [edist_dist, hloc y x (by rw [habs]; linarith), habs] using hsum
  -- Chop `[a, b]` into finitely many pieces of length `delta` and add up.
  have key : ∀ n : ℕ, ∀ x y : ℝ, x ≤ y → y - x ≤ n * delta →
      eVariationOn c (Set.Icc x y) = ENNReal.ofReal (k * (y - x)) := by
    intro n
    induction n with
    | zero =>
      intro x y hxy hlen
      simp only [Nat.cast_zero, zero_mul] at hlen
      have hyx : y = x := le_antisymm (by linarith) hxy
      subst hyx
      simp [eVariationOn.subsingleton c (Set.subsingleton_Icc_of_ge le_rfl)]
    | succ m ih =>
      intro x y hxy hlen
      by_cases hs : y - x ≤ delta
      · exact short x y hxy hs
      rw [not_le] at hs
      have hxz : x ≤ x + delta := by linarith
      have hzy : x + delta ≤ y := by linarith
      have h1 : eVariationOn c (Set.Icc x (x + delta)) = ENNReal.ofReal (k * delta) := by
        have := short x (x + delta) hxz (by linarith)
        simpa using this
      have h2 : eVariationOn c (Set.Icc (x + delta) y)
          = ENNReal.ofReal (k * (y - (x + delta))) := by
        refine ih (x + delta) y hzy ?_
        push_cast at hlen
        linarith
      have hadd := eVariationOn.Icc_add_Icc c (s := Set.univ) hxz hzy (Set.mem_univ _)
      simp only [Set.univ_inter] at hadd
      rw [← hadd, h1, h2, ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
      congr 1
      ring
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / delta)
  exact key n a b hab ((div_le_iff₀ hdelta).mp hn)
