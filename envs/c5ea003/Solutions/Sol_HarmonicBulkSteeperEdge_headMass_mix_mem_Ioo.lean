-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headMass_mix_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:02:38.805806+00:00
-- url     : https://prove2.me/submissions/a8971a5e-5e0b-4f76-8fed-ad0744369063

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
open HarmonicBulkSteeperEdge Finset in
theorem solution {w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) :
    headMass a n m < mixHeadMass w a b n m ∧ mixHeadMass w a b n m < headMass b n m := by
  -- the pure head fractions are strictly ordered in the exponent
  have hstrict : headMass a n m < headMass b n m := by
    have hIcc : ∀ t : ℕ, Icc 1 t = Ioc 0 t := by
      intro t
      ext i
      simp only [mem_Icc, mem_Ioc]
      omega
    -- the full window is the head plus the tail `(m, n]`
    have hsplit : ∀ c : ℝ, headSum c n = headSum c m + ∑ l ∈ Ioc m n, pw c l := by
      intro c
      unfold headSum
      rw [hIcc n, hIcc m, sum_Ioc_consecutive _ (Nat.zero_le m) hmn.le]
    have hpw : ∀ c : ℝ, ∀ i : ℕ, 0 < i → 0 < pw c i := by
      intro c i hi
      unfold pw
      exact Real.rpow_pos_of_pos (by exact_mod_cast hi) _
    have hpos : ∀ c : ℝ, ∀ k, 1 ≤ k → 0 < headSum c k := by
      intro c k hk
      unfold headSum
      refine sum_pos (fun i hi => hpw c i ?_) ⟨1, by simp; omega⟩
      simp only [mem_Icc] at hi
      omega
    -- head-versus-tail exchange: `k^{-a} l^{-b} < k^{-b} l^{-a}` for `k < l`
    have hterm : ∀ k ∈ Icc 1 m, ∀ l ∈ Ioc m n, pw a k * pw b l < pw b k * pw a l := by
      intro k hk l hl
      simp only [mem_Icc, mem_Ioc] at hk hl
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      have hkl : (k : ℝ) < l := by exact_mod_cast (by omega : k < l)
      unfold pw
      have e1 : (k : ℝ) ^ (-a) = (k : ℝ) ^ (b - a) * (k : ℝ) ^ (-b) := by
        rw [← Real.rpow_add hk0]
        congr 1
        ring
      have e2 : (l : ℝ) ^ (-a) = (l : ℝ) ^ (b - a) * (l : ℝ) ^ (-b) := by
        rw [← Real.rpow_add hl0]
        congr 1
        ring
      rw [e1, e2]
      have hmono : (k : ℝ) ^ (b - a) < (l : ℝ) ^ (b - a) :=
        Real.rpow_lt_rpow hk0.le hkl (by linarith)
      have hnn : 0 < (k : ℝ) ^ (-b) * (l : ℝ) ^ (-b) := by positivity
      calc (k : ℝ) ^ (b - a) * (k : ℝ) ^ (-b) * (l : ℝ) ^ (-b)
          = (k : ℝ) ^ (b - a) * ((k : ℝ) ^ (-b) * (l : ℝ) ^ (-b)) := by ring
        _ < (l : ℝ) ^ (b - a) * ((k : ℝ) ^ (-b) * (l : ℝ) ^ (-b)) :=
            mul_lt_mul_of_pos_right hmono hnn
        _ = (k : ℝ) ^ (-b) * ((l : ℝ) ^ (b - a) * (l : ℝ) ^ (-b)) := by ring
    have key : headSum a m * (∑ l ∈ Ioc m n, pw b l)
        < headSum b m * (∑ l ∈ Ioc m n, pw a l) := by
      unfold headSum
      rw [sum_mul_sum, sum_mul_sum]
      have hne1 : (Icc 1 m).Nonempty := ⟨1, by simp; omega⟩
      have hne2 : (Ioc m n).Nonempty := ⟨n, by simp; omega⟩
      exact sum_lt_sum_of_nonempty hne1 fun k hk =>
        sum_lt_sum_of_nonempty hne2 fun l hl => hterm k hk l hl
    unfold headMass
    rw [div_lt_div_iff₀ (hpos a n (by omega)) (hpos b n (by omega)), hsplit a, hsplit b]
    nlinarith [key]
  have hpos : ∀ c : ℝ, ∀ k, 1 ≤ k → 0 < headSum c k := by
    intro c k hk
    unfold headSum
    refine sum_pos (fun i hi => ?_) ⟨1, by simp; omega⟩
    simp only [mem_Icc] at hi
    unfold pw
    exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < i)) _
  -- the mixture's head sum is the corresponding convex combination
  have hmix : ∀ t, mixHeadSum w a b t = (1 - w) * headSum a t + w * headSum b t := by
    intro t
    unfold mixHeadSum mix headSum
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hp := hpos a m hm
  have hq := hpos a n (by omega)
  have hr := hpos b m hm
  have hs := hpos b n (by omega)
  have hw1' : 0 < 1 - w := by linarith
  unfold headMass at hstrict ⊢
  rw [div_lt_div_iff₀ hq hs] at hstrict
  unfold mixHeadMass
  rw [hmix, hmix]
  have hden : 0 < (1 - w) * headSum a n + w * headSum b n := by positivity
  -- the mixture is a mediant of the two fractions
  constructor
  · rw [div_lt_div_iff₀ hq hden]
    nlinarith [mul_lt_mul_of_pos_left hstrict hw0]
  · rw [div_lt_div_iff₀ hden hs]
    nlinarith [mul_lt_mul_of_pos_left hstrict hw1']
