-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headMass_lt_of_exponent_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:31:16.22045+00:00
-- url     : https://prove2.me/submissions/7f7d3749-37b5-4c21-bdc6-d24bae06c880

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
open HarmonicBulkSteeperEdge Finset in
theorem solution {a b : ℝ} {m n : ℕ} (hab : a < b) (hm : 1 ≤ m)
    (hmn : m < n) : headMass a n m < headMass b n m := by
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
