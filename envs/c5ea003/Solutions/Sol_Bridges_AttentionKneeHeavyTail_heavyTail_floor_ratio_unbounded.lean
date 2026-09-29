-- Prove2me | solution 1 for Bridges.AttentionKneeHeavyTail.heavyTail_floor_ratio_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T20:52:01.272986+00:00
-- url     : https://prove2.me/submissions/48dc8f8f-2702-4919-9feb-c0feebec7020

import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeFlatness
import Definitions.Def_Bridges_AttentionKneeGeometry
import Definitions.Def_Bridges_AttentionKneeHeavyTail
open Finset Bridges.AttentionKneeGeometry Bridges.AttentionKneeEntropyBound Bridges.AttentionKneeFlatness Bridges.AttentionKneeHeavyTail in
theorem solution (R : ℝ) :
    ∃ (w : ℕ → ℝ) (E : ℝ), (∀ i, 0 ≤ w i) ∧ Antitone w ∧ 0 < E ∧
      (∀ k, energy w k ≤ E) ∧ (∃ k, (3 / 4 : ℝ) ≤ mass w k) ∧
      R * ((3 / 4 : ℝ) ^ 2 / E) < (knee w (3 / 4) : ℝ) := by
  -- a heavy head `1/2` followed by a flat tail of `N` keys of weight `1/(2N)`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈9 * R / 4⌉₊ + 1 := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by omega
  have hNR : 9 * R / 4 < N := by
    have := Nat.le_ceil (9 * R / 4)
    rw [hN]
    push_cast
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (2 * N) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hNc : (N : ℝ) * c = 1 / 2 := by rw [hc]; field_simp
  have hc12 : c ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ,
      w = fun i => (if i = 0 then (1 / 2 : ℝ) else 0) + (if i ∈ Icc 1 N then c else 0) := ⟨_, rfl⟩
  have hwi : ∀ i, w i = (if i = 0 then (1 / 2 : ℝ) else 0) + (if i ∈ Icc 1 N then c else 0) :=
    fun i => by rw [hw]
  have hnn : ∀ i, 0 ≤ w i := by
    intro i
    rw [hwi]
    split_ifs <;> linarith
  have hle : ∀ i, w i ≤ 1 / 2 := by
    intro i
    rw [hwi]
    simp only [mem_Icc]
    split_ifs <;> linarith
  -- closed form of the retained mass
  have hmass : ∀ k, mass w k = (if 0 ∈ range k then (1 / 2 : ℝ) else 0)
      + ((range k ∩ Icc 1 N).card : ℝ) * c := by
    intro k
    unfold mass
    simp only [hwi]
    rw [sum_add_distrib, sum_ite_eq', sum_ite_mem, sum_const, nsmul_eq_mul]
  have hcardle : ∀ k, ((range k ∩ Icc 1 N).card : ℝ) ≤ N := by
    intro k
    have := card_le_card (inter_subset_right : range k ∩ Icc 1 N ⊆ Icc 1 N)
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : (range k ∩ Icc 1 N).card ≤ N)
  have hcardk : ∀ k, ((range k ∩ Icc 1 N).card : ℝ) ≤ k := by
    intro k
    have := card_le_card (inter_subset_left : range k ∩ Icc 1 N ⊆ range k)
    rw [card_range] at this
    exact_mod_cast this
  have hhead : ∀ k, (if 0 ∈ range k then (1 / 2 : ℝ) else 0) ≤ 1 / 2 := by
    intro k
    split_ifs <;> norm_num
  have hmass1 : ∀ k, mass w k ≤ 1 := by
    intro k
    rw [hmass]
    have := mul_le_mul_of_nonneg_right (hcardle k) hc0.le
    linarith [hhead k]
  have hmassk : ∀ k, mass w k ≤ 1 / 2 + k * c := by
    intro k
    rw [hmass]
    have := mul_le_mul_of_nonneg_right (hcardk k) hc0.le
    linarith [hhead k]
  have hfull : mass w (N + 1) = 1 := by
    rw [hmass, if_pos (mem_range.2 (Nat.succ_pos N))]
    have hsub : range (N + 1) ∩ Icc 1 N = Icc 1 N := by
      apply inter_eq_right.2
      intro i hi
      simp only [mem_Icc] at hi
      exact mem_range.2 (by omega)
    rw [hsub, Nat.card_Icc]
    have : ((N + 1 - 1 : ℕ) : ℝ) = N := by
      congr 1
    rw [this, hNc]
    norm_num
  refine ⟨w, 1 / 2, hnn, ?_, by norm_num, ?_, ⟨N + 1, by rw [hfull]; norm_num⟩, ?_⟩
  · -- antitone: head `1/2`, then a flat tail, then zeros
    intro i j hij
    rw [hwi, hwi]
    simp only [mem_Icc]
    split_ifs <;> (first | linarith | omega)
  · -- energy: `w_i² ≤ w_i / 2` and the mass is at most `1`
    intro k
    unfold energy
    calc ∑ i ∈ range k, w i ^ 2 ≤ ∑ i ∈ range k, w i * (1 / 2) := by
          refine sum_le_sum (fun i _ => ?_)
          rw [sq]
          exact mul_le_mul_of_nonneg_left (hle i) (hnn i)
      _ = mass w k * (1 / 2) := by rw [mass, sum_mul]
      _ ≤ 1 * (1 / 2) := mul_le_mul_of_nonneg_right (hmass1 k) (by norm_num)
      _ = 1 / 2 := by norm_num
  · -- the knee needs about `N/2` tail keys
    have hne : ({k | (3 / 4 : ℝ) ≤ mass w k} : Set ℕ).Nonempty := by
      refine ⟨N + 1, ?_⟩
      show (3 / 4 : ℝ) ≤ mass w (N + 1)
      rw [hfull]
      norm_num
    have hK : (3 / 4 : ℝ) ≤ mass w (knee w (3 / 4)) := Nat.sInf_mem hne
    have h1 := hmassk (knee w (3 / 4))
    have h2 : (1 / 4 : ℝ) ≤ (knee w (3 / 4) : ℝ) * c := by linarith
    have h3 : (N : ℝ) / 2 ≤ knee w (3 / 4) := by
      have : (N : ℝ) * c * (knee w (3 / 4) : ℝ) ≥ (N : ℝ) * (1 / 4) := by nlinarith
      rw [hNc] at this
      linarith
    have : R * ((3 / 4 : ℝ) ^ 2 / (1 / 2)) = 9 * R / 8 := by ring
    rw [this]
    linarith
