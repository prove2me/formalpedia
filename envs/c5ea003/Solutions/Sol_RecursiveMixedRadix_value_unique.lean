-- Prove2me | solution 1 for RecursiveMixedRadix.value_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:46:41.688924+00:00
-- url     : https://prove2.me/submissions/f9cd7226-2d3f-431a-bbfc-ab3e5a112993

-- Sol generated from NumberTheory/RecursiveMixedRadix.lean
import Mathlib
import Definitions.Def_NumberTheory_RecursiveMixedRadix
import Theorems.Thm_RecursiveMixedRadix_splitting_div

/-!
# Recursive mixed-radix representations

This file isolates the general mixed-radix mechanism behind factoradics and
recursive-base systems.  A radix sequence `r` determines place values
`weight r 0 = 1` and `weight r (k+1) = r k * weight r k`.

The main results prove, constructively and without cardinality arguments, that
valid length-`k` digit strings represent exactly the naturals below
`weight r k`, and do so uniquely.
-/

open RecursiveMixedRadix

open Finset







@[simp] theorem value_zero (r c : ℕ → ℕ) : value r c 0 = 0 := by
  simp [value]

theorem value_succ (r c : ℕ → ℕ) (k : ℕ) :
    value r c (k + 1) = value r c k + c k * weight r k := by
  simp [value, Finset.sum_range_succ]










open RecursiveMixedRadix in
theorem solution{r c d : ℕ → ℕ} (hr : ∀ i, 0 < r i) {k : ℕ}
    (hc : Valid r c k) (hd : Valid r d k)
    (hv : value r c k = value r d k) : ∀ i < k, c i = d i := by
  -- Key lemma: if c and d agree on all j < i, then value r c i = value r d i
  have agree_implies_value : ∀ i, (∀ j < i, c j = d j) → value r c i = value r d i := by
    intro i hagree
    induction i with
    | zero => simp [value_zero]
    | succ i ih => 
      have hci_di : c i = d i := hagree i (Nat.lt_succ_self i)
      have hvic : value r c i = value r d i := ih (fun j hj => hagree j (Nat.lt_succ_of_lt hj))
      rw [value_succ, value_succ, hvic, hci_di]
  -- Now prove the main result by contradiction
  by_contra hne
  push_neg at hne
  obtain ⟨i, hi_lt, hi_ne⟩ := hne
  -- Take the largest index where they differ
  have hne_set : (Finset.filter (fun j => j < k ∧ c j ≠ d j) (Finset.range (k + 1))).Nonempty := by
    use i
    simp [hi_lt, hi_ne]
    omega
  let m := Finset.max' _ hne_set
  have hm_mem : m < k ∧ c m ≠ d m := by
    have h := Finset.mem_filter.mp (Finset.max'_mem _ hne_set)
    simp only [Finset.mem_range] at h
    exact ⟨h.2.1, h.2.2⟩
  -- All indices j with m < j < k have c j = d j
  have hm_max : ∀ j, m < j → j < k → c j = d j := by
    intro j hj_lt hj_lt_k
    by_contra hne_j
    have hj_mem : j ∈ Finset.filter (fun j => j < k ∧ c j ≠ d j) (Finset.range (k + 1)) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hj_lt_k, hne_j⟩
    have hj_le_m : j ≤ m := Finset.le_max' _ _ hj_mem
    exact absurd hj_lt (not_lt.mpr hj_le_m)
  -- value r c k = value r d k, and they agree on indices m+1 to k-1
  -- So value r c (m+1) = value r d (m+1)
  -- Use splitting_mod: value r c (m+1) = value r c k % weight r (m+1)
  -- and the sum over [m+1, k) is the same for both
  have hval_m1_eq : value r c (m + 1) = value r d (m + 1) := by
    -- value r c k = value r c (m+1) + sum over [m+1, k)
    have hck : m + 1 ≤ k := by omega
    have hcalc_c : value r c k = value r c (m + 1) + ∑ j ∈ Ico (m + 1) k, c j * weight r j := by
      rw [value, value, ← Finset.sum_range_add_sum_Ico _ hck]
    have hcalc_d : value r d k = value r d (m + 1) + ∑ j ∈ Ico (m + 1) k, d j * weight r j := by
      rw [value, value, ← Finset.sum_range_add_sum_Ico _ hck]
    have hsum_eq : ∑ j ∈ Ico (m + 1) k, c j * weight r j = ∑ j ∈ Ico (m + 1) k, d j * weight r j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hm_max j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2]
    rw [hcalc_c, hcalc_d, hsum_eq] at hv
    omega
  -- By splitting_div, c m = value r c (m+1) / weight r m = value r d (m+1) / weight r m = d m
  have hcm : value r c (m + 1) / weight r m = c m := splitting_div hr (fun i hi => hc i (by omega))
  have hdm : value r d (m + 1) / weight r m = d m := splitting_div hr (fun i hi => hd i (by omega))
  rw [hval_m1_eq] at hcm
  rw [hcm] at hdm
  exact hm_mem.2 hdm
