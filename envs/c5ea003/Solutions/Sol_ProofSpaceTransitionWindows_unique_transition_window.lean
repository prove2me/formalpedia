-- Prove2me | solution 1 for ProofSpaceTransitionWindows.unique_transition_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:28.829612+00:00
-- url     : https://prove2.me/submissions/111eab51-d064-40b6-8a07-78df5578b49b

-- Sol generated from Logic/ProofSpaceTransitionWindows.lean
import Mathlib
import Definitions.Def_Logic_ProofSpaceTransitionWindows

/-!
# Transition Windows from Block Drift

A pointwise decrease assumption can be too rigid for cumulative proof-space
statistics.  This file replaces it by strict negative drift only at regularly
spaced block endpoints.  The resulting theorem produces a unique first sampled
crossing, proves permanence at all later sampled endpoints, and localizes the
unsampled crossing to one block of indices.
-/

open ProofSpaceTransitionWindows











open ProofSpaceTransitionWindows in
theorem solution    (f : ℕ → ℤ) (block K : ℕ)
    (hblock : ∀ k < K, f ((k + 1) * block) < f (k * block))
    (hfinal : f (K * block) ≤ 0) :
    ∃! k : ℕ, k ≤ K ∧ IsFirstSampledThreshold f block k ∧
      (∀ j, k < j → j ≤ K → f (j * block) < 0) ∧
      (0 < f 0 → 0 < k ∧
        0 < f ((k - 1) * block) ∧ f (k * block) ≤ 0) := by
  -- Define k as the first index where f(k*block) ≤ 0
  have hexists : ∃ k ≤ K, f (k * block) ≤ 0 := ⟨K, le_refl K, hfinal⟩
  -- Use well-founded recursion to find the minimum such k
  let S := {k | k ≤ K ∧ f (k * block) ≤ 0}
  have hSnonempty : S.Nonempty := ⟨K, by simp [S, hfinal]⟩
  let k := Nat.find hSnonempty
  have hk_mem : k ∈ S := Nat.find_spec hSnonempty
  have hk_le : k ≤ K := hk_mem.1
  have hk_neg : f (k * block) ≤ 0 := hk_mem.2
  -- k is the first index with f(k*block) ≤ 0, so for j < k, f(j*block) > 0
  have hfirst : ∀ j < k, 0 < f (j * block) := by
    intro j hj
    by_contra h
    push_neg at h
    have hjK : j < K := Nat.lt_of_lt_of_le hj hk_le
    have hble : j ≤ K := Nat.le_of_lt hjK
    have hjinS : j ∈ S := ⟨hble, h⟩
    exact Nat.find_min hSnonempty hj hjinS
  -- Helper: for n < m ≤ K, f(m*block) < f(n*block)
  have hdecr : ∀ n m, n < m → m ≤ K → f (m * block) < f (n * block) := by
    intro n m hnm hmK
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hnm' : n + 1 = m
      · subst hnm'; exact hblock n (by omega)
      · have hnm'' : n < m - 1 := by omega
        have hmK' : m - 1 ≤ K := by omega
        have := ih (m - 1) (by omega) hnm'' hmK'
        have hb := hblock (m - 1) (by omega)
        simp only [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hb
        exact lt_trans hb this
  -- Now prove the main result
  use k
  refine ⟨⟨hk_le, ?_, ?_, ?_⟩, ?_⟩
  -- Prove IsFirstSampledThreshold f block k
  · exact ⟨hk_neg, hfirst⟩
  -- Prove ∀ j, k < j → j ≤ K → f (j * block) < 0
  · exact fun j hkj hjK => lt_of_lt_of_le (hdecr k j hkj hjK) hk_neg
  -- Prove the conditional about k > 0
  · intro hf0
    refine ⟨?_, ?_, hk_neg⟩
    · -- k > 0
      by_contra hk0
      push_neg at hk0
      interval_cases k
      simp at hk_neg
      linarith
    · -- f ((k-1) * block) > 0
      have hkpos : 0 < k := by
        by_contra hk0
        push_neg at hk0
        interval_cases k
        simp at hk_neg
        linarith
      exact hfirst _ (Nat.sub_lt hkpos zero_lt_one)
  -- Prove uniqueness
  · intro y hy
    obtain ⟨hy_le, hy_thresh, _, _⟩ := hy
    -- y is also the first index where f(y * block) ≤ 0
    rw [IsFirstSampledThreshold] at hy_thresh
    obtain ⟨hy_neg, hy_first⟩ := hy_thresh
    -- Show y = k by antisymmetry
    apply le_antisymm
    · -- y ≤ k: if k < y, then f(k*block) > 0 by hy_first, contradicting hk_neg
      by_contra hk
      push_neg at hk
      have := hy_first k hk
      linarith
    · -- k ≤ y: if y < k, then f(y*block) > 0 by hfirst, contradicting hy_neg
      by_contra hy
      push_neg at hy
      have := hfirst y hy
      linarith
