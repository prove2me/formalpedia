-- Prove2me | solution 1 for ProofSpaceTransitionWindows.sampled_threshold_by_initial_imbalance
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:28.322103+00:00
-- url     : https://prove2.me/submissions/2dbadbb4-759f-46c9-bd86-1765b81d6978

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








/-- Integer-valued block descent forces at least one unit of decay per block. -/
theorem sampled_linear_decay
    (f : ℕ → ℤ) (block K : ℕ)
    (hblock : ∀ k < K, f ((k + 1) * block) < f (k * block)) :
    f (K * block) ≤ f 0 - K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 := hblock K (Nat.lt_succ_self K)
    have h2 := ih (fun k hk => hblock k (Nat.lt_of_lt_of_le hk (Nat.le_succ K)))
    have hcast : ((K + 1 : ℕ) : ℤ) = (K : ℤ) + 1 := by simp
    linarith



open ProofSpaceTransitionWindows in
theorem solution    (f : ℕ → ℤ) (block K : ℕ)
    (hblock : ∀ k < K, f ((k + 1) * block) < f (k * block))
    (hsize : f 0 ≤ K) :
    ∃ k ≤ K, IsFirstSampledThreshold f block k := by
  -- First, show f (K * block) ≤ 0 using linear decay
  have hK : f (K * block) ≤ 0 := by
    have := sampled_linear_decay f block K hblock
    linarith
  -- Use Nat.find to get the first k ≤ K with f (k * block) ≤ 0
  let k := Nat.find (⟨K, le_rfl, hK⟩ : ∃ m, m ≤ K ∧ f (m * block) ≤ 0)
  use k
  constructor
  · -- Show k ≤ K
    have hspec := Nat.find_spec (⟨K, le_rfl, hK⟩ : ∃ m, m ≤ K ∧ f (m * block) ≤ 0)
    exact hspec.1
  · -- Show IsFirstSampledThreshold f block k
    have hspec := Nat.find_spec (⟨K, le_rfl, hK⟩ : ∃ m, m ≤ K ∧ f (m * block) ≤ 0)
    constructor
    · -- f (k * block) ≤ 0
      exact hspec.2
    · -- ∀ j < k, 0 < f (j * block)
      intro j hj
      by_contra h
      push_neg at h
      -- If f (j * block) ≤ 0, then j is a valid witness with j < k
      have hk_le_K : k ≤ K := hspec.1
      have hj_le_K : j ≤ K := by linarith
      have hj_valid : j ≤ K ∧ f (j * block) ≤ 0 := ⟨hj_le_K, h⟩
      have hex : ∃ n, n ≤ K ∧ f (n * block) ≤ 0 := Exists.intro K (And.intro le_rfl hK)
      have hji : j ≤ K ∧ f (j * block) ≤ 0 := And.intro hj_le_K h
      exact Nat.find_min hex hj hji
