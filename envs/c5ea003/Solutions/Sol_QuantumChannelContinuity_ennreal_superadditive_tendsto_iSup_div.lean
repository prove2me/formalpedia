-- Prove2me | solution 1 for QuantumChannelContinuity.ennreal_superadditive_tendsto_iSup_div
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T18:23:49.244985+00:00
-- url     : https://prove2.me/submissions/91d20bb7-ea39-48ad-824a-34e2ea716940

import Mathlib.Analysis.Subadditive
import Mathlib.Topology.Instances.ENNReal.Lemmas
/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Fekete's lemma with infinite values retained

Nonnegative superadditive block quantities converge after normalization to
their positive-block supremum, whether that supremum is finite or infinite.
-/

open Filter Set
open scoped ENNReal Topology
namespace QuantumChannelContinuity

/-- Nonnegative superadditivity implies monotonicity in the block length. -/
theorem ennreal_monotone_of_superadditive (f : ℕ → ℝ≥0∞)
    (hf : ∀ m n, f m + f n ≤ f (m + n)) : Monotone f := by
  intro m n hmn
  calc
    f m ≤ f m + f (n - m) := le_add_of_nonneg_right bot_le
    _ ≤ f (m + (n - m)) := hf _ _
    _ = f n := by rw [Nat.add_sub_of_le hmn]

end QuantumChannelContinuity

open QuantumChannelContinuity in
/-- Full extended-real Fekete convergence, including an infinite supremum
and sequences with an infinite individual term. -/
theorem solution (f : ℕ → ℝ≥0∞)
    (hf : ∀ m n, f m + f n ≤ f (m + n)) :
    Tendsto (fun n : ℕ => f n / (n : ℝ≥0∞)) atTop
      (𝓝 (⨆ n : ℕ, ⨆ (_ : 0 < n), f n / (n : ℝ≥0∞))) := by
  classical
  have hmono := ennreal_monotone_of_superadditive f hf
  by_cases hfin : ∀ n, f n ≠ ⊤
  · let u : ℕ → ℝ := fun n => -(f n).toReal
    have hu : Subadditive u := by
      intro m n
      have h := ENNReal.toReal_mono (hfin (m + n)) (hf m n)
      rw [ENNReal.toReal_add (hfin m) (hfin n)] at h
      dsimp [u]
      linarith
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨n, hna⟩ := lt_iSup_iff.mp ha
      obtain ⟨hn, han⟩ := lt_iSup_iff.mp hna
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
      have hquot := ENNReal.div_ne_top (hfin n) hn0
      have har : a.toReal < (f n).toReal / (n : ℝ) := by
        have h := (ENNReal.toReal_lt_toReal han.ne_top hquot).mpr han
        simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast] using h
      have hstart : u n / (n : ℝ) < -a.toReal := by
        dsimp [u]
        rw [neg_div]
        linarith
      have hev := hu.eventually_div_lt_of_div_lt hn.ne' hstart
      filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with k hk hkpos
      have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hkpos.ne'
      apply (ENNReal.toReal_lt_toReal han.ne_top (ENNReal.div_ne_top (hfin k) hk0)).mp
      simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
      dsimp [u] at hk
      rw [neg_div] at hk
      linarith
    · intro a ha
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hb : f n / (n : ℝ≥0∞) ≤
          ⨆ k : ℕ, ⨆ (_ : 0 < k), f k / (k : ℝ≥0∞) :=
        le_iSup_of_le n (le_iSup_of_le hn le_rfl)
      exact hb.trans_lt ha
  · push_neg at hfin
    obtain ⟨n, hn⟩ := hfin
    have htop (k : ℕ) (hk : n ≤ k) : f k = ⊤ := by
      apply top_unique
      simpa only [hn] using hmono hk
    have hs : (⨆ k : ℕ, ⨆ (_ : 0 < k), f k / (k : ℝ≥0∞)) = ⊤ := by
      apply top_unique
      have hle : f (n + 1) / ((n + 1 : ℕ) : ℝ≥0∞) ≤
          ⨆ k : ℕ, ⨆ (_ : 0 < k), f k / (k : ℝ≥0∞) :=
        le_iSup_of_le (n + 1) (le_iSup_of_le (Nat.succ_pos n) le_rfl)
      simpa only [htop (n + 1) (Nat.le_succ n), ENNReal.top_div,
        ENNReal.natCast_ne_top, ↓reduceIte] using hle
    rw [hs]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with k hk
    simp only [htop k hk, ENNReal.top_div, ENNReal.natCast_ne_top, ↓reduceIte]


