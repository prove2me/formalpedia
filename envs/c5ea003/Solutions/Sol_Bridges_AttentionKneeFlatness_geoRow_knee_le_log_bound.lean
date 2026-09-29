-- Prove2me | solution 1 for Bridges.AttentionKneeFlatness.geoRow_knee_le_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T20:40:55.724771+00:00
-- url     : https://prove2.me/submissions/5bc9f8d2-7bd9-42bb-8728-ecc788b33d5b

import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeFlatness
import Definitions.Def_Bridges_AttentionKneeGeometry
open Finset Bridges.AttentionKneeGeometry Bridges.AttentionKneeEntropyBound Bridges.AttentionKneeFlatness in
theorem solution {a g : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hg0 : 0 ≤ g) (hg1 : g < 1) :
    (knee (geoRow a) g : ℝ) ≤ 1 + Real.log (1 - g)⁻¹ / (1 - a) := by
  -- core: the knee of a geometric row is at most `1 + log (1-g)⁻¹ / (1-a)`
  have core : ∀ a g : ℝ, 0 < a → a < 1 → 0 ≤ g → g < 1 →
      (knee (geoRow a) g : ℝ) ≤ 1 + Real.log (1 - g)⁻¹ / (1 - a) := by
    intro a g ha0 ha1 hg0 hg1
    have hmass : ∀ k, mass (geoRow a) k = 1 - a ^ k := by
      intro k
      unfold mass geoRow
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    obtain ⟨L, hL⟩ : ∃ L, L = Real.log (1 - g)⁻¹ := ⟨_, rfl⟩
    rw [← hL]
    have hlog1g : Real.log (1 - g) = -L := by rw [hL, Real.log_inv, neg_neg]
    have hL0 : 0 ≤ L := by
      have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - g) (by linarith : 1 - g ≤ 1)
      linarith
    have hla : Real.log a < 0 := Real.log_neg ha0 ha1
    obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = ⌈L / (-Real.log a)⌉₊ := ⟨_, rfl⟩
    have hk₀ge : L / (-Real.log a) ≤ k₀ := hk₀ ▸ Nat.le_ceil _
    have hk₀lt : (k₀ : ℝ) < L / (-Real.log a) + 1 :=
      hk₀ ▸ Nat.ceil_lt_add_one (div_nonneg hL0 (by linarith))
    have hpow : a ^ k₀ ≤ 1 - g := by
      have h1 : L ≤ k₀ * (-Real.log a) := by rwa [div_le_iff₀ (by linarith)] at hk₀ge
      have h2 : Real.log (a ^ k₀) ≤ Real.log (1 - g) := by
        rw [Real.log_pow, hlog1g]
        linarith
      exact (Real.log_le_log_iff (pow_pos ha0 _) (by linarith)).1 h2
    have hmem : k₀ ∈ {k | g ≤ mass (geoRow a) k} := by
      show g ≤ mass (geoRow a) k₀
      rw [hmass]
      linarith
    have hknee : knee (geoRow a) g ≤ k₀ := Nat.sInf_le hmem
    have hloga : 1 - a ≤ -Real.log a := by
      have := Real.log_le_sub_one_of_pos ha0
      linarith
    have hdiv : L / (-Real.log a) ≤ L / (1 - a) :=
      div_le_div_of_nonneg_left hL0 (by linarith) hloga
    calc (knee (geoRow a) g : ℝ) ≤ k₀ := by exact_mod_cast hknee
      _ ≤ L / (-Real.log a) + 1 := hk₀lt.le
      _ ≤ 1 + L / (1 - a) := by linarith
  exact core a g ha0 ha1 hg0 hg1
