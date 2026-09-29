-- Prove2me | solution 1 for Doppelganger.exists_lock_of_contraction_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T08:58:24.729894+00:00
-- url     : https://prove2.me/submissions/787ef2eb-eebe-44ff-a0fa-b8d79256aa36

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
open Doppelganger in
theorem solution {S I : Type*} [PseudoMetricSpace S] [Nonempty S] (δ : S → I → S) {k ε D : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (hcontract : ∀ (i : I) (s t : S), dist (δ s i) (δ t i) ≤ k * dist s t)
    (hε : 0 < ε) (hsep : ∀ s t : S, s ≠ t → ε ≤ dist s t)
    (hD : ∀ s t : S, dist s t ≤ D) :
    ∃ N : ℕ, ∀ w : List I, N ≤ w.length → Locks δ w := by
  -- each letter contracts distances by `k`
  have hdrive : ∀ (w : List I) (s t : S), dist (drive δ w s) (drive δ w t) ≤ k ^ w.length * dist s t := by
    intro w
    induction w with
    | nil => intro s t; simp [drive]
    | cons i w ih =>
      intro s t
      have h1 : drive δ (i :: w) s = drive δ w (δ s i) := rfl
      have h2 : drive δ (i :: w) t = drive δ w (δ t i) := rfl
      rw [h1, h2, List.length_cons, pow_succ]
      calc dist (drive δ w (δ s i)) (drive δ w (δ t i))
          ≤ k ^ w.length * dist (δ s i) (δ t i) := ih _ _
        _ ≤ k ^ w.length * (k * dist s t) :=
            mul_le_mul_of_nonneg_left (hcontract i s t) (pow_nonneg hk _)
        _ = k ^ w.length * k * dist s t := by ring
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hD0 : 0 ≤ D := (dist_nonneg).trans (hD s₀ s₀)
  -- pick `N` with `k^N (D + 1) < ε`
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : (0 : ℝ) < D + 1)) hk1
  refine ⟨N, fun w hw s t => ?_⟩
  by_contra hne
  have h1 := hsep _ _ hne
  have h2 := hdrive w s t
  have h3 : k ^ w.length ≤ k ^ N := pow_le_pow_of_le_one hk hk1.le hw
  have h4 : k ^ N * (D + 1) < ε := by rwa [lt_div_iff₀ (by linarith)] at hN
  have h5 : dist s t ≤ D := hD s t
  have h6 : 0 ≤ k ^ w.length := pow_nonneg hk _
  have h7 : 0 ≤ dist s t := dist_nonneg
  nlinarith
