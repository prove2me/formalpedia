-- Prove2me | solution 1 for Doppelganger.dist_drive_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:20:35.942711+00:00
-- url     : https://prove2.me/submissions/430c9e4c-d1da-4cfa-be5e-697c35d84952

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
open Doppelganger in
theorem solution {S I : Type*} [PseudoMetricSpace S] (δ : S → I → S) {k : ℝ} (hk : 0 ≤ k)
    (hcontract : ∀ (i : I) (s t : S), dist (δ s i) (δ t i) ≤ k * dist s t) (w : List I) (s t : S) :
    dist (drive δ w s) (drive δ w t) ≤ k ^ w.length * dist s t := by
  -- each input letter contracts distances by `k`
  induction w generalizing s t with
  | nil => simp [drive]
  | cons i w ih =>
    have h1 : drive δ (i :: w) s = drive δ w (δ s i) := rfl
    have h2 : drive δ (i :: w) t = drive δ w (δ t i) := rfl
    rw [h1, h2, List.length_cons, pow_succ]
    calc dist (drive δ w (δ s i)) (drive δ w (δ t i))
        ≤ k ^ w.length * dist (δ s i) (δ t i) := ih _ _
      _ ≤ k ^ w.length * (k * dist s t) :=
          mul_le_mul_of_nonneg_left (hcontract i s t) (pow_nonneg hk _)
      _ = k ^ w.length * k * dist s t := by ring
