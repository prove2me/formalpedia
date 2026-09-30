-- Prove2me | solution 1 for FourColor.minimal_counterexample_exists
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-29T23:55:57.196616+00:00
-- url     : https://prove2.me/submissions/25677a1b-71c4-4da6-ac41-68bc750d3078

import Definitions.Def_FourColor_Hypermap
import Mathlib.Data.Nat.Find

open FourColor

-- Minimize over the full admissible precubic class, without structural assumptions.
theorem solution :
    ∀ (n : ℕ) (H : Hypermap n), H.Admissible → ¬ H.FourColorable →
      ∃ (m : ℕ) (K : Hypermap m), m ≤ n ∧ K.MinimalCounterexample := by
  classical
  intro n H hH hn
  let bad : ℕ → Prop := fun m ↦ ∃ K : Hypermap m, K.Admissible ∧ ¬ K.FourColorable
  have exists_bad : ∃ m, bad m := ⟨n, H, hH, hn⟩
  obtain ⟨K, hK, hnot⟩ := Nat.find_spec exists_bad
  refine ⟨Nat.find exists_bad, K, Nat.find_min' exists_bad ⟨H, hH, hn⟩,
    ⟨hK, hnot, ?_⟩⟩
  intro m hm L hL
  by_contra hnotL
  exact Nat.find_min exists_bad hm ⟨L, hL, hnotL⟩
