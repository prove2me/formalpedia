-- Prove2me | solution 1 for LorentzianHardness.mem_multiIndexSet
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T07:00:17.625227+00:00
-- url     : https://prove2.me/submissions/ffa6ac38-48fa-46cb-afe3-ab325af08fd6

import Mathlib
import Definitions.Def_Bridges_NeuralCoding_LorentzianHardnessLowerBounds

open LorentzianHardness Finset BigOperators

theorem solution {n d : ℕ} {α : Fin n → ℕ} :
    α ∈ multiIndexSet n d ↔ (∀ i, α i ≤ d) ∧ ∑ i, α i = d := by
  simp only [multiIndexSet, mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨f, rfl⟩, hsum⟩
    exact ⟨fun i => Nat.lt_succ_iff.mp (f i).isLt, hsum⟩
  · rintro ⟨hle, hsum⟩
    refine ⟨⟨fun i => ⟨α i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩, hsum⟩
    ext i; simp
