-- Prove2me | solution 1 for mme_dwz_uniform_component_word_degree_le_fifteen_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:04:22.332762+00:00
-- url     : https://prove2.me/submissions/ad050b80-a7d2-4f44-a2d3-95678582d7d9

import Mathlib

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (L d : ℕ)
    (A T : Finset (Fin L → Fin 15))
    (same : (Fin L → Fin 15) → (Fin L → Fin 15) → Prop)
    [DecidableRel same]
    (hTA : T ⊆ A) (hT : T.Nonempty)
    (hdegree : ∀ a ∈ A, (A.filter (fun b ↦ same b a)).card = d) :
    d ≤ 15 ^ L := by
  obtain ⟨a, haT⟩ := hT
  have haA : a ∈ A := hTA haT
  rw [← hdegree a haA]
  calc
    (A.filter (fun b ↦ same b a)).card ≤ A.card := Finset.card_filter_le _ _
    _ ≤ Fintype.card (Fin L → Fin 15) := A.card_le_univ
    _ = 15 ^ L := by simp
