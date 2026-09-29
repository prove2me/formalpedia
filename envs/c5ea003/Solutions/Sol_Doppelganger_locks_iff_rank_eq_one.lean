-- Prove2me | solution 1 for Doppelganger.locks_iff_rank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:52:16.218777+00:00
-- url     : https://prove2.me/submissions/55c8dbaf-b63a-4b31-a5ae-3bea95b33f10

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite

open Doppelganger

variable {S I : Type*} [Fintype S] [DecidableEq S]

theorem solution [Nonempty S] (δ : S → I → S) (w : List I) :
    Locks δ w ↔ rank δ w = 1 := by
  constructor
  · intro h
    -- Image is a singleton, hence card 1
    obtain ⟨s0⟩ := ‹Nonempty S›
    have himg : (Finset.univ.image (drive δ w)) = {drive δ w s0} := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨s, rfl⟩
        exact h s s0
      · rintro rfl
        exact ⟨s0, rfl⟩
    simp [rank, himg]
  · intro hrank s t
    -- card image = 1 and both drive values are in the image ⇒ equal
    have hs : drive δ w s ∈ Finset.univ.image (drive δ w) := by
      simp
    have ht : drive δ w t ∈ Finset.univ.image (drive δ w) := by
      simp
    have hcard := hrank
    -- Finset.card_eq_one ⇒ ∃ a, s = {a}
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by simpa [rank] using hcard)
    have hs' : drive δ w s = a := by
      have : drive δ w s ∈ ({a} : Finset S) := by simpa [ha] using hs
      simpa using this
    have ht' : drive δ w t = a := by
      have : drive δ w t ∈ ({a} : Finset S) := by simpa [ha] using ht
      simpa using this
    exact hs'.trans ht'.symm
