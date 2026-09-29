-- Prove2me | solution 1 for UnitalMagmaDefect.ShiftMagma.defectSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:29:39.451172+00:00
-- url     : https://prove2.me/submissions/09fa1357-7764-40c8-a47b-adc4e6f8bde5

import Mathlib
import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
import Definitions.Def_Combinatorics_UnitalMagmaDefect
universe u
open UnitalMagmaDefect UnitalMagmaDefect.ShiftMagma Finset in
theorem solution {M : Type u} [Mul M] [Fintype M] [DecidableEq M]
    (hcomm : ∀ a b : M, a * b = b * a)
    {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]
    (hl : ∀ a : M, (1 : M) * a = a) (hr : ∀ a : M, a * (1 : M) = a)
    {S : Type u} {σ : S → S} [Fintype S] [DecidableEq S] (hσ : ∀ x, σ x ≠ x) :
    defectSet (ShiftMagma σ) =
      (univ.erase (1 : ShiftMagma σ)) ×ˢ
        ((univ.erase (1 : ShiftMagma σ)) ×ˢ (univ.erase (1 : ShiftMagma σ))) := by
  ext ⟨x, y, z⟩
  simp only [defectSet, mem_filter, mem_univ, true_and, mem_product, mem_erase, and_true]
  -- a triple involving the unit associates; three non-units never do
  rcases x with _ | a <;> rcases y with _ | b <;> rcases z with _ | c
  · exact iff_of_false (fun h => h rfl) (fun h => h.1 rfl)
  · exact iff_of_false (fun h => h rfl) (fun h => h.1 rfl)
  · exact iff_of_false (fun h => h rfl) (fun h => h.1 rfl)
  · exact iff_of_false (fun h => h rfl) (fun h => h.1 rfl)
  · exact iff_of_false (fun h => h rfl) (fun h => h.2.1 rfl)
  · exact iff_of_false (fun h => h rfl) (fun h => h.2.1 rfl)
  · exact iff_of_false (fun h => h rfl) (fun h => h.2.2 rfl)
  · refine iff_of_true (fun h => hσ (σ c) ?_)
      ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    exact (Option.some.inj (h : (some (σ c) : Option S) = some (σ (σ c)))).symm
