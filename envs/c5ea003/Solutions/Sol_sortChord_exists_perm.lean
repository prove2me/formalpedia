-- Prove2me | solution 1 for sortChord_exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:18:47.425242+00:00
-- url     : https://prove2.me/submissions/a804ee9e-8fb4-44bc-b799-b1ae3af773eb

import Mathlib
import Definitions.Def_Bridges_VoiceLeadingSorted
theorem solution {n : ℕ} (x : Fin n → ℤ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, sortChord x i = x (σ i) := by
  -- Mathlib's sorting permutation `Tuple.sort x` sorts the tuple monotonically
  refine ⟨Tuple.sort x, fun i => ?_⟩
  have hsorted2 : (List.ofFn (x ∘ Tuple.sort x)).SortedLE :=
    List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort x)
  have hperm2 : List.Perm (List.ofFn (x ∘ Tuple.sort x)) (List.ofFn x) :=
    Equiv.Perm.ofFn_comp_perm _ _
  -- the insertion sort used by `sortChord` is also a sorted permutation of `ofFn x`
  let R : ℤ → ℤ → Prop := fun a b => decide (a ≤ b) = true
  haveI : IsTotal ℤ R := ⟨fun a b => by simp only [R, decide_eq_true_eq]; exact le_total a b⟩
  haveI : IsTrans ℤ R := ⟨fun a b c h1 h2 => by
    simp only [R, decide_eq_true_eq] at h1 h2 ⊢; exact h1.trans h2⟩
  have hpw := List.pairwise_insertionSort R (List.ofFn x)
  have hsorted1 : (List.insertionSort R (List.ofFn x)).SortedLE :=
    (hpw.imp (fun h => by simpa [R] using h)).sortedLE
  have hperm1 := List.perm_insertionSort R (List.ofFn x)
  have heq : List.insertionSort R (List.ofFn x) = List.ofFn (x ∘ Tuple.sort x) :=
    (hperm1.trans hperm2.symm).eq_of_sortedLE hsorted1 hsorted2
  -- so the sorted chord reads off `x ∘ sort x`
  show (List.insertionSort R (List.ofFn x))[i.val]'(by simp) = x (Tuple.sort x i)
  rw [List.getElem_of_eq heq]
  simp
