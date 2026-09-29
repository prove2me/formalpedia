-- Prove2me | solution 1 for sortChord_perm_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:26:20.014813+00:00
-- url     : https://prove2.me/submissions/a2ba788c-fbcf-4357-b50b-ed03a613b966

import Mathlib
import Definitions.Def_Bridges_VoiceLeadingSorted
theorem solution {n : ℕ} (x : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
    sortChord (fun i => x (σ i)) = sortChord x := by
  let R : ℤ → ℤ → Prop := fun a b => decide (a ≤ b) = true
  haveI : IsTotal ℤ R := ⟨fun a b => by simp only [R, decide_eq_true_eq]; exact le_total a b⟩
  haveI : IsTrans ℤ R := ⟨fun a b c h1 h2 => by
    simp only [R, decide_eq_true_eq] at h1 h2 ⊢; exact h1.trans h2⟩
  -- insertion sort returns a sorted permutation
  have hsorted : ∀ l : List ℤ, (List.insertionSort R l).SortedLE := fun l =>
    ((List.pairwise_insertionSort R l).imp (fun h => by simpa [R] using h)).sortedLE
  -- the two inputs are permutations of each other, so the sorted outputs coincide
  have hperm : List.Perm (List.ofFn (fun i => x (σ i))) (List.ofFn x) :=
    Equiv.Perm.ofFn_comp_perm σ x
  have heq : List.insertionSort R (List.ofFn (fun i => x (σ i))) = List.insertionSort R (List.ofFn x) :=
    (((List.perm_insertionSort R _).trans hperm).trans (List.perm_insertionSort R _).symm).eq_of_sortedLE
      (hsorted _) (hsorted _)
  funext i
  show (List.insertionSort R (List.ofFn (fun i => x (σ i))))[i.val]'(by simp)
    = (List.insertionSort R (List.ofFn x))[i.val]'(by simp)
  exact List.getElem_of_eq heq _
