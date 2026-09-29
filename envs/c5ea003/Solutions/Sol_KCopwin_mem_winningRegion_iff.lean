-- Prove2me | solution 1 for KCopwin.mem_winningRegion_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T07:00:18.977975+00:00
-- url     : https://prove2.me/submissions/ad2bb11f-9b5a-4744-bfec-178257b9dc6a

import Mathlib
import Definitions.Def_Novelty_ArgumentationKernelGame
import Definitions.Def_Novelty_KCopwinAlgorithm

open KCopwin

variable {V : Type*}

theorem solution (G : SimpleGraph V) {k : ℕ} (n : ℕ) (s : State V k) :
    s ∈ winningRegion G n ↔ CapturableWithin G n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change s ∈ winStep G (winningRegion G n) ↔ _
      simp only [winStep, CapturableWithin, Set.mem_setOf_eq]
      constructor
      · rintro (h | ⟨c', hc', hnext⟩)
        · exact Or.inl h
        · refine Or.inr ⟨c', hc', ?_⟩
          rcases hnext with h | hnext
          · exact Or.inl h
          · exact Or.inr fun r' hr' => (ih _).1 (hnext r' hr')
      · rintro (h | ⟨c', hc', hnext⟩)
        · exact Or.inl h
        · refine Or.inr ⟨c', hc', ?_⟩
          rcases hnext with h | hnext
          · exact Or.inl h
          · exact Or.inr fun r' hr' => (ih _).2 (hnext r' hr')
