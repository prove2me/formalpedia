-- Prove2me | solution 1 for BookSixth.round_circle_prefix_standardize_preserves_appended_roundness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T08:08:26.591472+00:00
-- url     : https://prove2.me/submissions/e28af985-e581-4615-91e0-97f52c2d9248
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_isUnlink_pair_of_isUnlink_v1
import Theorems.Thm_BookSixth_isUnlink_pair_swap
import Theorems.Thm_BookSixth_perfect_circles_pairwise_unlinked_motion

open scoped BigOperators
open BookSixth

theorem solution {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
    (hroundC : ∀ i, RoundCircle (C i)) (hroundD : RoundCircle D)
    (hdisjointC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hdisjointD : ∀ i, Disjoint (C i) D)
    (hprefix : IsUnlink C)
    (hpairs : ∀ i, IsUnlink (![C i, D] : Fin 2 → Set Space3)) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (∀ i, (K 1) '' C i = standardCircle i.val) ∧
      RoundCircle (K 1 '' D) := by
  let E : Fin (n + 1) → Set Space3 := Fin.snoc C D
  have hE : ∀ i, RoundCircle (E i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [E] using hroundD
    · simpa [E] using hroundC j
  have hEdisjoint : ∀ i j : Fin (n + 1), i ≠ j →
      Disjoint (E i) (E j) := by
    intro i j hij
    rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
    · rcases j.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
      · have hne : i ≠ j := by
          intro h
          apply hij
          exact congrArg Fin.castSucc h
        simpa [E] using hdisjointC i j hne
      · simpa [E] using hdisjointD i
    · rcases j.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
      · simpa [E] using Disjoint.symm (hdisjointD j)
      · exact (hij rfl).elim
  have hEpairs : ∀ i j : Fin (n + 1), i ≠ j →
      IsUnlink (![E i, E j] : Fin 2 → Set Space3) := by
    intro i j hij
    rcases i.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
    · rcases j.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
      · have hne : i ≠ j := by
          intro h
          apply hij
          exact congrArg Fin.castSucc h
        simpa [E] using
          BookSixth.isUnlink_pair_of_isUnlink_v1
            (C := C) hprefix i j hne
      · simpa [E] using hpairs i
    · rcases j.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
      · simpa [E] using BookSixth.isUnlink_pair_swap (hpairs j)
      · exact (hij rfl).elim
  obtain ⟨K, hK1, hK2, hK0, hKold, hKround⟩ :=
    BookSixth.perfect_circles_pairwise_unlinked_motion
      (C := E) hE hEdisjoint hEpairs
  refine ⟨K, hK1, hK2, hK0, ?_, ?_⟩
  · intro i
    simpa [E] using hKold (Fin.castSucc i)
  · simpa [E] using hKround 1 (Fin.last n)
