-- Prove2me | solution 1 for BookSixth.round_circle_snoc_transport
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T08:29:56.318817+00:00
-- url     : https://prove2.me/submissions/8677a48e-0bd3-47d0-a4d7-9b973b88aa48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_isUnlink_path_image
import Theorems.Thm_BookSixth_round_circle_prefix_standardize_preserves_appended_roundness
import Theorems.Thm_BookSixth_round_circle_single_standardize_link_preserving_v3
import Theorems.Thm_BookSixth_round_circle_snoc_transport_compose_v4

open scoped BigOperators
open BookSixth

theorem solution {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
    (hroundC : ∀ i, RoundCircle (C i)) (hroundD : RoundCircle D)
    (hdisjointC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hdisjointD : ∀ i, Disjoint (C i) D)
    (hprefix : IsUnlink C)
    (hpairs : ∀ i, IsUnlink (![C i, D] : Fin 2 → Set Space3)) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ i, (H 1) '' C i = standardCircle i.val) ∧
      (H 1) '' D = standardCircle n := by
  obtain ⟨K, hKf, hKi, hK0, hKold, hKround⟩ :=
    round_circle_prefix_standardize_preserves_appended_roundness
      C D hroundC hroundD hdisjointC hdisjointD hprefix hpairs
  have htransportedPairs :
      ∀ i, IsUnlink (![K 1 '' C i, K 1 '' D] : Fin 2 → Set Space3) := by
    intro i
    have hpair : (fun j : Fin 2 => K 1 '' ![C i, D] j) =
        ![K 1 '' C i, K 1 '' D] := by
      funext j
      fin_cases j <;> rfl
    simpa only [hpair] using
      (BookSixth.isUnlink_path_image
        (C := ![C i, D]) K ⟨hKf, hKi, hK0⟩ (hpairs i))
  have hstandardPairs :
      ∀ i : Fin n, IsUnlink (![standardCircle i.val, K 1 '' D] : Fin 2 → Set Space3) := by
    intro i
    simpa [hKold i] using htransportedPairs i
  obtain ⟨G, hGf, hGi, hG0, hGnew, hGpres⟩ :=
    round_circle_single_standardize_link_preserving_v3
      (n := n) (D := K 1 '' D) hKround
      (by
        intro i hi
        exact hstandardPairs ⟨i, hi⟩)
  have hGprefix : ∀ i : Fin n,
      (G 1) '' standardCircle i.val = standardCircle i.val := by
    intro i
    exact hGpres 1 i.val i.isLt
  exact round_circle_snoc_transport_compose_v4
    C D K G ⟨hKf, hKi, hK0⟩ ⟨hGf, hGi, hG0⟩
    hKold hGnew hGprefix
