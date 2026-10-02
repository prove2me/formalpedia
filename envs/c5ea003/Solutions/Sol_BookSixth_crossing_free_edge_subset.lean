-- Prove2me | solution 1 for BookSixth.crossing_free_edge_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T12:06:49.606399+00:00
-- url     : https://prove2.me/submissions/303a3f25-4584-4b9b-823e-8c6c51f3216b

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem solution {N M : ℕ} (D : PlaneDrawing N M) :
    ∃ E : Finset (Fin M), M ≤ E.card + D.crossings.card ∧
      ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ t s : EdgeParameter,
        0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 →
        D.arc e t ≠ D.arc f s := by
  classical
  let removed : Finset (Fin M) := D.crossings.image (fun c => c.1.1)
  let E : Finset (Fin M) := Finset.univ \ removed
  have hremoved : removed.card ≤ D.crossings.card := Finset.card_image_le
  have hcount : E.card + removed.card = M := by
    simpa [E] using
      (Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ removed))
  refine ⟨E, by omega, ?_⟩
  intro e he f hf hef t s ht0 ht1 hs0 hs1 heq
  have hen : e ∉ removed := (Finset.mem_sdiff.mp he).2
  have hfn : f ∉ removed := (Finset.mem_sdiff.mp hf).2
  rcases lt_or_gt_of_ne hef with hlt | hgt
  · have hc : ((e, f), D.arc e t) ∈ D.crossings :=
      (D.crossings_exact e f (D.arc e t)).mpr
        ⟨hlt, t, s, ht0, ht1, hs0, hs1, rfl, heq.symm⟩
    exact hen (Finset.mem_image_of_mem (fun c => c.1.1) hc)
  · have hc : ((f, e), D.arc f s) ∈ D.crossings :=
      (D.crossings_exact f e (D.arc f s)).mpr
        ⟨hgt, s, t, hs0, hs1, ht0, ht1, rfl, heq⟩
    exact hfn (Finset.mem_image_of_mem (fun c => c.1.1) hc)
