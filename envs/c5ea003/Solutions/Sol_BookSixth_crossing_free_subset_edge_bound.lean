-- Prove2me | solution 1 for BookSixth.crossing_free_subset_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T22:00:38.550861+00:00
-- url     : https://prove2.me/submissions/9e3a12a8-d8b7-484d-8595-c1b0c3ab2d7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthCrossingFreeFaceData
import Theorems.Thm_BookSixth_crossing_free_face_certificate_exists

open scoped BigOperators
open BookSixth

theorem solution {N M : ℕ} (D : PlaneDrawing N M)
    (V : Finset (Fin N)) (E : Finset (Fin M))
    (hend : ∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V)
    (hfree : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ t s : EdgeParameter,
      0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 →
      D.arc e t ≠ D.arc f s) :
    E.card ≤ 3 * V.card := by
  classical
  have hcert : CrossingFreeFaceCertificate D V E :=
    crossing_free_face_certificate_exists D V E hend hfree
  rcases hcert with ⟨F, _hfaces, hEuler, hface, hedge⟩
  have hcount : F.card * 3 ≤ E.card * 2 :=
    Finset.card_mul_le_card_mul (crossingFreeFaceIncident D)
      (s := F) (t := E) hface hedge
  omega
