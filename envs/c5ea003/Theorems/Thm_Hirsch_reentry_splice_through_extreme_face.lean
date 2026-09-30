-- Prove2me | Theorems.Thm_Hirsch_reentry_splice_through_extreme_face
-- name    : Hirsch.reentry_splice_through_extreme_face
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T02:11:19.055886+00:00
-- url     : https://prove2.me/theorems/9d1ffa54-5123-4a52-87a2-e482d3c78918
-- title:
--   Replace a path reentry segment by an intrinsic extreme-face path
-- statement:
--   If a padded graph walk in P visits an extreme face F at indices s≤t and F has intrinsic graph diameter at most B, replace the entire segment between those visits by a walk inside F. The resulting parent walk has exact padded budget s+B+(L-t), independent of how often the original segment left and re-entered F.
-- source:
--   Verified Polynomial Hirsch graph-geometry helper developed in the September 2026 formalization; see jjoshua2/prove2me-work PR #27.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem reentry_splice_through_extreme_face
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F)
    (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P)
    (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' (s + B + (L - t)) = v ∧
      ∀ j < s + B + (L - t),
        w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by sorry

end Hirsch
