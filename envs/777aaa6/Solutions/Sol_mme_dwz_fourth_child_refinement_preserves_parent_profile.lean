-- Prove2me | solution 1 for mme_dwz_fourth_child_refinement_preserves_parent_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:47:34.382588+00:00
-- url     : https://prove2.me/submissions/24ab3875-45db-4a03-9aad-5327cbbe7a9c

import Definitions.Def_mme_dwz_fourth_child_coordinate_join_data

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.CoupledParentCompatibility
universe u
set_option autoImplicit false

theorem solution (q : ℕ) (L : Fin 9)
    (p : IntegerZSplitProfile 5) (m : ℕ)
    (kLeft kRight : Fin (p.length m) → Fin 5)
    (hsum : ∀ r, (kLeft r).val + (kRight r).val = L.val)
    (x x' : (r : Fin (p.length m)) → LiftedCoarsePair.{u} q (kLeft r))
    (y y' : (r : Fin (p.length m)) → LiftedCoarsePair.{u} q (kRight r)) :
    let w := packWord (p.length m) (fun r =>
      joinCoords q L (kLeft r) (kRight r) (hsum r) (x r) (y r))
    let w' := packWord (p.length m) (fun r =>
      joinCoords q L (kLeft r) (kRight r) (hsum r) (x' r) (y' r))
    (prescribedZWord fourthLeftGrade p m w ↔
      ∀ a : Fin 5, (Finset.univ.filter (fun r => kLeft r = a)).card = p.count a * m) ∧
    (prescribedZWord fourthLeftGrade p m w ↔
      prescribedZWord fourthLeftGrade p m w') := by
  dsimp only
  constructor
  · unfold prescribedZWord leftGradeCount
    simp only [get_packWord, joined_left_grade]
  · unfold prescribedZWord leftGradeCount
    simp only [get_packWord, joined_left_grade]

