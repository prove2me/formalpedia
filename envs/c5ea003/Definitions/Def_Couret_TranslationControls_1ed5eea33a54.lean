-- Prove2me | Definitions.Def_Couret_TranslationControls_1ed5eea33a54
-- name    : Couret_TranslationControls_1ed5eea33a54
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:28.478048+00:00
-- url     : https://prove2.me/theorems/3991beb3-4164-4cdd-af7d-faa3599bcb55
-- title:
--   Ordered-square counts under translation
-- statement:
--   This support bundle supplies the finite-set translation identities for ordered sums, including the shift of a square count by twice the translation. For an abelian group, translating $S$ by $u$ moves each ordered pair sum by $2u$. These lemmas provide the algebraic control needed when comparing normalized and translated collision supports.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TranslationControls.lean; source file SHA-256 c764285724771fcbb1b02517caf13fbb761d34a18fd72c778c87d1496e10d81a

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_TwoPointCollision_eefa36a5b454

set_option autoImplicit false
namespace Couret.InterIA.Translation
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem ordered_square_translate (S : Finset G) (t z : G) :
    orderedSquare (S.image (fun x => x+t)) z = orderedSquare S (z-(t+t)) := by
  unfold orderedSquare
  rw [Finset.sum_image (fun a _ b _ he => add_right_cancel he)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_image (fun b _ c _ he => add_right_cancel he)]
  apply Finset.sum_congr rfl
  intro b hb
  have he : (a+t)+(b+t)=z ↔ a+b=z-(t+t) := by
    constructor
    · intro hz
      calc a+b = ((a+t)+(b+t))-(t+t) := by abel
           _ = z-(t+t) := by rw [hz]
    · intro hz
      calc (a+t)+(b+t) = (a+b)+(t+t) := by abel
           _ = (z-(t+t))+(t+t) := by rw [hz]
           _ = z := by abel
  simp only [he]

theorem two_torsion_translation_preserves_square (S : Finset G) (t : G)
    (ht : t+t=0) (z : G) :
    orderedSquare (S.image (fun x => x+t)) z = orderedSquare S z := by
  rw [ordered_square_translate, ht, sub_zero]

end Couret.InterIA.Translation


