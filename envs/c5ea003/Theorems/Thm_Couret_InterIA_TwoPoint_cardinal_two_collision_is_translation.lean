-- Prove2me | Theorems.Thm_Couret_InterIA_TwoPoint_cardinal_two_collision_is_translation
-- name    : Couret.InterIA.TwoPoint.cardinal_two_collision_is_translation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:33:16.217298+00:00
-- url     : https://prove2.me/theorems/ff1ac20d-7cec-4e26-9acf-cb153532ba7d
-- title:
--   cardinal two collision is translation
-- statement:
--   For every abelian group $G$ with decidable equality, for every two-element finite subsets $S,T⊆G$, if their ordered-pair sum counts agree at every $z∈G$, then $S+t=T$ for some $t∈G$. There is no assertion that $2t=0$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TwoPointCollision.lean, lines 158–165; source file SHA-256 2b544e811d91074c1143be0a41817cbd978462a670ca9d6c7b39cd133d16f371; theorem Couret.InterIA.TwoPoint.cardinal_two_collision_is_translation

import Definitions.Def_Couret_TwoPointCollision_eefa36a5b454
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
import Theorems.Thm_Couret_InterIA_TwoPoint_distinct_doubles_gap
import Theorems.Thm_Couret_InterIA_TwoPoint_equal_doubles_gap
import Theorems.Thm_Couret_InterIA_TwoPoint_gap_produces_translation
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.TwoPoint
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem cardinal_two_collision_is_translation (S T : Finset G)
    (hS : S.card=2) (hT : T.card=2)
    (hsquare : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∃ t : G, S.image (fun x => x+t)=T := by sorry


end Couret.InterIA.TwoPoint
