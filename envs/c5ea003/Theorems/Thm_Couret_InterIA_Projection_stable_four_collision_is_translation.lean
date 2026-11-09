-- Prove2me | Theorems.Thm_Couret_InterIA_Projection_stable_four_collision_is_translation
-- name    : Couret.InterIA.Projection.stable_four_collision_is_translation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:51.013749+00:00
-- url     : https://prove2.me/theorems/4729a4e1-35fd-492c-884a-fcceb397f0b4
-- title:
--   stable four collision is translation
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. For every positive natural m and finite S,T⊆ℤ/(2m)ℤ with |S|=|T|=4, if x+m∈S for every x∈S, x+m∈T for every x∈T, and Q(S,z)=Q(T,z) for every z, then there exists u∈ℤ/(2m)ℤ such that {x+u:x∈S}=T.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/StableProjection.lean, lines 186–196; source file SHA-256 6ce8aa246312a4979a5fa5cefe9a796e2df61ddcdc38e08f0109e9e007cd5feb; theorem Couret.InterIA.Projection.stable_four_collision_is_translation

import Definitions.Def_Couret_StableProjection_78f7ee270976
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Projection_quotient_translation_lifts
import Theorems.Thm_Couret_InterIA_TwoPoint_cardinal_two_collision_is_translation
import Definitions.Def_Couret_MixedGeometry_fb699ea460d2
import Definitions.Def_Couret_IntersectionTwo_2d7b2419466c
import Mathlib.Algebra.MonoidAlgebra.MapDomain

set_option autoImplicit false
namespace Couret.InterIA.Projection
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.GroupRing

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem stable_four_collision_is_translation (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hSs : ∀ x ∈ S, x+m ∈ S) (hTs : ∀ x ∈ T, x+m ∈ T)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∃ u : ZMod (2*m), S.image (fun x => x+u)=T := by sorry


end Couret.InterIA.Projection
