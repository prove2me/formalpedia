-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Lifts_collision_translated_shapes
-- name    : Couret.InterIA.Catalogue.Lifts.collision_translated_shapes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:20.174769+00:00
-- url     : https://prove2.me/theorems/6b042b08-c16f-4847-af03-a9c3bc5ce848
-- title:
--   Translated shapes of collisions
-- statement:
--   For every positive natural $m$ and four-element subsets $S,T$ of $R=\mathbb Z/(2m)\mathbb Z$ with equal ordered-pair sum counts at every element and no unit $u$, element $v$ satisfying $uS+v=T$, there is $t\in\{0,m\}$ such that, for $T'=T+t$, either there exist $v,x,r\in R$ with $2r=m$, $S+v=\{0,r,x,x+2r\}$ and $T'+v=\{0,r,x+r,x+3r\}$, or there exist $v,r,c,d\in R$ with $4r=m$, $c\in\{2r,6r\}$, $d\in\{3r,7r\}$, $S+v=\{c,d,0,4r\}$ and $T'+v=\{c,d,r,5r\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/OrbitLiftAssembly.lean, lines 32–42; source file SHA-256 5c80300fa2224d4f90652ce0604aca6fbf4e62f95e2e424719b4c229b06344d9; theorem Couret.InterIA.Catalogue.Lifts.collision_translated_shapes

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_four_lift_translation
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_four_orbit_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_two_lift_translation
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_two_orbit_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Orbits_collision_orbit_shapes
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.Catalogue.Orbits Couret.InterIA.Parity

theorem collision_translated_shapes (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧
      (TwoTranslated m S (T.image (fun x => x+t)) ∨ FourTranslated m S (T.image (fun x => x+t))) := by sorry


end Couret.InterIA.Catalogue.Lifts
