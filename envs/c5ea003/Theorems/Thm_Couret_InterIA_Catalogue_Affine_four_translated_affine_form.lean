-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Affine_four_translated_affine_form
-- name    : Couret.InterIA.Catalogue.Affine.four_translated_affine_form
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:59.881538+00:00
-- url     : https://prove2.me/theorems/03e2900c-7398-42d7-82c2-10d559fc0ff1
-- title:
--   four translated affine form
-- statement:
--   For every positive natural m and finite S,T⊆ℤ/(2m)ℤ, suppose there exist v,r,c,d in that ring with 4r=m, c∈{2r,6r}, d∈{3r,7r}, S+v={c,d,0,4r}, and T+v={c,d,r,5r}. Then there exist a positive natural q with 2m=8q, a unit u∈ℤ/(2m)ℤ, and v′,c′,d′ in that ring such that c′∈{2q,6q}, d′∈{3q,7q}, {u z+v′:z∈S}={c′,d′,0,4q}, and {u z+v′:z∈T}={c′,d′,q,5q}. All numerical multiples and natural numbers appearing inside sets are interpreted in the ambient ring.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineSupportForms.lean, lines 53–84; source file SHA-256 113669caaf57f6ebef75a308ce77f0622fd86334394df6458d63f094203eafc4; theorem Couret.InterIA.Catalogue.Affine.four_translated_affine_form

import Definitions.Def_Couret_AffineSupportForms_4a272694daca
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_cyclic_step_unit_normalisation
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_four_lift_step_order
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts

theorem four_translated_affine_form (m : ℕ) (hm : 0 < m) (S T : Finset (ZMod (2*m)))
    (h : FourTranslated m S T) : FourAffineForm m S T := by sorry


end Couret.InterIA.Catalogue.Affine
