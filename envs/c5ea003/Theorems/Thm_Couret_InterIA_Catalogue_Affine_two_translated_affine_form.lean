-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Affine_two_translated_affine_form
-- name    : Couret.InterIA.Catalogue.Affine.two_translated_affine_form
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:45:04.080508+00:00
-- url     : https://prove2.me/theorems/6c3e4e3a-e884-4a5b-ab9e-14b7d8a8d8b1
-- title:
--   Two translated forms become affine forms
-- statement:
--   For every positive natural $m$ and finite subsets $S,T$ of $R=\mathbb Z/(2m)\mathbb Z$, assume there are $v,x,r\in R$ with $2r=m$, $S+v=\{0,r,x,x+2r\}$ and $T+v=\{0,r,x+r,x+3r\}$. There exist a positive natural $q$ with $2m=4q$, a unit $u\in R^\times$, and $w,y\in R$ with $uS+w=\{0,q,y,y+2q\}$ and $uT+w=\{0,q,y+q,y+3q\}$. No cardinality or distinctness hypotheses are imposed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineSupportForms.lean, lines 28–51; source file SHA-256 113669caaf57f6ebef75a308ce77f0622fd86334394df6458d63f094203eafc4; theorem Couret.InterIA.Catalogue.Affine.two_translated_affine_form

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
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_two_lift_step_order
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts

theorem two_translated_affine_form (m : ℕ) (hm : 0 < m) (S T : Finset (ZMod (2*m)))
    (h : TwoTranslated m S T) : TwoAffineForm m S T := by sorry




end Couret.InterIA.Catalogue.Affine
