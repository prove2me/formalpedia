-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Affine_collision_affine_forms
-- name    : Couret.InterIA.Catalogue.Affine.collision_affine_forms
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:07:51.402879+00:00
-- url     : https://prove2.me/theorems/d800cf6e-c918-4def-99a4-2a4bd389df88
-- title:
--   Affine forms of collisions
-- statement:
--   For every positive natural $m$ and four-element subsets $S,T$ of $R=\mathbb Z/(2m)\mathbb Z$, suppose their ordered-pair sum counts agree at every $z\in R$ and there are no unit $u\in R^\times$ and $v\in R$ with $uS+v=T$. There is $t\in\{0,m\}$ such that, writing $T'=T+t$, one of the following holds: there are a positive natural $q$ with $2m=4q$, a unit $u$, and $v,x\in R$ such that $uS+v=\{0,q,x,x+2q\}$ and $uT'+v=\{0,q,x+q,x+3q\}$; or there are a positive natural $q$ with $2m=8q$, a unit $u$, and $v,c,d\in R$, with $c\in\{2q,6q\}$ and $d\in\{3q,7q\}$, such that $uS+v=\{c,d,0,4q\}$ and $uT'+v=\{c,d,q,5q\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AffineFormAssembly.lean, lines 7–17; source file SHA-256 950577d51e759236cc4f563502c0e426bd57982b418ff30d743f6f7c8b79152e; theorem Couret.InterIA.Catalogue.Affine.collision_affine_forms

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
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_four_translated_affine_form
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_two_translated_affine_form
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_collision_translated_shapes
import Definitions.Def_Couret_AffineSupportForms_4a272694daca

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts Couret.InterIA.Parity

theorem collision_affine_forms (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧
      (TwoAffineForm m S (T.image (fun x => x+t)) ∨ FourAffineForm m S (T.image (fun x => x+t))) := by sorry






end Couret.InterIA.Catalogue.Affine
