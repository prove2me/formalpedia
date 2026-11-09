-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_affine_image_comp
-- name    : Couret.InterIA.Catalogue.Quarter.Ambient.affine_image_comp
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:47.444439+00:00
-- url     : https://prove2.me/theorems/e400cbd5-e522-4521-a0a8-ba8d68d5415e
-- title:
--   affine image comp
-- statement:
--   For every natural number $n$, finite subset $S⊆ℤ/nℤ$, units $u,a$, and residues $v,b$, $(uS+v)$ mapped under $z↦az+b$ equals the image of $S$ under $z↦(au)z+(av+b)$. This includes $n=0$ and $S$ empty.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AmbientDilationLift.lean, lines 74–82; source file SHA-256 245b598d834c2a25f7b7b267060abd2116fa77a0c09833bf30949efa2e7c0a1a; theorem Couret.InterIA.Catalogue.Quarter.Ambient.affine_image_comp

import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive

theorem affine_image_comp {n : ℕ} (S : Finset (ZMod n))
    (u a : (ZMod n)ˣ) (v b : ZMod n) :
    (S.image (fun z => (u : ZMod n)*z+v)).image (fun z => (a : ZMod n)*z+b)=
      S.image (fun z => (↑(a*u) : ZMod n)*z+((a : ZMod n)*v+b)) := by sorry


end Couret.InterIA.Catalogue.Quarter.Ambient
