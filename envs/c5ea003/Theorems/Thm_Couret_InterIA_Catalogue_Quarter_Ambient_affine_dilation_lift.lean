-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_affine_dilation_lift
-- name    : Couret.InterIA.Catalogue.Quarter.Ambient.affine_dilation_lift
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:00.458651+00:00
-- url     : https://prove2.me/theorems/266b08cd-8a6d-47c9-86ab-bf2b239790cb
-- title:
--   affine dilation lift
-- statement:
--   For every positive natural d,b, unit u∈ℤ/(4b)ℤ and v∈ℤ/(4b)ℤ, there exists a unit U∈ℤ/(4db)ℤ such that for every z∈ℤ/(4b)ℤ, D(uz+v)=U D(z)+D(v), where D(w) is the residue of d·val(w) modulo 4db and val(w) is the least nonnegative representative of w.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AmbientDilationLift.lean, lines 8–30; source file SHA-256 245b598d834c2a25f7b7b267060abd2116fa77a0c09833bf30949efa2e7c0a1a; theorem Couret.InterIA.Catalogue.Quarter.Ambient.affine_dilation_lift

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_dilate_nat
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive

theorem affine_dilation_lift (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
    (u : (ZMod (4*b))ˣ) (v : ZMod (4*b)) :
    ∃ U : (ZMod (4*(d*b)))ˣ, ∀ z : ZMod (4*b),
      dilate (4*(d*b)) d ((u : ZMod (4*b))*z+v)=
        (U : ZMod (4*(d*b)))*dilate (4*(d*b)) d z+dilate (4*(d*b)) d v := by sorry








end Couret.InterIA.Catalogue.Quarter.Ambient
