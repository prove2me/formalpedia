-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternB_dilate
-- name    : Couret.InterIA.Catalogue.Quarter.Primitive.patternB_dilate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:45:29.536477+00:00
-- url     : https://prove2.me/theorems/3a2ad27e-1f61-4a63-96f0-14f475d6039b
-- title:
--   patternB dilate
-- statement:
--   For all natural d,b,a with d>0, map ℤ/(4b)ℤ to ℤ/(4db)ℤ by w↦d·val(w), reduced in the target. The image of the finite set {0,b,a+b,a+3b} in the source is exactly {0,db,da+db,da+3db} in the target. Repeated elements count once. The case b=0 is included; both rings are then ℤ and val(w) is the natural absolute value of the integer w.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPrimitiveReduction.lean, lines 43–54; source file SHA-256 04116ba5236184358d50490faa8000ec249e62fb1c5665b6d82deee453cd3c82; theorem Couret.InterIA.Catalogue.Quarter.Primitive.patternB_dilate

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
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem patternB_dilate (d b a : ℕ) (hd : 0 < d) :
    (patternB b (a : ZMod (4*b))).image (dilate (4*(d*b)) d)=
      patternB (d*b) (d*a : ℕ) := by sorry






end Couret.InterIA.Catalogue.Quarter.Primitive
