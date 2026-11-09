-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_unit_quarter_sign
-- name    : Couret.InterIA.Catalogue.Quarter.Primitive.unit_quarter_sign
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:11.696807+00:00
-- url     : https://prove2.me/theorems/744a47c7-1471-4195-981d-c5161c2a071a
-- title:
--   unit quarter sign
-- statement:
--   For every integer $q>0$ and unit $u$ modulo $4q$, $uq=q$ or $uq=-q$ modulo $4q$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPrimitiveNormalisation.lean, lines 8–22; source file SHA-256 887d1f22b7114913eff0206bd9fb0b0b10e19d86cf09f8c53729d69597242304; theorem Couret.InterIA.Catalogue.Quarter.Primitive.unit_quarter_sign

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_preserves_half
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter.AffineCriterion

theorem unit_quarter_sign (q : ℕ) (hq : 0 < q) (u : (ZMod (4*q))ˣ) :
    (u : ZMod (4*q))*q=q ∨ (u : ZMod (4*q))*q= -q := by sorry










end Couret.InterIA.Catalogue.Quarter.Primitive
