-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_two_quarters_ne_zero
-- name    : Couret.InterIA.Catalogue.Quarter.two_quarters_ne_zero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:31:15.164006+00:00
-- url     : https://prove2.me/theorems/d68c6b2a-2050-4d33-8a52-fbbfde2ac9ca
-- title:
--   two quarters ne zero
-- statement:
--   For every positive natural q, the residue 2q is nonzero in ℤ/(4q)ℤ.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPatterns.lean, lines 24–31; source file SHA-256 9b8c9c084f6777ce5ceb009e93059cec597e0b75776aa3c220bc02c5f8961a7b; theorem Couret.InterIA.Catalogue.Quarter.two_quarters_ne_zero

import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
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
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Catalogue.Parameters Couret.InterIA.Parity

theorem two_quarters_ne_zero (q : ℕ) (hq : 0 < q) : 2 • (q : ZMod (4*q)) ≠ 0 := by sorry
















end Couret.InterIA.Catalogue.Quarter
