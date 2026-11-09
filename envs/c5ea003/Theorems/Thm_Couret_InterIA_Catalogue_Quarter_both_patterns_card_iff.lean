-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_both_patterns_card_iff
-- name    : Couret.InterIA.Catalogue.Quarter.both_patterns_card_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:53.311227+00:00
-- url     : https://prove2.me/theorems/f92b5b62-e1ec-4b92-89e3-771b59acd7e2
-- title:
--   Both pattern cardinalities
-- statement:
--   For every positive natural $q$ and $x\in\mathbb Z/(4q)\mathbb Z$, both $\{0,q,x,x+2q\}$ and $\{0,q,x+q,x+3q\}$ have cardinality $4$ if and only if $x\notin\{0,q,2q,3q\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPatterns.lean, lines 101–103; source file SHA-256 9b8c9c084f6777ce5ceb009e93059cec597e0b75776aa3c220bc02c5f8961a7b; theorem Couret.InterIA.Catalogue.Quarter.both_patterns_card_iff

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternA_card_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_card_iff
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Catalogue.Parameters Couret.InterIA.Parity

theorem both_patterns_card_iff (q : ℕ) (hq : 0 < q) (x : ZMod (4*q)) :
    (patternA q x).card=4 ∧ (patternB q x).card=4 ↔ x ∉ badParameters q := by sorry


end Couret.InterIA.Catalogue.Quarter
