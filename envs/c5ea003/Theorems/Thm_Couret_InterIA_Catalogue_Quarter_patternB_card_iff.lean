-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_card_iff
-- name    : Couret.InterIA.Catalogue.Quarter.patternB_card_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:53.341637+00:00
-- url     : https://prove2.me/theorems/51f2aa49-a0d9-4f36-92f6-ad93c9be7ed6
-- title:
--   patternB card iff
-- statement:
--   For every integer $q>0$ and residue $x∈ℤ/(4q)ℤ$, the set $\{0,q,x+q,x+3q\}$ has cardinality $4$ if and only if $x∉\{0,q,2q,3q\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPatterns.lean, lines 97–99; source file SHA-256 9b8c9c084f6777ce5ceb009e93059cec597e0b75776aa3c220bc02c5f8961a7b; theorem Couret.InterIA.Catalogue.Quarter.patternB_card_iff

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_shift_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternA_card_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_as_shifted_A
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Catalogue.Parameters Couret.InterIA.Parity

theorem patternB_card_iff (q : ℕ) (hq : 0 < q) (x : ZMod (4*q)) :
    (patternB q x).card=4 ↔ x ∉ badParameters q := by sorry




end Couret.InterIA.Catalogue.Quarter
