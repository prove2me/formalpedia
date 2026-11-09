-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_patterns_collision
-- name    : Couret.InterIA.Catalogue.Quarter.admissible_patterns_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:30.791547+00:00
-- url     : https://prove2.me/theorems/a8ec97ea-4ee8-4dfa-9ce4-7270671fdd80
-- title:
--   admissible patterns collision
-- statement:
--   In ℤ/(4q)ℤ put A={0,q,x,x+2q}, B={0,q,x+q,x+3q}, and D={0,q,2q,3q}; these are sets, so repeated entries count once. For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. For every positive natural q and x∈ℤ/(4q)ℤ with x∉D, Q(A,z)=Q(B,z) for every z∈ℤ/(4q)ℤ.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPatternConverse.lean, lines 32–56; source file SHA-256 41da6cd22f81baaf77052df26dcf8825ae5a0546a46be6b741b1b68fdb82f147; theorem Couret.InterIA.Catalogue.Quarter.admissible_patterns_collision

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_pair_separations
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_shift_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_as_shifted_A
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_quarter_ne_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_two_quarters_ne_zero
import Theorems.Thm_Couret_InterIA_IntersectionTwo_pp_actual_square_iff
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo

theorem admissible_patterns_collision (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) :
    ∀ z, orderedSquare (patternA q x) z=orderedSquare (patternB q x) z := by sorry




end Couret.InterIA.Catalogue.Quarter
