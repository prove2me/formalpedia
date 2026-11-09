-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_common_point_has_no_partner
-- name    : Couret.InterIA.Catalogue.Quarter.AffineCriterion.common_point_has_no_partner
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:28.745949+00:00
-- url     : https://prove2.me/theorems/ed61d04a-1c53-4810-820b-bf1a633e36e6
-- title:
--   common point has no partner
-- statement:
--   In ℤ/(4q)ℤ put A={0,q,x,x+2q}, B={0,q,x+q,x+3q}, and D={0,q,2q,3q}; these are sets, so repeated entries count once. For every positive natural q, x∈ℤ/(4q)ℤ with x∉D and z∈ℤ/(4q)ℤ with z=0 or z=q, one has z+2q∉A.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterAffineGeometry.lean, lines 31–69; source file SHA-256 4fc9cdbc6c8581db933863c792c5b7374b8c41f0609ff0ee3db720e92e88e383; theorem Couret.InterIA.Catalogue.Quarter.AffineCriterion.common_point_has_no_partner

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_quarter_ne_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_two_quarters_ne_zero
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem common_point_has_no_partner (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (z : ZMod (4*q)) (hz : z=0 ∨ z=q) :
    z+2 • (q : ZMod (4*q)) ∉ patternA q x := by sorry








end Couret.InterIA.Catalogue.Quarter.AffineCriterion
