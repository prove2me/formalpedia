-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_iff_four_systems
-- name    : Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_iff_four_systems
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:59:42.321851+00:00
-- url     : https://prove2.me/theorems/58004fc1-f84b-4f8d-929e-a04da3ff8f27
-- title:
--   affine iff four systems
-- statement:
--   In ℤ/(4q)ℤ put A={0,q,x,x+2q}, B={0,q,x+q,x+3q}, and D={0,q,2q,3q}; these are sets, so repeated entries count once. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For every positive natural q and x∈ℤ/(4q)ℤ with x∉D, A and B are affinely equivalent if and only if there exists a unit u of ℤ/(4q)ℤ such that either uq=q and (ux=x+q or ux=x+3q), or uq=−q and (ux=x or ux=x+2q).
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterAffineCriterion.lean, lines 125–134; source file SHA-256 7575c3b014a769e070202229a8e9d2abee0368ed94316d08f50628cef77847e5; theorem Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_iff_four_systems

import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_common_pair_cases
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_exchanged_point_image
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_four_systems_affine
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem affine_iff_four_systems (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) :
    AffineEquivalent (patternA q x) (patternB q x) ↔
      ∃ u : (ZMod (4*q))ˣ, FourSystems q x u := by sorry




end Couret.InterIA.Catalogue.Quarter.AffineCriterion
