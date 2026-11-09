-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_exchanged_point_image
-- name    : Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_exchanged_point_image
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:37.051872+00:00
-- url     : https://prove2.me/theorems/83ddcefe-b5a6-480d-8c4f-1ad48f5e79b2
-- title:
--   Image of an exchanged point
-- statement:
--   For every positive natural $q$, $x\in R=\mathbb Z/(4q)\mathbb Z$ outside $\{0,q,2q,3q\}$, unit $u\in R^\times$ and $v\in R$, if $u\{0,q,x,x+2q\}+v=\{0,q,x+q,x+3q\}$ as finite sets, then $ux+v=x+q$ or $ux+v=x+3q$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterAffineCriterion.lean, lines 33–53; source file SHA-256 7575c3b014a769e070202229a8e9d2abee0368ed94316d08f50628cef77847e5; theorem Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_exchanged_point_image

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_affine_injective
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_pair_separations
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem affine_exchanged_point_image (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (u : (ZMod (4*q))ˣ) (v : ZMod (4*q))
    (hAB : (patternA q x).image (fun a => (u : ZMod (4*q))*a+v)=patternB q x) :
    (u : ZMod (4*q))*x+v=x+q ∨
      (u : ZMod (4*q))*x+v=x+3 • (q : ZMod (4*q)) := by sorry














end Couret.InterIA.Catalogue.Quarter.AffineCriterion
