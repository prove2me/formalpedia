-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_common_point_image
-- name    : Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_common_point_image
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:58.663388+00:00
-- url     : https://prove2.me/theorems/2580cb40-d5ed-4cdc-9648-8c5f4991553e
-- title:
--   affine common point image
-- statement:
--   Write $P_q(x)=\{0,q,x,x+2q\}$, $B_q(x)=\{0,q,x+q,x+3q\}$ and $D_q=\{0,q,2q,3q\}$ in $ℤ/(4q)ℤ$. For every integer $q>0$, $x∈ℤ/(4q)ℤ$ outside $D_q$, unit $u$, and residues $v,z$, if $uP_q(x)+v=B_q(x)$ and $z=0$ or $z=q$, then $uz+v=0$ or $uz+v=q$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterAffineGeometry.lean, lines 106–116; source file SHA-256 4fc9cdbc6c8581db933863c792c5b7374b8c41f0609ff0ee3db720e92e88e383; theorem Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_common_point_image

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_common_point_has_no_partner
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_patternB_unpaired_common
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_affine_injective
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_preserves_half
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem affine_common_point_image (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (u : (ZMod (4*q))ˣ) (v z : ZMod (4*q))
    (hAB : (patternA q x).image (fun a => (u : ZMod (4*q))*a+v)=patternB q x)
    (hz : z=0 ∨ z=q) : (u : ZMod (4*q))*z+v=0 ∨ (u : ZMod (4*q))*z+v=q := by sorry


end Couret.InterIA.Catalogue.Quarter.AffineCriterion
