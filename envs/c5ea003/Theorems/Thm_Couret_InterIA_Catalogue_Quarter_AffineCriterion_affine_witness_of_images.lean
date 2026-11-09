-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_witness_of_images
-- name    : Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_witness_of_images
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:44.0992+00:00
-- url     : https://prove2.me/theorems/6a8693d3-3c2b-4e2c-9b88-03185e8ea4c2
-- title:
--   affine witness of images
-- statement:
--   Write $P_q(x)=\{0,q,x,x+2q\}$, $B_q(x)=\{0,q,x+q,x+3q\}$ and $D_q=\{0,q,2q,3q\}$ in $ℤ/(4q)ℤ$. For every integer $q>0$, residue $x∉D_q$, unit $u$, and residue $v$, if $u0+v∈\{0,q\}$, $uq+v∈\{0,q\}$, and $ux+v∈\{x+q,x+3q\}$, then $uP_q(x)+v=B_q(x)$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterAffineCriterion.lean, lines 68–93; source file SHA-256 7575c3b014a769e070202229a8e9d2abee0368ed94316d08f50628cef77847e5; theorem Couret.InterIA.Catalogue.Quarter.AffineCriterion.affine_witness_of_images

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_affine_injective
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_preserves_half
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternA_card_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_card_iff
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem affine_witness_of_images (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (u : (ZMod (4*q))ˣ) (v : ZMod (4*q))
    (h0 : (u : ZMod (4*q))*0+v=0 ∨ (u : ZMod (4*q))*0+v=q)
    (hQ : (u : ZMod (4*q))*q+v=0 ∨ (u : ZMod (4*q))*q+v=q)
    (hX : (u : ZMod (4*q))*x+v=x+q ∨ (u : ZMod (4*q))*x+v=x+3 • (q : ZMod (4*q))) :
    (patternA q x).image (fun a => (u : ZMod (4*q))*a+v)=patternB q x := by sorry










end Couret.InterIA.Catalogue.Quarter.AffineCriterion
