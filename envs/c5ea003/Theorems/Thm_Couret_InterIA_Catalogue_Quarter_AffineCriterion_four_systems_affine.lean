-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_four_systems_affine
-- name    : Couret.InterIA.Catalogue.Quarter.AffineCriterion.four_systems_affine
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:54:03.217139+00:00
-- url     : https://prove2.me/theorems/a1a67326-1137-408e-98e3-017bb299fae7
-- title:
--   four systems affine
-- statement:
--   Write $P_q(x)=\{0,q,x,x+2q\}$, $B_q(x)=\{0,q,x+q,x+3q\}$ and $D_q=\{0,q,2q,3q\}$ in $ℤ/(4q)ℤ$. For every integer $q>0$, residue $x∉D_q$, and unit $u$ modulo $4q$, suppose either $uq=q$ and $ux∈\{x+q,x+3q\}$, or $uq=-q$ and $ux∈\{x,x+2q\}$. Then there exist a unit $a$ and residue $v$ with $aP_q(x)+v=B_q(x)$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterAffineCriterion.lean, lines 110–123; source file SHA-256 7575c3b014a769e070202229a8e9d2abee0368ed94316d08f50628cef77847e5; theorem Couret.InterIA.Catalogue.Quarter.AffineCriterion.four_systems_affine

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_witness_of_images
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem four_systems_affine (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (u : (ZMod (4*q))ˣ) (hu : FourSystems q x u) :
    AffineEquivalent (patternA q x) (patternB q x) := by sorry






end Couret.InterIA.Catalogue.Quarter.AffineCriterion
