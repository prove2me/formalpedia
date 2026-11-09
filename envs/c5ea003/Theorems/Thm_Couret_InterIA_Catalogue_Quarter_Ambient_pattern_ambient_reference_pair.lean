-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_pattern_ambient_reference_pair
-- name    : Couret.InterIA.Catalogue.Quarter.Ambient.pattern_ambient_reference_pair
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:21:28.061211+00:00
-- url     : https://prove2.me/theorems/8183a919-fee0-4807-9272-414cfdeb300e
-- title:
--   pattern ambient reference pair
-- statement:
--   Write $P_q(x)=\{0,q,x,x+2q\}$, $B_q(x)=\{0,q,x+q,x+3q\}$ and $D_q=\{0,q,2q,3q\}$ in $ℤ/(4q)ℤ$. For every integer $q>0$ and residue $x∉D_q$ such that no unit $u$ and residue $v$ satisfy $uP_q(x)+v=B_q(x)$, there exist integers $d,b>0$ with $q=db$, $b≡2$ modulo $4$, a unit $U$ modulo $4q$, and a residue $V$, such that $(UP_q(x)+V,UB_q(x)+V)$ is, in either order, the pair of images of $P_b(1),B_b(1)$ under $z↦d\operatorname{val}(z)$ from $ℤ/(4b)ℤ$ to $ℤ/(4q)ℤ$, where $\operatorname{val}$ is the least nonnegative representative.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AmbientDilationLift.lean, lines 50–72; source file SHA-256 245b598d834c2a25f7b7b267060abd2116fa77a0c09833bf30949efa2e7c0a1a; theorem Couret.InterIA.Catalogue.Quarter.Ambient.pattern_ambient_reference_pair

import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_affine_dilation_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_gcd_reference_reduction
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive

theorem pattern_ambient_reference_pair (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (hna : ¬ AffineEquivalent (patternA q x) (patternB q x)) :
    ∃ d b : ℕ, 0 < d ∧ 0 < b ∧ q=d*b ∧ b%4=2 ∧
      ∃ U : (ZMod (4*q))ˣ, ∃ V : ZMod (4*q),
        ((patternA q x).image (fun z => (U : ZMod (4*q))*z+V)=(patternA b 1).image (dilate (4*q) d) ∧
         (patternB q x).image (fun z => (U : ZMod (4*q))*z+V)=(patternB b 1).image (dilate (4*q) d)) ∨
        ((patternA q x).image (fun z => (U : ZMod (4*q))*z+V)=(patternB b 1).image (dilate (4*q) d) ∧
         (patternB q x).image (fun z => (U : ZMod (4*q))*z+V)=(patternA b 1).image (dilate (4*q) d)) := by sorry




end Couret.InterIA.Catalogue.Quarter.Ambient
