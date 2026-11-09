-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_scale_iff
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.system_scale_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:41:10.056624+00:00
-- url     : https://prove2.me/theorems/87ab68d6-9b65-4dd5-8c1a-554f281ec30b
-- title:
--   Scaling the unit system
-- statement:
--   For natural numbers $d,b,a,e,k$ with $d>0$ and $b>0$, the existence of a unit $u$ modulo $4db$ satisfying $u(db)=e(db)$ and $u(da)=da+k(db)$ is equivalent to the existence of a unit $w$ modulo $4b$ satisfying $wb=eb$ and $wa=a+kb$. No restrictions on $a,e,k$ are imposed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticCore.lean, lines 28–55; source file SHA-256 82693435b82358edeca13f5b4d237954c592a51649c16be781ec5926b1273c45; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.system_scale_iff

import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_scaled_cast_eq
import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem system_scale_iff (d b a e k : ℕ) (hd : 0 < d) (hb : 0 < b) :
    System (d*b) (d*a) e k ↔ System b a e k := by sorry


end Couret.InterIA.Catalogue.Quarter.Arithmetic
