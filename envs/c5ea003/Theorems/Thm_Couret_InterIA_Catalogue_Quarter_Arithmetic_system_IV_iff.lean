-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_IV_iff
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.system_IV_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:46:59.67086+00:00
-- url     : https://prove2.me/theorems/05fc4a35-f7f5-4639-b6a4-c2bef11078ad
-- title:
--   system IV iff
-- statement:
--   For all natural numbers $b,a$ with $b>0$ and $\gcd(a,b)=1$, there exists a unit $u$ modulo $4b$ satisfying $ub=3b$ and $ua=a+2b$ if and only if $a+b$ is even. The value $a=0$ is not excluded.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticSystems.lean, lines 125–130; source file SHA-256 d93360c6c75de0b5944dc398bab25d7e89eec7f6821d906234948b4afcaacfa5; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.system_IV_iff

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_coprime_not_both_even
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_negative_system_sufficient
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_mod_four
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem system_IV_iff (b a : ℕ) (hb : 0 < b) (hab : a.Coprime b) :
    System b a 3 2 ↔ (a+b)%2=0 := by sorry


end Couret.InterIA.Catalogue.Quarter.Arithmetic
