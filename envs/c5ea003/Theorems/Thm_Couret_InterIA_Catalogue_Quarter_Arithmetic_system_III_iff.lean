-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_III_iff
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.system_III_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:46:39.782327+00:00
-- url     : https://prove2.me/theorems/d13989cc-242c-4462-acc7-637d39af3bd8
-- title:
--   system III iff
-- statement:
--   For all natural b,a with b>0 and gcd(a,b)=1, there exists a unit u∈ℤ/(4b)ℤ satisfying ub=3b and ua=a if and only if a is even. The equations interpret all natural numbers in the residue ring; a=0 is allowed subject to coprimality.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticSystems.lean, lines 119–123; source file SHA-256 d93360c6c75de0b5944dc398bab25d7e89eec7f6821d906234948b4afcaacfa5; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.system_III_iff

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

theorem system_III_iff (b a : ℕ) (hb : 0 < b) (hab : a.Coprime b) :
    System b a 3 0 ↔ a%2=0 := by sorry




end Couret.InterIA.Catalogue.Quarter.Arithmetic
