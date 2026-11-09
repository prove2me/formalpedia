-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_scaled_cast_eq
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.scaled_cast_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:32:27.636205+00:00
-- url     : https://prove2.me/theorems/baf252ea-f46d-4a50-bdee-a22e6a44f2f1
-- title:
--   scaled cast eq
-- statement:
--   For all natural numbers $d,n,a,b$ with $d≠0$, the congruence $da=db$ modulo $dn$ is equivalent to $a=b$ modulo $n$. For $n=0$ both are equalities in $ℤ$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticCore.lean, lines 13–16; source file SHA-256 82693435b82358edeca13f5b4d237954c592a51649c16be781ec5926b1273c45; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.scaled_cast_eq

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
import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem scaled_cast_eq (d n a b : ℕ) (hd : d ≠ 0) :
    ((d*a : ℕ) : ZMod (d*n))=(d*b : ℕ) ↔ (a : ZMod n)=b := by sorry






end Couret.InterIA.Catalogue.Quarter.Arithmetic
