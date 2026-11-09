-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_negative_system_sufficient
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.negative_system_sufficient
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:56.409007+00:00
-- url     : https://prove2.me/theorems/9a18b63f-e7e6-4267-ae78-f8fad6aa6ba2
-- title:
--   Sufficiency for a negative system
-- statement:
--   For natural numbers $b,a,k$ with $b>0$, $b\bmod2=1$, $k=0$ or $k=2$, and $(2a)\bmod4=(kb)\bmod4$, there exists a unit $u\in(\mathbb Z/(4b)\mathbb Z)^\times$ such that $ub=3b$ and $ua=a+kb$ in $\mathbb Z/(4b)\mathbb Z$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticSystems.lean, lines 89–109; source file SHA-256 d93360c6c75de0b5944dc398bab25d7e89eec7f6821d906234948b4afcaacfa5; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.negative_system_sufficient

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
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem negative_system_sufficient (b a k : ℕ) (hb : 0 < b)
    (hbo : b%2=1) (hk : k=0 ∨ k=2) (ha : (2*a)%4=(k*b)%4) :
    System b a 3 k := by sorry










end Couret.InterIA.Catalogue.Quarter.Arithmetic
