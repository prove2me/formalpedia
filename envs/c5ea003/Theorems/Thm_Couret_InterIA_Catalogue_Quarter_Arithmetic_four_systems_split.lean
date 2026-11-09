-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_four_systems_split
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.four_systems_split
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:33:54.663519+00:00
-- url     : https://prove2.me/theorems/ce15c6f7-9951-41fe-a44d-21434332d12b
-- title:
--   four systems split
-- statement:
--   Here the condition $\mathcal S(q,X,e,k)$ means that there is a unit $u$ modulo $4q$ satisfying $uq=eq$ and $uX=X+kq$ modulo $4q$. For all natural numbers $q,X$, there exists a unit $u$ modulo $4q$ such that either $uq=q$ and $uX∈\{X+q,X+3q\}$, or $uq=-q$ and $uX∈\{X,X+2q\}$, if and only if at least one of $\mathcal S(q,X,1,1)$, $\mathcal S(q,X,1,3)$, $\mathcal S(q,X,3,0)$, and $\mathcal S(q,X,3,2)$ holds. The case $q=0$ is included, with $ℤ/(0)ℤ=ℤ$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticClassification.lean, lines 48–67; source file SHA-256 aa25c7fbf429030eeccff75a2d618fc03437ca5ed80cb99719a28df85a261c79; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.four_systems_split

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm

theorem four_systems_split (q X : ℕ) :
    (∃ u, FourSystems q (X : ZMod (4*q)) u) ↔
      System q X 1 1 ∨ System q X 1 3 ∨ System q X 3 0 ∨ System q X 3 2 := by sorry








end Couret.InterIA.Catalogue.Quarter.Arithmetic
