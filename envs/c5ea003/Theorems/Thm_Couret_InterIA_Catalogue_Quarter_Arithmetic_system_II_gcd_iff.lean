-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_II_gcd_iff
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.system_II_gcd_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:06.108663+00:00
-- url     : https://prove2.me/theorems/3b42d7b8-5a12-48d9-98ae-b8d6efb31883
-- title:
--   system II gcd iff
-- statement:
--   For every integer $q>0$ and natural number $X$, there exists a unit $u$ modulo $4q$ with $uq=q$ and $uX=X+3q$ if and only if the natural number $q/\gcd(q,X)$ is divisible by $4$. This includes $X=0$; the gcd divisor is positive.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticClassification.lean, lines 33–36; source file SHA-256 aa25c7fbf429030eeccff75a2d618fc03437ca5ed80cb99719a28df85a261c79; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.system_II_gcd_iff

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_coprime
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_modulus_positive
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_II_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_scale_iff
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm

theorem system_II_gcd_iff (q X : ℕ) (hq : 0 < q) :
    System q X 1 3 ↔ (q / q.gcd X)%4=0 := by sorry














end Couret.InterIA.Catalogue.Quarter.Arithmetic
