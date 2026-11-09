-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_III_gcd_iff
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.system_III_gcd_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:52.148576+00:00
-- url     : https://prove2.me/theorems/8ab1dc15-293a-4ed6-b9ab-42d0bebdad2a
-- title:
--   Third system gcd criterion
-- statement:
--   For natural numbers $q,X$ with $q>0$, there exists a unit $u\in(\mathbb Z/(4q)\mathbb Z)^\times$ satisfying $uq=3q$ and $uX=X$ modulo $4q$ if and only if $(X/\gcd(q,X))\bmod2=0$. Here $X=0$ is allowed, and the gcd divisor is positive.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticClassification.lean, lines 38–41; source file SHA-256 aa25c7fbf429030eeccff75a2d618fc03437ca5ed80cb99719a28df85a261c79; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.system_III_gcd_iff

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_III_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_scale_iff
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm

theorem system_III_gcd_iff (q X : ℕ) (hq : 0 < q) :
    System q X 3 0 ↔ (X / q.gcd X)%2=0 := by sorry












end Couret.InterIA.Catalogue.Quarter.Arithmetic
