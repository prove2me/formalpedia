-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_IV_gcd_iff
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.system_IV_gcd_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:31.771608+00:00
-- url     : https://prove2.me/theorems/eeb4ce20-4f41-49d9-8602-fd43dacda14d
-- title:
--   system IV gcd iff
-- statement:
--   For all natural q,X with q>0, there exists a unit u∈ℤ/(4q)ℤ satisfying uq=3q and uX=X+2q if and only if X/gcd(q,X)+q/gcd(q,X) is even. The quotients are natural-number division, the gcd is positive, and X=0 is included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticClassification.lean, lines 43–46; source file SHA-256 aa25c7fbf429030eeccff75a2d618fc03437ca5ed80cb99719a28df85a261c79; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.system_IV_gcd_iff

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_IV_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_scale_iff
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm

theorem system_IV_gcd_iff (q X : ℕ) (hq : 0 < q) :
    System q X 3 2 ↔ ((X / q.gcd X)+(q / q.gcd X))%2=0 := by sorry










end Couret.InterIA.Catalogue.Quarter.Arithmetic
