-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_two_negative_branches_separate
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.two_negative_branches_separate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:08.020951+00:00
-- url     : https://prove2.me/theorems/68c8d7b8-82d3-40c7-9a6a-6577b0e4e7b0
-- title:
--   two negative branches separate
-- statement:
--   In ℤ/24ℤ all four assertions hold: there is a unit u with 6u=18 and 2u=14; there is no unit u with 6u=18 and 2u=2; there is a unit u with 6u=18 and 4u=4; and there is no unit u with 6u=18 and 4u=16. The witnesses in the two existence assertions need not be the same.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticBoundary.lean, lines 53–57; source file SHA-256 74ee22738a4ba93ca2f316f06b61bde30f27ee972c2487d5eab677e973748b31; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.two_negative_branches_separate

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_III_gcd_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_IV_gcd_iff
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem two_negative_branches_separate : System 6 2 3 2 ∧ ¬ System 6 2 3 0 ∧
    System 6 4 3 0 ∧ ¬ System 6 4 3 2 := by sorry


end Couret.InterIA.Catalogue.Quarter.Arithmetic
