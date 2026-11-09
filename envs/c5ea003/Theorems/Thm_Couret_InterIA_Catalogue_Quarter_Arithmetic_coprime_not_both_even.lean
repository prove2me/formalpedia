-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_coprime_not_both_even
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.coprime_not_both_even
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:31:45.866612+00:00
-- url     : https://prove2.me/theorems/fe714850-df2c-432f-bde6-7e1b8931bb22
-- title:
--   coprime not both even
-- statement:
--   For all natural a,b with gcd(a,b)=1, a has remainder 1 modulo 2 or b has remainder 1 modulo 2. Zero is allowed in either argument when the coprimality condition holds.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticSystems.lean, lines 57–63; source file SHA-256 d93360c6c75de0b5944dc398bab25d7e89eec7f6821d906234948b4afcaacfa5; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.coprime_not_both_even

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
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem coprime_not_both_even (a b : ℕ) (hab : a.Coprime b) :
    a%2=1 ∨ b%2=1 := by sorry














end Couret.InterIA.Catalogue.Quarter.Arithmetic
