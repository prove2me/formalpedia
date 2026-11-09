-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_coprime
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.reduced_coprime
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:32:08.718518+00:00
-- url     : https://prove2.me/theorems/9d86a6ea-ea12-4f6d-a9a8-c65ac057e70c
-- title:
--   Coprimality after gcd reduction
-- statement:
--   For natural numbers $q,X$ with $q>0$, the natural numbers $X/\gcd(q,X)$ and $q/\gcd(q,X)$ are coprime. The value $X=0$ is included; the divisor is positive.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticClassification.lean, lines 19–22; source file SHA-256 aa25c7fbf429030eeccff75a2d618fc03437ca5ed80cb99719a28df85a261c79; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.reduced_coprime

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
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm

theorem reduced_coprime (q X : ℕ) (hq : 0 < q) :
    (X / q.gcd X).Coprime (q / q.gcd X) := by sorry




















end Couret.InterIA.Catalogue.Quarter.Arithmetic
