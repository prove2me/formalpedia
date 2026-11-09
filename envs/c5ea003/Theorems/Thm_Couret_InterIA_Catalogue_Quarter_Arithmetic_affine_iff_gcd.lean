-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_affine_iff_gcd
-- name    : Couret.InterIA.Catalogue.Quarter.Arithmetic.affine_iff_gcd
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:06.095814+00:00
-- url     : https://prove2.me/theorems/7df23023-58f1-486c-aabd-9ab13f73b168
-- title:
--   Affine equivalence and a gcd criterion
-- statement:
--   For every positive natural $q$ and $x\in R=\mathbb Z/(4q)\mathbb Z$ outside $\{0,q,2q,3q\}$, there exist a unit $u\in R^\times$ and $v\in R$ with $u\{0,q,x,x+2q\}+v=\{0,q,x+q,x+3q\}$ if and only if $(q/\gcd(q,X))\bmod4\ne2$, where $X$ is the least nonnegative representative of $x$ and division is natural-number division. The denominator is positive because $q>0$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticClassification.lean, lines 77–83; source file SHA-256 aa25c7fbf429030eeccff75a2d618fc03437ca5ed80cb99719a28df85a261c79; theorem Couret.InterIA.Catalogue.Quarter.Arithmetic.affine_iff_gcd

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_iff_four_systems
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_coprime_not_both_even
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_four_systems_split
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_coprime
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_III_gcd_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_II_gcd_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_IV_gcd_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_I_gcd_iff
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm

theorem affine_iff_gcd (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) :
    AffineEquivalent (patternA q x) (patternB q x) ↔ (q/q.gcd x.val)%4 ≠ 2 := by sorry




end Couret.InterIA.Catalogue.Quarter.Arithmetic
