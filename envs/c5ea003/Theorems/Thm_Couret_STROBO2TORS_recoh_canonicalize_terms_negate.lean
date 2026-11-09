-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_canonicalize_terms_negate
-- name    : Couret.STROBO2TORS.recoh_canonicalize_terms_negate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:51.670885+00:00
-- url     : https://prove2.me/theorems/8eab8ab1-5421-4f13-be9f-79a77dcfe7b6
-- title:
--   Canonicalization commutes with coefficient negation
-- statement:
--   For every sparse term list $L$ of exponent-integer coefficient pairs, $$C(-L)=-C(L).$$ Repeated exponents and zero coefficients in the input are allowed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCanonicalCoefficients.lean, lines 258–271; source file SHA-256 d920e9c13ad1cd37a18406f175fa3c21d46e127b29d51e490e7886f8da6b9549; theorem Couret.STROBO2TORS.recoh_canonicalize_terms_negate

import Aesop
import Definitions.Def_Couret_RecohCanonicalCoefficients_7eb0bfadc07d
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_negate_terms_polynomial
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

/-!
Canonical sparse integer coefficient lists.

The Python v0.2 `_terms` routine combines coefficients at equal exponents,
discards zeros, and sorts the remaining exponent/coefficient pairs.  The
definitions below express those operations on already typed lists.  Literal
equality and literal negation of the resulting lists are faithful to the
existing polynomial and complex-value semantics.  JSON parsing and Python
execution are not asserted by this file.
-/

namespace Couret.STROBO2TORS

open Polynomial

theorem recoh_canonicalize_terms_negate (ts : RecohSparseTerms) :
    recohCanonicalizeTerms (recohNegateTerms ts) =
      recohNegateTerms (recohCanonicalizeTerms ts) := by sorry


























end Couret.STROBO2TORS
