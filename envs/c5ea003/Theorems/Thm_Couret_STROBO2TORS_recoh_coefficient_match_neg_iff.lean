-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_match_neg_iff
-- name    : Couret.STROBO2TORS.recoh_coefficient_match_neg_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:21.419529+00:00
-- url     : https://prove2.me/theorems/17374b88-5033-4c06-8744-7a6478772252
-- title:
--   Negated coefficient matching is algebraically exact
-- statement:
--   Let $p$ be prime, $k\in\mathbb N$, $\zeta$ primitive of order $p^{k+1}$, $E$ an exponent list, and $T$ a sparse integer coefficient list whose exponents are below $(p-1)p^k$. Then
--
--   $$\operatorname{MatchNeg}_{p,k}(E,T)=\mathrm{true}\Longleftrightarrow-\sum_{e\in E}\zeta^e=\sum_{(a,c)\in T}c\zeta^a.$$
--
--   This verifies the negative-sign branch of root coefficient comparison.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientObservations.lean, lines 168–175; source file SHA-256 a214893fb37c3513240d7e15478b624128c990891c03081a0727378779f10685; theorem Couret.STROBO2TORS.recoh_coefficient_match_neg_iff

import Aesop
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_value_negate
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficients_reduced_negate
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Exact observation checking from integer cyclotomic coefficients.

Observed readings are supplied directly as lists of pairs `(exponent,
integer coefficient)`.  No conversion from coefficients back to root lists
is used.  Complex values occur only in the interpretation and correctness
theorems; all checkers compare natural numbers and integer coefficients.

The range contract is sufficient for faithful evaluation.  The stronger
typed-format contract also excludes zero coefficients and repeated
exponents, matching the conditions inspected by Python `_read_coefficients`.
It does not certify JSON parsing, Python execution or sorting.
-/

namespace Couret.STROBO2TORS

open Polynomial
open scoped BigOperators

theorem recoh_coefficient_match_neg_iff {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (es : List ℕ) (terms : RecohSparseTerms) (ht : RecohCoefficientsReduced p k terms) :
    recohCoefficientMatchNeg p k es terms = true ↔
      -(es.map (ζ ^ ·)).sum = recohCoefficientValue ζ terms := by sorry


variable {G : Type*} [AddCommGroup G] [DecidableEq G]













/-!
The coefficient checkers do not themselves establish support coverage,
primality, primitive-root identities or the interpretation of candidate
encodings.  Their correctness theorems display these contracts explicitly.
The observed coefficient values require no witness as a sum of three roots.
Such a representation, if it exists, is supplied by a successfully checked
candidate rather than assumed as an input encoding.

Typed lists may be arbitrarily long.  No constant or bit-complexity bound
for reading or checking observed input is asserted here.  In particular,
the twelve-position bound for comparing two normalized triples is not a
bound on arbitrary externally supplied coefficient lists.
-/


end Couret.STROBO2TORS
