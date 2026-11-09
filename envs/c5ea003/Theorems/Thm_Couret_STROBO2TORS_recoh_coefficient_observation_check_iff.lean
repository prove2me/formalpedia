-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_observation_check_iff
-- name    : Couret.STROBO2TORS.recoh_coefficient_observation_check_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:39.057765+00:00
-- url     : https://prove2.me/theorems/8003e85a-da31-4ff2-b92a-2f60f34e7809
-- title:
--   Exact coefficients and sparse square checks recover the full observation
-- statement:
--   Let $G$ be an abelian group, $I$ an index type, $p_i$ primes, $k_i\in\mathbb N$, and $\zeta_i$ primitive roots of order $p_i^{k_i+1}$. Let $\chi_i$ be complex additive characters, $L_i$ reduced sparse observed lists, and $v_i=\sum_{(e,c)\in L_i}c\zeta_i^e$. An exponent encoder $E_i(B)$ interprets as $\sum_{e\in E_i(B)}\zeta_i^e=P_{\chi_i}(B)$ for each support to which the assumption is applied. Assume $I$ is finite. Let $U$ be finite, let $R:G\to\mathbb N$ vanish outside $U$, and fix a finite support $S$, for which the encoder interpretation holds at every $i$. Then
--
--   $$\operatorname{coefficientObservationCheck}(U,R,p,k,E,L,S)=\mathrm{true}\iff(R_S,(P_{\chi_i}(S))_i)=(R,v).$$
--
--   Observed lists need only satisfy the reduced-exponent bound; duplicate exponents and zero coefficients are allowed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientObservations.lean, lines 217–232; source file SHA-256 a214893fb37c3513240d7e15478b624128c990891c03081a0727378779f10685; theorem Couret.STROBO2TORS.recoh_coefficient_observation_check_iff

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_readings_check_iff
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





































variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_coefficient_observation_check_iff {I : Type*} [Fintype I]
    (U : Finset G) (R : G → ℕ) (p k : I → ℕ)
    (enc : I → Finset G → List ℕ) (obsTerms : I → RecohSparseTerms) (S : Finset G)
    (bank : I → AddChar G ℂ) (ζ obs : I → ℂ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hterms : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i, ((enc i S).map (ζ i ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i) :
    recohCoefficientObservationCheck U R p k enc obsTerms S = true ↔
      recohObservation bank S = (R, obs) := by sorry






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
