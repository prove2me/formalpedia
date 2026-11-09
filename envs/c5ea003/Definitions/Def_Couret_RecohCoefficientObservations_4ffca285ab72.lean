-- Prove2me | Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
-- name    : Couret_RecohCoefficientObservations_4ffca285ab72
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:04:01.814311+00:00
-- url     : https://prove2.me/theorems/9b8e266a-7f05-44b1-97a2-7487e0b397fc
-- title:
--   Exact coefficient formats and observation checks
-- statement:
--   Interprets sparse integer terms $(e,c)$ as $\sum c\zeta^e$. Defines reduced exponents by $e<(p-1)p^k$, and a stricter input format requiring distinct exponents and nonzero coefficients as well. Defines exact coefficient comparison, comparison to a negated reading, finite-bank reading checks, and the conjunction with the sparse square check. The bundled lemmas connect these operations to polynomial and primitive-root evaluation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientObservations.lean; source file SHA-256 a214893fb37c3513240d7e15478b624128c990891c03081a0727378779f10685

import Aesop
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

/-- The complex value represented by integer coefficients in the power
basis of a supplied root.  This is semantic, not a runtime computation. -/
noncomputable def recohCoefficientValue (ζ : ℂ) (terms : RecohSparseTerms) : ℂ :=
  (terms.map (fun t => (t.2 : ℂ) * ζ ^ t.1)).sum

/-- Every stored exponent lies strictly below the primary cyclotomic degree.
Repeated exponents and zero coefficients do not invalidate this contract. -/
def RecohCoefficientsReduced (p k : ℕ) (terms : RecohSparseTerms) : Prop :=
  ∀ t ∈ terms, t.1 < (p - 1) * p ^ k

/-- Conditions on already typed coefficient terms corresponding to the
range, nonzero and nonrepetition checks in `_read_coefficients`.  Input order
is arbitrary, as it is in the Python input format. -/
def RecohCoefficientFormat (p k : ℕ) (terms : RecohSparseTerms) : Prop :=
  RecohCoefficientsReduced p k terms ∧
    (terms.map Prod.fst).Nodup ∧ ∀ t ∈ terms, t.2 ≠ 0

/-- Executable validation of the typed coefficient-format conditions. -/
def recohCoefficientFormatCheck (p k : ℕ) (terms : RecohSparseTerms) : Bool := by
  letI : Decidable (RecohCoefficientFormat p k terms) := by
    unfold RecohCoefficientFormat RecohCoefficientsReduced
    infer_instance
  exact decide (RecohCoefficientFormat p k terms)





/-- Agreement between the explicit weighted sum and polynomial semantics. -/
theorem recoh_terms_polynomial_aeval (ζ : ℂ) (terms : RecohSparseTerms) :
    aeval ζ (recohTermsPolynomial terms) = recohCoefficientValue ζ terms := by
  induction terms with
  | nil => simp [recohTermsPolynomial, recohCoefficientValue]
  | cons t terms ih =>
    simp only [recohTermsPolynomial, map_add, aeval_monomial,
      recohCoefficientValue, List.map_cons, List.sum_cons]
    rw [show aeval ζ (recohTermsPolynomial terms) =
      (terms.map (fun t => (t.2 : ℂ) * ζ ^ t.1)).sum from ih]
    rfl

/-- The exponent-range contract implies the required strict degree bound,
even when coefficients cancel or vanish. -/
theorem recoh_coefficients_degree_lt (p k : ℕ) (terms : RecohSparseTerms)
    (h : RecohCoefficientsReduced p k terms) :
    (recohTermsPolynomial terms).degree < ((p - 1) * p ^ k : ℕ) := by
  revert h
  induction terms with
  | nil =>
    intro _
    simpa only [recohTermsPolynomial, degree_zero] using
      (WithBot.bot_lt_coe ((p - 1) * p ^ k))
  | cons t terms ih =>
    intro h
    have ht : t.1 < (p - 1) * p ^ k := h t (by simp)
    have htail : RecohCoefficientsReduced p k terms := by
      intro u hu
      exact h u (List.mem_cons_of_mem _ hu)
    change (monomial t.1 t.2 + recohTermsPolynomial terms).degree < _
    exact lt_of_le_of_lt (degree_add_le _ _) (max_lt
      (lt_of_le_of_lt (degree_monomial_le t.1 t.2) (WithBot.coe_lt_coe.mpr ht))
      (ih htail))

/-- Every raw monomial emitted by the root normalizer satisfies the exponent
range contract; this assertion does not require canonical coefficient lists. -/
theorem recoh_root_terms_reduced {p : ℕ} (hp : p.Prime) (k e : ℕ) :
    RecohCoefficientsReduced p k (recohRootTerms p k e) := by
  unfold RecohCoefficientsReduced recohRootTerms
  dsimp only
  split_ifs with h
  · intro t ht
    obtain rfl := List.mem_singleton.mp ht
    exact h
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    change j * p ^ k + e % p ^ (k + 1) % p ^ k < (p - 1) * p ^ k
    have hr := Nat.mod_lt (e % p ^ (k + 1)) (pow_pos hp.pos k)
    calc
      j * p ^ k + e % p ^ (k + 1) % p ^ k < j * p ^ k + p ^ k :=
        Nat.add_lt_add_left hr _
      _ = (j + 1) * p ^ k := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (p - 1) * p ^ k :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (List.mem_range.mp hj))

theorem recoh_reduced_terms_reduced {p : ℕ} (hp : p.Prime) (k : ℕ) (es : List ℕ) :
    RecohCoefficientsReduced p k (recohReducedTerms p k es) := by
  intro t ht
  obtain ⟨e, _, he⟩ := List.mem_flatMap.mp ht
  exact recoh_root_terms_reduced hp k e t he

theorem recoh_reduced_terms_value {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (es : List ℕ) :
    recohCoefficientValue ζ (recohReducedTerms p k es) = (es.map (ζ ^ ·)).sum := by
  rw [← recoh_terms_polynomial_aeval, recoh_reduced_terms_polynomial]
  exact recoh_root_sum_polynomial_aeval hp k hζ es

/-- Faithfulness of the sparse integer comparator for any two coefficient
lists whose exponents lie in the primary power basis. -/
theorem recoh_reduced_coefficients_equal_iff {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (xs ys : RecohSparseTerms)
    (hx : RecohCoefficientsReduced p k xs) (hy : RecohCoefficientsReduced p k ys) :
    recohSparseEqual xs ys = true ↔ recohCoefficientValue ζ xs = recohCoefficientValue ζ ys := by
  rw [recoh_sparse_equal_iff]
  have degree_bound (terms : RecohSparseTerms) (ht : RecohCoefficientsReduced p k terms) :
      (recohTermsPolynomial terms).degree < ((p ^ (k + 1)).totient : WithBot ℕ) := by
    simpa only [Nat.totient_prime_pow_succ hp, Nat.mul_comm] using
      recoh_coefficients_degree_lt p k terms ht
  have h := (recoh_cyclotomic_eval_eq_iff (pow_pos hp.pos _) hζ
    (recohTermsPolynomial xs) (recohTermsPolynomial ys)
    (degree_bound xs hx) (degree_bound ys hy)).symm
  simpa only [recoh_terms_polynomial_aeval] using h

/-- Compare a candidate root sum directly to observed integer coefficients. -/
def recohCoefficientMatch (p k : ℕ) (es : List ℕ) (terms : RecohSparseTerms) : Bool :=
  recohSparseEqual (recohReducedTerms p k es) terms







/-- Direct integer comparison of the negative candidate reading against the
observed coefficients, for the executable sign-recovery backend. -/
def recohCoefficientMatchNeg (p k : ℕ) (es : List ℕ) (terms : RecohSparseTerms) : Bool :=
  recohSparseEqual (recohNegateTerms (recohReducedTerms p k es)) terms



variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Check a finite, arbitrarily indexed bank of observed coefficient lists.
No enumeration of the ambient group and no complex arithmetic occur. -/
def recohCoefficientReadingsCheck {I : Type*} [Fintype I]
    (p k : I → ℕ) (enc : I → Finset G → List ℕ) (obsTerms : I → RecohSparseTerms)
    (S : Finset G) : Bool :=
  decide (∀ i : I, recohCoefficientMatch (p i) (k i) (enc i S) (obsTerms i) = true)



/-- Complete observation checker whose observed readings are already
integer coefficients in the primary power bases. -/
def recohCoefficientObservationCheck {I : Type*} [Fintype I]
    (U : Finset G) (R : G → ℕ) (p k : I → ℕ)
    (enc : I → Finset G → List ℕ) (obsTerms : I → RecohSparseTerms) (S : Finset G) : Bool :=
  recohSparseSquareCheck U S R && recohCoefficientReadingsCheck p k enc obsTerms S







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


