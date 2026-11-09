-- Prove2me | Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
-- name    : Couret_RecohCyclotomicNormalization_6797485e207c
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:17.98084+00:00
-- url     : https://prove2.me/theorems/331902c2-6dba-4ab3-9ccb-5db9e6bcbc63
-- title:
--   Sparse primary cyclotomic normal forms
-- statement:
--   For prime-power root orders $p^{k+1}$, the primary polynomial is $\sum_{j<p}X^{jp^k}$. Root powers and exponent lists are reduced to degree below $(p-1)p^k$. Sparse terms are lists of natural-exponent and integer-coefficient pairs, with coefficient lookup, polynomial interpretation, equality checking and coefficient negation. Raw constructors accept arbitrary natural parameters; primality and root assumptions are supplied by theorems.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclotomicNormalization.lean; source file SHA-256 a32b9cab640a62555c7e6cf6db19b7be429a75e16530887b17a37e8f886e5a45

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

set_option autoImplicit false

/-!
Exact integer-polynomial normalization for primary character sums.

The parameter `k` is one less than the positive primary exponent: the order
is `p ^ (k + 1)` and the stride is `p ^ k`.  Executable reduction uses lists
of integer monomials.  Mathlib's noncomputable integer-polynomial operations
provide their semantics; complex evaluation occurs in correctness theorems.
The separate Python `cyclotomic_sum` implementation is not extracted from,
or certified by, this module.
-/

namespace Couret.STROBO2TORS

open Polynomial
open scoped BigOperators

/-- Explicit prime-power cyclotomic polynomial, used as algebraic semantics. -/
noncomputable def recohPrimaryPolynomial (p k : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range p, X ^ (j * p ^ k)

theorem recoh_primary_polynomial_eq_cyclotomic {p : ℕ} (hp : p.Prime) (k : ℕ) :
    recohPrimaryPolynomial p k = cyclotomic (p ^ (k + 1)) ℤ := by
  rw [recohPrimaryPolynomial, cyclotomic_prime_pow_eq_geom_sum hp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [← pow_mul, Nat.mul_comm]

/-- The integer power basis of a primitive root is faithful below the
cyclotomic degree.  This is an unconditional injectivity theorem, with the
order and primitivity hypotheses displayed explicitly. -/
theorem recoh_cyclotomic_eval_eq_iff {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (P Q : ℤ[X])
    (hP : P.degree < (n.totient : WithBot ℕ))
    (hQ : Q.degree < (n.totient : WithBot ℕ)) :
    aeval ζ P = aeval ζ Q ↔ P = Q := by
  constructor
  · intro he
    apply sub_eq_zero.mp
    apply Polynomial.eq_zero_of_dvd_of_degree_lt
      (minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hn) (by
        rw [map_sub, he, sub_self]))
    rw [← cyclotomic_eq_minpoly hζ hn, degree_cyclotomic]
    exact lt_of_le_of_lt (degree_sub_le P Q) (max_lt hP hQ)
  · rintro rfl
    rfl

theorem recoh_primary_polynomial_aeval {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    aeval ζ (recohPrimaryPolynomial p k) = 0 := by
  rw [recoh_primary_polynomial_eq_cyclotomic hp,
    cyclotomic_eq_minpoly hζ (pow_pos hp.pos _)]
  exact minpoly.aeval ℤ ζ

theorem recoh_primary_top_power {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    ζ ^ ((p - 1) * p ^ k) = -(∑ j ∈ Finset.range (p - 1), ζ ^ (j * p ^ k)) := by
  have hz := recoh_primary_polynomial_aeval hp k hζ
  simp only [recohPrimaryPolynomial, map_sum, map_pow, aeval_X] at hz
  have hs := Finset.sum_range_succ (fun j : ℕ => ζ ^ (j * p ^ k)) (p - 1)
  rw [Nat.sub_add_cancel hp.one_le] at hs
  rw [hs] at hz
  linear_combination hz

/-- Algebraic form of the two reduction branches in `cyclotomic_sum`. -/
noncomputable def recohRootPolynomial (p k e : ℕ) : ℤ[X] :=
  let r := e % p ^ (k + 1)
  if r < (p - 1) * p ^ k then X ^ r
  else -(∑ j ∈ Finset.range (p - 1), X ^ (j * p ^ k + r % p ^ k))

private theorem recoh_high_residue {p k r : ℕ} (hp : p.Prime)
    (hr : r < p ^ (k + 1)) (hh : (p - 1) * p ^ k ≤ r) :
    r = (p - 1) * p ^ k + r % p ^ k := by
  have hdiv : r / p ^ k = p - 1 := Nat.div_eq_of_lt_le hh (by
    simpa only [Nat.sub_add_cancel hp.one_le, pow_succ, Nat.mul_comm] using hr)
  have hparts := Nat.mod_add_div r (p ^ k)
  rw [hdiv] at hparts
  simpa only [Nat.mul_comm, Nat.add_comm] using hparts.symm

theorem recoh_root_polynomial_aeval {p : ℕ} (hp : p.Prime) (k e : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    aeval ζ (recohRootPolynomial p k e) = ζ ^ e := by
  have hmod : ζ ^ (e % p ^ (k + 1)) = ζ ^ e := by
    rw [hζ.eq_orderOf]
    exact pow_mod_orderOf ζ e
  unfold recohRootPolynomial
  dsimp only
  split_ifs with h
  · simpa only [map_pow, aeval_X] using hmod
  · simp only [map_neg, map_sum, map_pow, aeval_X]
    have hr := recoh_high_residue hp
      (Nat.mod_lt e (pow_pos hp.pos _)) (Nat.le_of_not_gt h)
    have hsum :
        (∑ j ∈ Finset.range (p - 1),
          ζ ^ (j * p ^ k + e % p ^ (k + 1) % p ^ k)) =
        (∑ j ∈ Finset.range (p - 1), ζ ^ (j * p ^ k)) *
          ζ ^ (e % p ^ (k + 1) % p ^ k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      exact pow_add ζ _ _
    rw [hsum, ← neg_mul, ← recoh_primary_top_power hp k hζ,
      ← pow_add, ← hr]
    exact hmod



/-- The reduced polynomial for a list of roots; multiplicities are retained. -/
noncomputable def recohRootSumPolynomial (p k : ℕ) (es : List ℕ) : ℤ[X] :=
  (es.map (recohRootPolynomial p k)).sum

theorem recoh_root_sum_polynomial_aeval {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (es : List ℕ) :
    aeval ζ (recohRootSumPolynomial p k es) = (es.map (ζ ^ ·)).sum := by
  induction es with
  | nil => simp [recohRootSumPolynomial]
  | cons e es ih =>
    simp only [recohRootSumPolynomial, List.map_cons, List.sum_cons, map_add]
    rw [recoh_root_polynomial_aeval hp k e hζ]
    exact congrArg (ζ ^ e + ·) ih





/-! ## Executable sparse terms and their polynomial interpretation -/

/-- A raw list of monomials.  Repeated exponents and zero coefficients are
allowed; syntactic equality of these lists is not the comparison primitive. -/
abbrev RecohSparseTerms := List (ℕ × ℤ)

/-- Executable reduction of a single root.  This uses exactly the two
branches of the integer-polynomial reduction above. -/
def recohRootTerms (p k e : ℕ) : RecohSparseTerms :=
  let r := e % p ^ (k + 1)
  if r < (p - 1) * p ^ k then [(r, 1)]
  else (List.range (p - 1)).map (fun j => (j * p ^ k + r % p ^ k, -1))

/-- Executable reduction of a list of roots before combining equal powers. -/
def recohReducedTerms (p k : ℕ) (es : List ℕ) : RecohSparseTerms :=
  es.flatMap (recohRootTerms p k)

/-- Semantic interpretation; the polynomial implementation itself is
noncomputable in Mathlib, while the term-list operations are executable. -/
noncomputable def recohTermsPolynomial : RecohSparseTerms → ℤ[X]
  | [] => 0
  | t :: ts => monomial t.1 t.2 + recohTermsPolynomial ts

theorem recoh_terms_polynomial_append (xs ys : RecohSparseTerms) :
    recohTermsPolynomial (xs ++ ys) = recohTermsPolynomial xs + recohTermsPolynomial ys := by
  induction xs with
  | nil => simp [recohTermsPolynomial]
  | cons t ts ih => simp [recohTermsPolynomial, ih, add_assoc]

private theorem recoh_terms_polynomial_range (m : ℕ) (f : ℕ → ℕ) (c : ℤ) :
    recohTermsPolynomial ((List.range m).map (fun j => (f j, c))) =
      ∑ j ∈ Finset.range m, monomial (f j) c := by
  induction m with
  | zero => simp [recohTermsPolynomial]
  | succ m ih =>
    rw [List.range_succ, List.map_append, recoh_terms_polynomial_append,
      Finset.sum_range_succ, ih]
    simp [recohTermsPolynomial]

theorem recoh_root_terms_polynomial (p k e : ℕ) :
    recohTermsPolynomial (recohRootTerms p k e) = recohRootPolynomial p k e := by
  unfold recohRootTerms recohRootPolynomial
  dsimp only
  split_ifs
  · simp [recohTermsPolynomial, X_pow_eq_monomial]
  · rw [recoh_terms_polynomial_range]
    simp only [monomial_neg, ← X_pow_eq_monomial, Finset.sum_neg_distrib]

theorem recoh_reduced_terms_polynomial (p k : ℕ) (es : List ℕ) :
    recohTermsPolynomial (recohReducedTerms p k es) = recohRootSumPolynomial p k es := by
  induction es with
  | nil => simp [recohReducedTerms, recohTermsPolynomial, recohRootSumPolynomial]
  | cons e es ih =>
    simp only [recohReducedTerms, List.flatMap_cons,
      recoh_terms_polynomial_append, recoh_root_terms_polynomial]
    rw [show recohTermsPolynomial (List.flatMap (recohRootTerms p k) es) =
        recohRootSumPolynomial p k es from ih]
    simp [recohRootSumPolynomial]









/-! ## Executable equality by summing coefficients at present exponents -/

/-- Sum all coefficients at a given exponent, including repetitions. -/
def recohSparseCoeff (ts : RecohSparseTerms) (n : ℕ) : ℤ :=
  (ts.map (fun t => if t.1 = n then t.2 else 0)).sum

/-- Compare only exponents present in either raw list.  Duplicated tests are
harmless; no dense vector of cyclotomic-degree length is constructed. -/
def recohSparseEqual (xs ys : RecohSparseTerms) : Bool :=
  ((xs.map Prod.fst) ++ (ys.map Prod.fst)).all
    (fun n => decide (recohSparseCoeff xs n = recohSparseCoeff ys n))

theorem recoh_terms_polynomial_coeff (ts : RecohSparseTerms) (n : ℕ) :
    (recohTermsPolynomial ts).coeff n = recohSparseCoeff ts n := by
  induction ts with
  | nil => simp [recohTermsPolynomial, recohSparseCoeff]
  | cons t ts ih =>
    simp [recohTermsPolynomial, recohSparseCoeff, coeff_monomial] at ih ⊢
    exact ih

theorem recoh_sparse_coeff_zero_of_not_mem (ts : RecohSparseTerms) (n : ℕ)
    (hn : n ∉ ts.map Prod.fst) : recohSparseCoeff ts n = 0 := by
  induction ts with
  | nil => simp [recohSparseCoeff]
  | cons t ts ih =>
    have hne : t.1 ≠ n := by
      intro he
      exact hn (by simp [he])
    have htail : n ∉ ts.map Prod.fst := by
      intro hm
      exact hn (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hm)
    simp only [recohSparseCoeff, List.map_cons, List.sum_cons, if_neg hne,
      zero_add]
    exact ih htail

/-- Exact semantic equality for arbitrary raw term lists; this deliberately
does not assert syntactic injectivity of raw lists. -/
theorem recoh_sparse_equal_iff (xs ys : RecohSparseTerms) :
    recohSparseEqual xs ys = true ↔
      recohTermsPolynomial xs = recohTermsPolynomial ys := by
  unfold recohSparseEqual
  rw [List.all_eq_true]
  constructor
  · intro h
    apply Polynomial.ext
    intro n
    rw [recoh_terms_polynomial_coeff, recoh_terms_polynomial_coeff]
    by_cases hn : n ∈ xs.map Prod.fst ++ ys.map Prod.fst
    · exact of_decide_eq_true (h n hn)
    · have hx : n ∉ xs.map Prod.fst := by
        intro hm
        exact hn (List.mem_append_left _ hm)
      have hy : n ∉ ys.map Prod.fst := by
        intro hm
        exact hn (List.mem_append_right _ hm)
      rw [recoh_sparse_coeff_zero_of_not_mem xs n hx,
        recoh_sparse_coeff_zero_of_not_mem ys n hy]
  · intro h n _
    apply decide_eq_true
    rw [← recoh_terms_polynomial_coeff, ← recoh_terms_polynomial_coeff, h]







/-- Executable coefficient negation for the sign comparison in the decoder. -/
def recohNegateTerms (ts : RecohSparseTerms) : RecohSparseTerms :=
  ts.map (fun t => (t.1, -t.2))





/-!
## Boundary with the separate Python implementation

`recohRootTerms` uses the same exponent reduction and the same emitted
integer monomials as `cyclotomic_sum` in `../recoh_exact_decoder.py`, with
`order = p ^ (k + 1)` and `stride = p ^ k`.  The Python code subsequently
combines coefficients with `Counter`, omits zeros and sorts by exponent.

The theorems in this module certify the Lean term-list reduction and its
coefficient-summing comparator.  They identify exact equality with equality
of the interpreted integer polynomials and then with complex equality.
They do not certify Python execution, its container operations, parsing,
the extraction of primary orders, or a canonical sorted-list representation.
There is no theorem asserting injectivity of raw monomial lists.

For two normalized triples with prime 2 or 3, the comparator visits at most
twelve exponent positions.  Each test scans both finite term lists.  The
length bounds above do not constitute a bit-complexity theorem: exponent
reduction, integer arithmetic and input reading retain their own costs.
-/


end Couret.STROBO2TORS


