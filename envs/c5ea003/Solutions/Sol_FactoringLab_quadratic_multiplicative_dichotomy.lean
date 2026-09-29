-- Prove2me | solution 1 for FactoringLab.quadratic_multiplicative_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:53:52.984563+00:00
-- url     : https://prove2.me/submissions/d0210f5c-2e41-478f-adf3-2b9d8dc874d4

-- Sol generated from Probability/QuadraticDichotomy.lean
import Mathlib
import Definitions.Def_Probability_QuadraticDichotomy
import Definitions.Def_Probability_SymmetryCircularity
import Theorems.Thm_FactoringLab_quadratic_degenerate_monomial
import Theorems.Thm_FactoringLab_recovery_from_sum
/-
# The Quadratic Multiplicative Dichotomy (Factoring Lab, Phase A v19c — cycle 2)

Partially closing **Conjecture 3** of `FUTURE_DIRECTIONS.md`.

The previous cycle proved the dichotomy for the *affine* family `f(r) = r + c`
(`FactoringLab.affine_invariant_dichotomy`): such an invariant is either `N` in
disguise (`c = 0`) or it hands over `p + q` and hence, by
`FactoringLab.recovery_from_sum`, the complete factorization.

Here the same dichotomy is established for the *entire quadratic family*: `f`
multiplicative with `f(r) = a r² + b r + c` at primes, so that
`T = f(N) = F(p) F(q)` for a semiprime `N = pq`.  The two sides are:

* **`FactoringLab.quadratic_invariant_N_only`** — in the degenerate case
  `a c = 0 ∧ a b N + b c = 0` the value is the explicit function
  `T = a²N² + b²N + c²` of `N` alone.  (The degenerate case is exactly
  "`F` is a monomial `a X²`, `b X` or `c`", which the proof extracts.)
* **`FactoringLab.quadratic_invariant_determines_sum`** — otherwise `p + q` is a
  root of the *explicit nonzero* integer polynomial
  `Q = (ac) X² + (abN + bc) X + (a²N² + (b² − 2ac)N + c² − T)`
  whose coefficients are computed from `N` and `T` only.  Since `deg Q ≤ 2`
  there are at most two candidate values of `p + q`, and each candidate yields
  a candidate factorization in closed form.

So the invariant is either `N`-only or a factoring algorithm in disguise,
with at most a factor-two search in between; there is no intermediate
"partially informative" behaviour in the quadratic family.  The key algebraic
step is the symmetric-function identity `quadratic_invariant_identity`, which
expresses `F(p)F(q)` in terms of `N = pq` and `s = p + q` alone — the exact
mechanism the conjecture predicted.
-/

open Polynomial

open FactoringLab

/-! ## 1.  The symmetric-function identity -/


/-! ## 2.  The `N`-only side of the dichotomy -/


/-- **The `N`-only side.**  If the `s`-coefficients of the identity vanish then
the invariant is an explicit function of `N` alone — it carries no information
about the individual factors beyond `N`. -/
theorem quadratic_invariant_N_only {a b c p q : ℤ} (hN : p * q ≠ 0)
    (h1 : a * c = 0) (h2 : a * b * (p * q) + b * c = 0) :
    (a * p ^ 2 + b * p + c) * (a * q ^ 2 + b * q + c)
      = a ^ 2 * (p * q) ^ 2 + b ^ 2 * (p * q) + c ^ 2 := by
  rcases quadratic_degenerate_monomial hN h1 h2 with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
  · subst ha; subst hb; ring
  · subst ha; subst hc; ring
  · subst hb; subst hc; ring

/-! ## 3.  The recovery side: an explicit quadratic for `p + q` -/


theorem sumCandidatePoly_natDegree_le (a b c N T : ℤ) :
    (sumCandidatePoly a b c N T).natDegree ≤ 2 := by
  unfold sumCandidatePoly
  compute_degree

theorem sumCandidatePoly_coeff_two (a b c N T : ℤ) :
    (sumCandidatePoly a b c N T).coeff 2 = a * c := by
  simp only [sumCandidatePoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem sumCandidatePoly_coeff_one (a b c N T : ℤ) :
    (sumCandidatePoly a b c N T).coeff 1 = a * b * N + b * c := by
  simp only [sumCandidatePoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- Nondegeneracy makes the candidate polynomial nonzero. -/
theorem sumCandidatePoly_ne_zero {a b c N T : ℤ}
    (hnd : a * c ≠ 0 ∨ a * b * N + b * c ≠ 0) : sumCandidatePoly a b c N T ≠ 0 := by
  intro h
  rcases hnd with h2 | h1
  · exact h2 (by rw [← sumCandidatePoly_coeff_two a b c N T, h, coeff_zero])
  · exact h1 (by rw [← sumCandidatePoly_coeff_one a b c N T, h, coeff_zero])

/-- The true sum of the factors is a root of the candidate polynomial. -/
theorem sumCandidatePoly_eval (a b c p q : ℤ) :
    (sumCandidatePoly a b c (p * q)
        ((a * p ^ 2 + b * p + c) * (a * q ^ 2 + b * q + c))).eval (p + q) = 0 := by
  simp only [sumCandidatePoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- **The recovery side.**  Outside the degenerate case the sum `p + q` is a
root of an explicit nonzero polynomial of degree `≤ 2` whose coefficients are
computed from the public data `(N, T)`; hence there are at most two candidate
sums, and the search for the factorization is a two-element search. -/
theorem quadratic_invariant_determines_sum {a b c p q : ℤ}
    (hnd : a * c ≠ 0 ∨ a * b * (p * q) + b * c ≠ 0) :
    let N := p * q
    let T := (a * p ^ 2 + b * p + c) * (a * q ^ 2 + b * q + c)
    let Q := sumCandidatePoly a b c N T
    Q ≠ 0 ∧ Q.natDegree ≤ 2 ∧ (p + q) ∈ Q.roots ∧ Multiset.card Q.roots ≤ 2 := by
  intro N T Q
  have hQ : Q ≠ 0 := sumCandidatePoly_ne_zero hnd
  have hdeg : Q.natDegree ≤ 2 := sumCandidatePoly_natDegree_le a b c N T
  refine ⟨hQ, hdeg, ?_, le_trans (card_roots' Q) hdeg⟩
  rw [mem_roots hQ]
  simpa [IsRoot, Q, N, T] using sumCandidatePoly_eval a b c p q

/-! ## 4.  The dichotomy -/


/-! ## 5.  The affine and linear families as special cases -/



open FactoringLab in
theorem solution{a b c p q : ℤ} (hpq : p ≤ q) (hN : p * q ≠ 0) :
    let N := p * q
    let T := (a * p ^ 2 + b * p + c) * (a * q ^ 2 + b * q + c)
    ((a * c = 0 ∧ a * b * N + b * c = 0) → T = a ^ 2 * N ^ 2 + b ^ 2 * N + c ^ 2) ∧
      (¬ (a * c = 0 ∧ a * b * N + b * c = 0) →
        let Q := sumCandidatePoly a b c N T
        Q ≠ 0 ∧ Multiset.card Q.roots ≤ 2 ∧ (p + q) ∈ Q.roots ∧
          ((p + q) - (Int.sqrt ((p + q) ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
          ((p + q) + (Int.sqrt ((p + q) ^ 2 - 4 * N) : ℤ)) / 2 = q) := by
  intro N T
  constructor
  · rintro ⟨h1, h2⟩
    exact quadratic_invariant_N_only hN h1 h2
  · intro hnd
    have hnd' : a * c ≠ 0 ∨ a * b * N + b * c ≠ 0 := by
      by_contra h
      push_neg at h
      exact hnd ⟨h.1, h.2⟩
    obtain ⟨hQ, _, hroot, hcard⟩ := quadratic_invariant_determines_sum (a := a) (b := b) (c := c)
      (p := p) (q := q) hnd'
    obtain ⟨_, h1, h2⟩ := recovery_from_sum hpq (rfl : N = p * q) (rfl : p + q = p + q)
    exact ⟨hQ, hcard, hroot, h1, h2⟩
