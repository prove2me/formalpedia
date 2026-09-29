-- Prove2me | solution 1 for GradedTransitivity.binomPoly_eval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:38:07.613866+00:00
-- url     : https://prove2.me/submissions/b8ea4f7d-5a81-45c9-b4ca-80ecd26bfd89

-- Sol generated from Shared/GradedTransitivity/PolyClassification.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_Newton
import Definitions.Def_Shared_GradedTransitivity_PolyClassification

/-!
# Denominator `(1-q)^{r+1}` ⟺ eventually polynomial of degree `≤ r`

`PolynomialGrowth` shows one implication and `Newton` produces, from the
vanishing of `Δ^{r+1}`, an explicit binomial expansion.  Here we convert that
binomial expansion into an honest polynomial, using the falling factorial
`descPochhammer`, and obtain the exact classification

`(1-q)^{r+1} · ∑ a n qⁿ` is a polynomial ⟺ `a` is eventually given by a
polynomial of degree `≤ r`.

## Main results

* `binomPoly_eval` : `C(n-N, j)` is a polynomial function of `n` of degree `j`.
* `exists_polynomial_of_sdiff_iter_eventuallyZero` : vanishing of `Δ^{r+1}`
  produces the polynomial.
* `gen_poly_iff_eventually_polynomial` : the classification.
-/

open GradedTransitivity

open Polynomial







open GradedTransitivity in
theorem solution(N j : ℕ) : ∀ n ≥ N, (binomPoly N j).eval (n : ℚ) = binomShift N j n := by
  intro n hn
  have hcast : (n : ℚ) - (N : ℚ) = ((n - N : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hn]
    ring
  have hfac : (j.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  simp only [binomPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, hcast]
  rw [descPochhammer_eval_eq_descFactorial ℚ (n - N) j,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [binomShift, Nat.cast_mul]
  field_simp
