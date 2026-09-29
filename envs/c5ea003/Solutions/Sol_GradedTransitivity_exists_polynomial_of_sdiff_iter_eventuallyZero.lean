-- Prove2me | solution 1 for GradedTransitivity.exists_polynomial_of_sdiff_iter_eventuallyZero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:47:49.884917+00:00
-- url     : https://prove2.me/submissions/b4a0e588-96a7-4395-a09d-a5c35e55a04c

-- Sol generated from Shared/GradedTransitivity/PolyClassification.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_Newton
import Definitions.Def_Shared_GradedTransitivity_PolyClassification
import Theorems.Thm_GradedTransitivity_binomPoly_eval
import Theorems.Thm_GradedTransitivity_newton_forward

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


theorem binomPoly_natDegree_le (N j : ℕ) : (binomPoly N j).natDegree ≤ j := by
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_comp, descPochhammer_natDegree, Polynomial.natDegree_X_sub_C, mul_one]





open GradedTransitivity in
theorem solution{r : ℕ} {a : ℕ → ℚ}
    (h : EventuallyZero (sdiff^[r + 1] a)) :
    ∃ (N : ℕ) (p : ℚ[X]), p.natDegree ≤ r ∧ ∀ n ≥ N, a n = p.eval (n : ℚ) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ∑ j ∈ Finset.range (r + 1), C (sdiff^[j] a N) * binomPoly N j, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact le_trans (binomPoly_natDegree_le N j) (by have := Finset.mem_range.1 hj; omega)
  · intro n hn
    rw [newton_forward hN n hn]
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [binomPoly_eval N j n hn]
    rfl
