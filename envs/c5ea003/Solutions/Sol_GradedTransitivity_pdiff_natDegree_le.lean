-- Prove2me | solution 1 for GradedTransitivity.pdiff_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:42:16.463893+00:00
-- url     : https://prove2.me/submissions/69f91884-5d1a-438f-92ad-282a0fb1e6c2

-- Sol generated from Shared/GradedTransitivity/PolynomialGrowth.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_PolynomialGrowth

/-!
# Eventually polynomial sequences have denominator `(1-q)^{r+1}`

The discrete derivative `p ↦ p(X+1) - p` lowers the degree of a polynomial.
Iterating it `r+1` times therefore annihilates every polynomial of degree `≤ r`,
and combined with `Shared.GradedTransitivity.FiniteDifference` this shows that a
sequence which is *eventually* given by a polynomial of degree `≤ r` has
generating function with denominator `(1-q)^{r+1}`.

## Main results

* `pdiff_natDegree_le` : the discrete derivative drops the degree.
* `sdiff_iter_eval_eq_zero` : `Δ^{r+1}` kills degree `≤ r` polynomial sequences.
* `exists_poly_of_eventually_polynomial` : the rationality statement.
-/

open GradedTransitivity

open Polynomial










open GradedTransitivity in
theorem solution{p : ℚ[X]} {d : ℕ} (hp : p.natDegree ≤ d + 1) :
    (pdiff p).natDegree ≤ d := by
  by_cases h0 : p.natDegree = 0
  · have : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    rw [pdiff, this]
    simp
  · have hpne : p ≠ 0 := fun h => h0 (by simp [h])
    have hcomp : (p.comp (X + C 1)).natDegree = p.natDegree := by
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    have hm : (X + C (1 : ℚ)).leadingCoeff = 1 := Polynomial.monic_X_add_C 1
    have hlead : (p.comp (X + C (1 : ℚ))).leadingCoeff = p.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; norm_num), hm,
        one_pow, mul_one]
    have hcne : p.comp (X + C (1 : ℚ)) ≠ 0 := by
      intro h
      rw [h] at hlead
      simp only [Polynomial.leadingCoeff_zero] at hlead
      exact hpne (Polynomial.leadingCoeff_eq_zero.1 hlead.symm)
    have hdeg : (p.comp (X + C (1 : ℚ))).degree = p.degree := by
      rw [Polynomial.degree_eq_natDegree hcne, Polynomial.degree_eq_natDegree hpne, hcomp]
    by_cases hz : pdiff p = 0
    · simp [hz]
    · have hlt : (pdiff p).degree < (p.comp (X + C (1 : ℚ))).degree :=
        Polynomial.degree_sub_lt hdeg hcne hlead
      have : (pdiff p).natDegree < (p.comp (X + C (1 : ℚ))).natDegree :=
        Polynomial.natDegree_lt_natDegree hz hlt
      omega
