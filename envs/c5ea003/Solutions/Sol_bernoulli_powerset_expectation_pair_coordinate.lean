-- Prove2me | solution 1 for bernoulli_powerset_expectation_pair_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T20:57:17.283519+00:00
-- url     : https://prove2.me/submissions/7f042a08-db76-43c0-85e8-36d9812e2082

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_powerset_expectation_prod_factor
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

/-- `bernoulli_powerset_expectation_pair_coordinate`.

**Pair-coordinate independence** of the Bernoulli powerset expectation: for two
*distinct* coordinates `w ≠ w'`, the expectation of the product of per-coordinate
functions factorizes into the product of the two single-coordinate marginals:
`E[g(𝟙[w∈Ω])·h(𝟙[w'∈Ω])] = (p·g 1+(1-p)·g 0)·(p·h 1+(1-p)·h 0)`. Derived from
the product-factorization (independence) lemma by choosing the per-coordinate
family to be `g` at `w`, `h` at `w'`, and the constant `1` elsewhere; both the LHS
and RHS products over `univ` then collapse to their two non-trivial factors at
`{w, w'}` (the complement product is `1`). This is the input that makes the
off-diagonal (cross) terms vanish when computing the variance / second moment of
a statistic linear in the inclusion indicators. -/
theorem solution {n₁ n₂ : ℕ}
    (p : ℝ) (w w' : Fin n₁ × Fin n₂) (hww : w ≠ w') (g h : ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => g (if w ∈ Omega then 1 else 0) * h (if w' ∈ Omega then 1 else 0)) =
      (p * g 1 + (1 - p) * g 0) * (p * h 1 + (1 - p) * h 0) := by
  classical
  set F : (Fin n₁ × Fin n₂) → ℝ → ℝ :=
    fun u => if u = w then g else if u = w' then h else (fun _ => 1) with hF
  have key := bernoulli_powerset_expectation_prod_factor (n₁ := n₁) (n₂ := n₂) p F
  have collapse : ∀ (φ : (Fin n₁ × Fin n₂) → ℝ) (cw cw' : ℝ),
      (∀ u, u ≠ w → u ≠ w' → φ u = 1) → φ w = cw → φ w' = cw' →
      (∏ u : Fin n₁ × Fin n₂, φ u) = cw * cw' := by
    intro φ cw cw' hother hw hw'
    rw [← Finset.prod_mul_prod_compl {w, w'} φ]
    have h1 : (∏ u ∈ ({w, w'} : Finset (Fin n₁ × Fin n₂)), φ u) = cw * cw' := by
      rw [Finset.prod_pair hww, hw, hw']
    have h2 : (∏ u ∈ ({w, w'} : Finset (Fin n₁ × Fin n₂))ᶜ, φ u) = 1 := by
      apply Finset.prod_eq_one
      intro u hu
      simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
      exact hother u hu.1 hu.2
    rw [h1, h2, mul_one]
  have hL : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        ∏ u : Fin n₁ × Fin n₂, F u (if u ∈ Omega then 1 else 0)) =
      (fun Omega => g (if w ∈ Omega then 1 else 0) * h (if w' ∈ Omega then 1 else 0)) := by
    funext Omega
    apply collapse (fun u => F u (if u ∈ Omega then 1 else 0))
    · intro u hu hu'; simp only [hF, if_neg hu, if_neg hu']
    · simp only [hF, if_pos rfl]
    · simp only [hF, if_neg (show w' ≠ w from fun he => hww he.symm), if_true]
  rw [hL] at key
  rw [key]
  apply collapse (fun u => p * F u 1 + (1 - p) * F u 0)
  · intro u hu hu'; simp only [hF, if_neg hu, if_neg hu']; ring
  · simp only [hF, if_pos rfl]
  · simp only [hF, if_neg (show w' ≠ w from fun he => hww he.symm), if_true]
