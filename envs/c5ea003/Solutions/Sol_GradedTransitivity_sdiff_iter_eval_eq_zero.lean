-- Prove2me | solution 1 for GradedTransitivity.sdiff_iter_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:43:45.71923+00:00
-- url     : https://prove2.me/submissions/6b08390b-314c-4de6-ba95-a1e4110203ec

-- Sol generated from Shared/GradedTransitivity/PolynomialGrowth.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_PolynomialGrowth
import Theorems.Thm_GradedTransitivity_pdiff_natDegree_le

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


@[simp] lemma pdiff_eval (p : ℚ[X]) (x : ℚ) : (pdiff p).eval x = p.eval (x + 1) - p.eval x := by
  simp [pdiff, Polynomial.eval_comp]


/-- The sequence-level forward difference of a polynomial sequence is the
polynomial sequence of the discrete derivative. -/
theorem sdiff_evalSeq (p : ℚ[X]) :
    sdiff (fun n : ℕ => p.eval (n : ℚ)) = fun n : ℕ => (pdiff p).eval (n : ℚ) := by
  funext n
  simp [GradedTransitivity.sdiff, pdiff_eval]






open GradedTransitivity in
theorem solution:
    ∀ (d : ℕ) (p : ℚ[X]), p.natDegree ≤ d →
      sdiff^[d + 1] (fun n : ℕ => p.eval (n : ℚ)) = fun _ => 0 := by
  intro d
  induction d with
  | zero =>
      intro p hp
      obtain ⟨c, rfl⟩ : ∃ c, p = C c :=
        ⟨p.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.1 hp)⟩
      funext n
      simp [GradedTransitivity.sdiff]
  | succ d ih =>
      intro p hp
      have hd : (pdiff p).natDegree ≤ d := pdiff_natDegree_le hp
      have : sdiff^[d + 1 + 1] (fun n : ℕ => p.eval (n : ℚ))
          = sdiff^[d + 1] (sdiff (fun n : ℕ => p.eval (n : ℚ))) :=
        Function.iterate_succ_apply _ _ _
      rw [this, sdiff_evalSeq]
      exact ih _ hd
