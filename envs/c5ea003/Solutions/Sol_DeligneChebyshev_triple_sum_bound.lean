-- Prove2me | solution 1 for DeligneChebyshev.triple_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:37:49.98957+00:00
-- url     : https://prove2.me/submissions/5672655e-a92e-4fe0-a6df-6fb11d65375c

-- Sol generated from Algebra/AbstractAlgebra/DeligneChebyshevBound.lean
import Mathlib
import Definitions.Def_Algebra_AbstractAlgebra_DeligneChebyshevBound

/-!
# The Deligne bound for Chebyshev `U`-polynomials and triple correlation sums

This file proves the (elementary) "Deligne bound" for the Chebyshev polynomials of the
second kind `U_k` on the interval `[-1, 1]`:
`|U_k(x)| ≤ k + 1` for all `x ∈ [-1, 1]`.

The name refers to the analogy with Deligne's bounds for the eigenvalues of Frobenius
(equivalently, for Hecke eigenvalues / Kloosterman-type sums), where the relevant local
factors are exactly Chebyshev `U`-polynomials evaluated on `[-1,1]`.

We also record the immediate application to **triple correlation sums**: any sum
`∑_{n ≤ N} f(n) g(n+1) h(n+2)` of three sequences bounded by `1` in absolute value is
bounded by `N + 1`, and this bound is sharp.

The Chebyshev polynomial is `Polynomial.Chebyshev.U ℝ k`, evaluated via `Polynomial.eval`.
We package this as a real-valued function `Uval k x`.
-/

open Real Set
open scoped BigOperators

open DeligneChebyshev







/-! ## Triple correlation sums -/





open DeligneChebyshev in
theorem solution(f g h : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hg : ∀ n, |g n| ≤ 1) (hh : ∀ n, |h n| ≤ 1) (N : ℕ) :
    |triple_sum f g h N| ≤ (N + 1 : ℕ) := by
  unfold triple_sum
  calc |∑ n ∈ Finset.range (N + 1), f n * g (n + 1) * h (n + 2)|
      ≤ ∑ n ∈ Finset.range (N + 1), |f n * g (n + 1) * h (n + 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        rw [abs_mul, abs_mul]
        have h1 : |f n| * |g (n + 1)| ≤ 1 := by
          calc |f n| * |g (n + 1)| ≤ 1 * 1 := by
                gcongr <;> [exact hf n; exact hg (n+1)]
            _ = 1 := by ring
        calc |f n| * |g (n + 1)| * |h (n + 2)| ≤ 1 * 1 := by
              gcongr; exact hh (n+2)
          _ = 1 := by ring
    _ = (N + 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_range]
        simp
