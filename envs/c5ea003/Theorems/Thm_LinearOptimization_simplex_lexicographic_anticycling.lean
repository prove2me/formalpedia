-- Prove2me | Theorems.Thm_LinearOptimization_simplex_lexicographic_anticycling
-- name    : LinearOptimization.simplex_lexicographic_anticycling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:24:26.613915+00:00
-- url     : https://prove2.me/theorems/0ddbb2a6-f66d-42f6-adf6-69cdd67ee96a
-- title:
--   The lexicographic pivoting rule prevents cycling
-- statement:
--   **(Theorem 3.4)** Suppose that the simplex algorithm starts with all the rows in the simplex tableau, other than the zeroth row, lexicographically positive. Suppose that the lexicographic pivoting rule is followed. Then:
--
--   - **(a)** every row of the simplex tableau, other than the zeroth row, remains lexicographically positive throughout the algorithm;
--   - **(b)** the zeroth row strictly increases lexicographically at each iteration;
--   - **(c)** the simplex method terminates after a finite number of iterations.
--
--   (No nondegeneracy assumption; the $i$th tableau row is $[\,(B^{-1}b)_i \mid (B^{-1}A)_i\,]$ and the zeroth row is $[\,-c_B'B^{-1}b \mid c' - c_B'B^{-1}A\,]$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 3.4, p. 110

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 3.4 (p. 110).** Lexicographic anticycling: under the
lexicographic pivoting rule, (a) lexicographic positivity of the tableau
rows `1, …, m` is preserved by every pivot, (b) the zeroth tableau row
strictly increases lexicographically at every pivot, and (c) there is no
infinite lexicographic pivot run starting from a tableau whose rows other
than the zeroth are lexicographically positive. -/

theorem LinearOptimization.simplex_lexicographic_anticycling {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i)) :
    (∀ (B B' : Fin m ↪ Fin n) (x x' : Fin n → ℝ),
      IsSimplexState A b B x →
      (∀ i, LexPos (tableauRow A b B i)) →
      IsLexicographicPivot A b c B x B' x' →
      (∀ i, LexPos (tableauRow A b B' i)) ∧
      LexLt (tableauZerothRow A b c B) (tableauZerothRow A b c B')) ∧
    ¬∃ f : ℕ → (Fin m ↪ Fin n) × (Fin n → ℝ),
      (∀ k, IsSimplexState A b (f k).1 (f k).2) ∧
      (∀ i, LexPos (tableauRow A b (f 0).1 i)) ∧
      ∀ k, IsLexicographicPivot A b c (f k).1 (f k).2 (f (k + 1)).1 (f (k + 1)).2 := by
  sorry
