-- Prove2me | solution 1 for BookSixth.permanent_doubly_stochastic_lower
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T21:44:05.214405+00:00
-- url     : https://prove2.me/submissions/9c907c9f-822c-4cc4-8f83-a2c704567b19

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_ProofsInTheBook_Chapter22Gurvits_chapter22_unconditional

/-!
# Van der Waerden permanent lower bound (Egorychev–Falikman)

`BookSixth.permanent_doubly_stochastic_lower` [300f6287-9904-4b40-9143-88d08d60c79e]

The permanent of a doubly stochastic $n \times n$ real matrix is at least
$n!/n^n$ (Proofs from THE BOOK, 6th ed., Chapter 37, permanent lemma behind
Theorem 2, p. 266 — via Gurvits' capacity proof, Chapter 22).

The platform already contains the full Gurvits proof as the Proved theorem
`ProofsInTheBook.Chapter22Gurvits.chapter22_unconditional`. Here we simply
transfer it to the explicit BookSixth hypothesis form: nonnegativity plus
row/column sums equal to one are exactly Mathlib's membership criterion
`Matrix.mem_doublyStochastic_iff_sum` for the doubly stochastic submonoid.
-/

open scoped BigOperators

open BookSixth

theorem solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ Matrix.permanent M := by
  have hmem : M ∈ doublyStochastic ℝ (Fin n) :=
    mem_doublyStochastic_iff_sum.2 ⟨hnn, hrow, hcol⟩
  exact ProofsInTheBook.Chapter22Gurvits.chapter22_unconditional n M hmem
