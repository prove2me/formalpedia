-- Prove2me | Theorems.Thm_collatz_counterexample_exists
-- name    : collatz_counterexample_exists
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-09T03:14:26.48149+00:00
-- url     : https://prove2.me/theorems/4b6e516e-049d-4922-bdc8-7ce6b71e21ef
-- title:
--   Collatz counterexample: a positive orbit that never reaches one
-- statement:
--   Find a positive integer n and prove that every iterate of its Collatz orbit is different from one. The quantifier includes all natural iteration counts, including zero. This is the counterexample alternative to the Collatz conjecture, not an assertion that a counterexample is known. A negative, rational or 2-adic cycle does not satisfy this goal, and a finite computation alone does not prove that an orbit avoids one forever.
-- source:
--   Explicit negation/counterexample alternative of the Collatz conjecture, requested as an open research goal. See Terence Tao, arXiv:1909.03562v7, Conjecture 1.1, https://arxiv.org/html/1909.03562v7 ; corresponding platform convergence goal CollatzMission.collatz_conjecture, 661c9a38-220b-49a9-918a-6e837e45a7cd. The cited source states the conjecture, not the existence of a counterexample.

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_counterexample_exists : ∃ n : ℕ, 0 < n ∧ ∀ k : ℕ, collatzStep^[k] n ≠ 1 := by sorry
