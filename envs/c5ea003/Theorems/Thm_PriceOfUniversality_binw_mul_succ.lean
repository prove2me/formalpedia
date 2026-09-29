-- Prove2me | Theorems.Thm_PriceOfUniversality_binw_mul_succ
-- name    : PriceOfUniversality.binw_mul_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:23:01.335685+00:00
-- url     : https://prove2.me/theorems/bf33dc66-e76d-4b5c-b823-587af2f9f75f
-- title:
--   The key reindexing identity `(j+1) * C(n+1, j+1) = (n+1) * C(n, j)`, in the form
-- statement:
--   The key reindexing identity `(j+1) * C(n+1, j+1) = (n+1) * C(n, j)`, in the form
--   needed for moment computations.
--
--   ```lean
--   theorem PriceOfUniversality.binw_mul_succ(m j : ℕ) (t : ℝ) :
--       ((j : ℝ) + 1) * binw (m + 1) t (j + 1) = ((m : ℝ) + 1) * t * binw m t j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BinomialConcentration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BinomialConcentration.lean#L47

-- Thm stub generated from Novelty/BinomialConcentration.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
/-
# Binomial moments and Chebyshev concentration

Elementary, fully explicit development of the first two moments of the binomial
weights

  `binw n t k = C(n,k) * t ^ k * (1 - t) ^ (n - k)`

and of the resulting Chebyshev concentration inequality.  These are the
analytic ingredients used in `UniversalRedundancyBernoulli.lean` to prove a
Rissanen-style `(1/2) log₂ n` lower bound on the minimax redundancy of the class
of memoryless binary sources.

Main results:

* `binw_sum` — the weights sum to one (binomial theorem);
* `binw_mean` — `∑ k * binw n t k = n * t`;
* `binw_sq` — `∑ k ^ 2 * binw n t k = n * t * ((n - 1) * t + 1)`;
* `binw_variance` — `∑ (k - n t) ^ 2 * binw n t k = n * t * (1 - t)`;
* `binw_chebyshev` / `binw_concentration` — Chebyshev's inequality for the
  binomial law.
-/

open PriceOfUniversality

open Finset

theorem PriceOfUniversality.binw_mul_succ(m j : ℕ) (t : ℝ) :
    ((j : ℝ) + 1) * binw (m + 1) t (j + 1) = ((m : ℝ) + 1) * t * binw m t j := by sorry
