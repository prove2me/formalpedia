-- Prove2me | Theorems.Thm_PriceOfUniversality_binw_sq
-- name    : PriceOfUniversality.binw_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:23:31.439693+00:00
-- url     : https://prove2.me/theorems/407a62c2-6141-43b9-819b-7bd60be806a0
-- title:
--   The second moment of the binomial law.
-- statement:
--   The second moment of the binomial law.
--
--   ```lean
--   theorem PriceOfUniversality.binw_sq(n : ℕ) (t : ℝ) :
--       ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * binw n t k = (n : ℝ) * t * (((n : ℝ) - 1) * t + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BinomialConcentration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BinomialConcentration.lean#L98

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

theorem PriceOfUniversality.binw_sq(n : ℕ) (t : ℝ) :
    ∑ k ∈ range (n + 1), (k : ℝ) ^ 2 * binw n t k = (n : ℝ) * t * (((n : ℝ) - 1) * t + 1) := by sorry
