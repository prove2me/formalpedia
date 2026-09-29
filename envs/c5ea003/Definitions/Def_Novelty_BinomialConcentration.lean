-- Prove2me | Definitions.Def_Novelty_BinomialConcentration
-- name    : Novelty_BinomialConcentration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:07:25.715918+00:00
-- url     : https://prove2.me/theorems/26929334-1fa0-48e5-9d63-0ec39296beaa
-- title:
--   Aether Catalog definitions — Novelty_BinomialConcentration
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BinomialConcentration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BinomialConcentration.lean by skeleton subtraction
import Mathlib
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

namespace PriceOfUniversality

open Finset

/-- The binomial weight `C(n,k) t^k (1-t)^{n-k}`. -/
noncomputable def binw (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (t ^ k * (1 - t) ^ (n - k))










end PriceOfUniversality


