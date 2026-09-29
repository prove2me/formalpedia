-- Prove2me | Theorems.Thm_PriceOfUniversality_binw_chebyshev
-- name    : PriceOfUniversality.binw_chebyshev
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:22:52.789595+00:00
-- url     : https://prove2.me/theorems/43347a47-a85b-49f1-a03e-cd6415bb82fa
-- title:
--   Chebyshev's inequality for the binomial law.
-- statement:
--   **Chebyshev's inequality for the binomial law.**
--
--   ```lean
--   theorem PriceOfUniversality.binw_chebyshev{n : ℕ} {t d : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hd : 0 < d)
--       {K : Finset ℕ} (hK : K ⊆ range (n + 1))
--       (hfar : ∀ k ∈ K, d ^ 2 ≤ ((k : ℝ) - (n : ℝ) * t) ^ 2) :
--       ∑ k ∈ K, binw n t k ≤ (n : ℝ) * t * (1 - t) / d ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BinomialConcentration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BinomialConcentration.lean#L139

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

theorem PriceOfUniversality.binw_chebyshev{n : ℕ} {t d : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hd : 0 < d)
    {K : Finset ℕ} (hK : K ⊆ range (n + 1))
    (hfar : ∀ k ∈ K, d ^ 2 ≤ ((k : ℝ) - (n : ℝ) * t) ^ 2) :
    ∑ k ∈ K, binw n t k ≤ (n : ℝ) * t * (1 - t) / d ^ 2 := by sorry
