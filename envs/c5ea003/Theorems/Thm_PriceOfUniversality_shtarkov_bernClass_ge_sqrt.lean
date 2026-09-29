-- Prove2me | Theorems.Thm_PriceOfUniversality_shtarkov_bernClass_ge_sqrt
-- name    : PriceOfUniversality.shtarkov_bernClass_ge_sqrt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:24:35.21239+00:00
-- url     : https://prove2.me/theorems/a468471a-896a-4541-862e-b9ced1664b7c
-- title:
--   `√n / 4` is a lower bound for the Shtarkov sum of the memoryless binary class.
-- statement:
--   `√n / 4` is a lower bound for the Shtarkov sum of the memoryless binary class.
--
--   ```lean
--   theorem PriceOfUniversality.shtarkov_bernClass_ge_sqrt(n : ℕ) (hn : 1 ≤ n) :
--       Real.sqrt n / 4 ≤ shtarkov (bernClass n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyBernoulli.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyBernoulli.lean#L280

-- Thm stub generated from Novelty/UniversalRedundancyBernoulli.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
/-
# The price of universality, IV: a Rissanen-style `(1/2) log₂ n` lower bound

We instantiate the exact minimax theory of `UniversalRedundancyShtarkov` on the
class of **memoryless binary sources of block length `n`**: messages are binary
strings of length `n` (encoded as subsets of `Fin n`), and the source with
parameter `t` gives the string `s` probability `t ^ #s * (1 - t) ^ (n - #s)`.
The class is indexed by the maximum-likelihood grid `t = j / n`, `j = 0, …, n`
(the standard parametrisation for normalised maximum likelihood: `j/n` is exactly
the MLE of a string with `j` ones).

The main theorem, `bernoulli_regret_ge_half_logb`, states that **every** code for
length-`n` binary strings suffers, on some string, a regret of at least

  `(1/2) · log₂ n − 2`  bits

against the best member of the class.  This reproduces Rissanen's `(k/2) log n`
minimax redundancy rate for a `k = 1`-parameter family, with explicit constants
and no asymptotics.

The proof is the classical "counting distinguishable sources" argument made
quantitative:

* the Shtarkov sum dominates `∑ᵢ Pθᵢ(Kᵢ)` for any disjoint family of index sets;
* Chebyshev's inequality (`binw_concentration`) shows that a binomial source
  with mean `c` puts mass `≥ 3/4` on the window of half-width `d ≈ √n` around `c`;
* there are `≈ √n / 2` such windows inside `[0, n]`, so the Shtarkov sum is
  `≥ √n / 4`, i.e. the class contains `≈ √n` mutually distinguishable sources.
-/

open PriceOfUniversality

open Finset Real

/-! ## The class of memoryless binary sources -/









/-! ## The Shtarkov sum of the class -/







/-! ## The `√n` lower bound on the Shtarkov sum -/


variable (n : ℕ)

theorem PriceOfUniversality.shtarkov_bernClass_ge_sqrt(n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt n / 4 ≤ shtarkov (bernClass n) := by sorry
