-- Prove2me | solution 1 for PriceOfUniversality.bern_eq_binw
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:40:16.79075+00:00
-- url     : https://prove2.me/submissions/df55550c-f19c-4f96-a5e0-26e562099cd0

-- Sol generated from Novelty/UniversalRedundancyBernoulli.lean
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














/-! ## Rissanen-style minimax redundancy -/





open PriceOfUniversality in
theorem solution(n : ℕ) (t : ℝ) (k : ℕ) :
    (n.choose k : ℝ) * (t ^ k * (1 - t) ^ (n - k)) = binw n t k := rfl
