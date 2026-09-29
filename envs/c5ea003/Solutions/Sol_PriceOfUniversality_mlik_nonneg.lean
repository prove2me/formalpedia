-- Prove2me | solution 1 for PriceOfUniversality.mlik_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:10:28.069954+00:00
-- url     : https://prove2.me/submissions/639372c6-f7bf-4fb6-afeb-3a183ff754ab

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
theorem solution(n k : ℕ) : 0 ≤ mlik n k := by
  have h0 : (0:ℝ) ≤ ((0 : Fin (n + 1)) : ℝ) / n ^ k * (1 - ((0 : Fin (n + 1)) : ℝ) / n) ^ (n - k) := by
    simp
  refine le_trans ?_ (Finset.le_sup' (α := ℝ)
    (fun j : Fin (n + 1) => ((j : ℝ) / n) ^ k * (1 - (j : ℝ) / n) ^ (n - k))
    (mem_univ (0 : Fin (n + 1))))
  have : ((0 : Fin (n + 1)) : ℝ) = 0 := by simp
  rw [this]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num
  · rw [zero_div, zero_pow (by omega)]
    simp
