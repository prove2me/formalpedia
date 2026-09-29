-- Prove2me | solution 1 for PriceOfUniversality.logb_shtarkov_bernClass_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:13:56.822145+00:00
-- url     : https://prove2.me/submissions/cc3c6399-81da-42e5-9c49-e7c7338e1e6d

-- Sol generated from Novelty/UniversalRedundancyBernoulli.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_shtarkov_bernClass_ge_sqrt
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
theorem solution(n : ℕ) (hn : 1 ≤ n) :
    (1/2) * Real.logb 2 n - 2 ≤ Real.logb 2 (shtarkov (bernClass n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hone := shtarkov_bernClass_ge_sqrt n hn
  have hsq : (0:ℝ) < Real.sqrt n / 4 := by positivity
  have h2 : logb 2 (Real.sqrt n / 4) ≤ logb 2 (shtarkov (bernClass n)) :=
    Real.logb_le_logb_of_le (by norm_num) hsq hone
  have hs : Real.logb 2 (Real.sqrt n) = (1/2) * Real.logb 2 n := by
    rw [Real.logb, Real.logb, Real.log_sqrt (le_of_lt hnR)]
    ring
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.logb_pow]
    simp
  rw [Real.logb_div (by positivity) (by norm_num), hs, h4] at h2
  linarith
