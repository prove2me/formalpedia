-- Prove2me | solution 1 for PriceOfUniversality.shtarkov_bernClass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:10:28.581979+00:00
-- url     : https://prove2.me/submissions/f2a99b91-66ff-41a6-97f8-1ca21df2931b

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




/-- Summing a function of the number of ones over all binary strings of length `n`
is summing against binomial coefficients. -/
lemma sum_over_msgs (n : ℕ) (g : ℕ → ℝ) :
    ∑ s : Msg n, g (#s) = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * g k := by
  have h1 : (univ : Finset (Finset (Fin n))) = (univ : Finset (Fin n)).powerset := by
    simp
  rw [h1, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_powersetCard]
  simp [Finset.card_univ, nsmul_eq_mul]





/-! ## The Shtarkov sum of the class -/


lemma maxLik_bernClass (n : ℕ) (s : Msg n) : maxLik (bernClass n) s = mlik n (#s) := rfl





/-! ## The `√n` lower bound on the Shtarkov sum -/


variable (n : ℕ)














/-! ## Rissanen-style minimax redundancy -/





open PriceOfUniversality in
theorem solution(n : ℕ) :
    shtarkov (bernClass n) = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * mlik n k := by
  rw [shtarkov]
  calc ∑ s : Msg n, maxLik (bernClass n) s = ∑ s : Msg n, mlik n (#s) :=
        Finset.sum_congr rfl fun s _ => maxLik_bernClass n s
    _ = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * mlik n k := sum_over_msgs n (mlik n)
