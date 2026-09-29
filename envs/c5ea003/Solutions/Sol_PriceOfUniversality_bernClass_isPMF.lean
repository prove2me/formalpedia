-- Prove2me | solution 1 for PriceOfUniversality.bernClass_isPMF
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:43:14.376454+00:00
-- url     : https://prove2.me/submissions/34116387-7bfc-4ec9-91b8-e380577c6f63

-- Sol generated from Novelty/UniversalRedundancyBernoulli.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_bern_eq_binw
import Theorems.Thm_PriceOfUniversality_binw_sum
import Theorems.Thm_PriceOfUniversality_grid_mem_Icc
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


/-- Each member of the class is a probability distribution on strings. -/
theorem bern_isPMF {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsPMF (bern n t) := by
  have h1t : 0 ≤ 1 - t := by linarith
  refine ⟨fun s => by unfold bern; positivity, ?_⟩
  calc ∑ s : Msg n, bern n t s
      = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (t ^ k * (1 - t) ^ (n - k)) :=
        sum_over_msgs n (fun k => t ^ k * (1 - t) ^ (n - k))
    _ = ∑ k ∈ range (n + 1), binw n t k :=
        Finset.sum_congr rfl fun k _ => bern_eq_binw n t k
    _ = 1 := binw_sum n t



/-! ## The Shtarkov sum of the class -/







/-! ## The `√n` lower bound on the Shtarkov sum -/


variable (n : ℕ)














/-! ## Rissanen-style minimax redundancy -/





open PriceOfUniversality in
theorem solution(n : ℕ) (j : Fin (n + 1)) : IsPMF (bernClass n j) :=
  bern_isPMF (grid_mem_Icc j).1 (grid_mem_Icc j).2
