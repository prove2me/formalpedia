-- Prove2me | solution 1 for PriceOfUniversality.sum_windows_le_shtarkov
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:13:08.691407+00:00
-- url     : https://prove2.me/submissions/438e451b-e872-4261-b3e0-9a0ede54affe

-- Sol generated from Novelty/UniversalRedundancyBernoulli.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_bern_eq_binw
import Theorems.Thm_PriceOfUniversality_mlik_nonneg
import Theorems.Thm_PriceOfUniversality_shtarkov_bernClass
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




lemma binw_le_choose_mul_mlik (n : ℕ) (j : Fin (n + 1)) (k : ℕ) :
    binw n ((j : ℝ) / n) k ≤ (n.choose k : ℝ) * mlik n k := by
  rw [← bern_eq_binw]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.le_sup' (α := ℝ)
    (fun j : Fin (n + 1) => ((j : ℝ) / n) ^ k * (1 - (j : ℝ) / n) ^ (n - k)) (mem_univ j)



/-! ## The `√n` lower bound on the Shtarkov sum -/


variable (n : ℕ)














/-! ## Rissanen-style minimax redundancy -/





open PriceOfUniversality in
theorem solution(n : ℕ) (I : Finset ℕ) (K : ℕ → Finset ℕ)
    (hK : ∀ i ∈ I, K i ⊆ range (n + 1))
    (hdisj : (I : Set ℕ).PairwiseDisjoint K) (jsel : ℕ → Fin (n + 1)) :
    ∑ i ∈ I, ∑ k ∈ K i, binw n ((jsel i : ℝ) / n) k ≤ shtarkov (bernClass n) := by
  have hstep : ∀ i ∈ I, ∑ k ∈ K i, binw n ((jsel i : ℝ) / n) k
      ≤ ∑ k ∈ K i, (n.choose k : ℝ) * mlik n k :=
    fun i _ => Finset.sum_le_sum fun k _ => binw_le_choose_mul_mlik n (jsel i) k
  calc ∑ i ∈ I, ∑ k ∈ K i, binw n ((jsel i : ℝ) / n) k
      ≤ ∑ i ∈ I, ∑ k ∈ K i, (n.choose k : ℝ) * mlik n k := Finset.sum_le_sum hstep
    _ = ∑ k ∈ I.biUnion K, (n.choose k : ℝ) * mlik n k := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ k ∈ range (n + 1), (n.choose k : ℝ) * mlik n k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro k hk
          rw [Finset.mem_biUnion] at hk
          obtain ⟨i, hi, hki⟩ := hk
          exact hK i hi hki
        · intro k _ _
          have := mlik_nonneg n k
          positivity
    _ = shtarkov (bernClass n) := (shtarkov_bernClass n).symm
