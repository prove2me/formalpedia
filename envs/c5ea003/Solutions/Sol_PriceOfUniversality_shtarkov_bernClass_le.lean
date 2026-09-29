-- Prove2me | solution 1 for PriceOfUniversality.shtarkov_bernClass_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:22:32.570895+00:00
-- url     : https://prove2.me/submissions/4d43efd7-7ee9-40af-9c3b-976e06d8353c

-- Sol generated from Novelty/UniversalRedundancySharpness.lean
import Mathlib
import Definitions.Def_Novelty_BinomialConcentration
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyProduct
import Definitions.Def_Novelty_UniversalRedundancySharpness
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_bern_eq_binw
import Theorems.Thm_PriceOfUniversality_binw_nonneg
import Theorems.Thm_PriceOfUniversality_binw_sum
import Theorems.Thm_PriceOfUniversality_grid_mem_Icc
import Theorems.Thm_PriceOfUniversality_shtarkov_bernClass
/-
# The price of universality, VI: sharpness, non-vacuity and the two-sided rate

Adversarial review of the preceding files.  Two questions are settled here.

**1. Are the hypotheses of the "exact price" theorems satisfiable?**
`indicatorClass_sandwich` exhibits a concrete class — the `m` deterministic
sources on an alphabet of size `m` — that satisfies every hypothesis of
`price_of_universality_sandwich` and `minimax_regret_disjoint`, so those results
are not vacuous.  For this class the general theory specialises to a sharp
pigeonhole statement about code lengths, `exists_length_ge_logb_card`: any Kraft
code on `m` messages assigns some message a length of at least `log₂ m`.

**2. Is the `(1/2) log₂ n` lower bound of the Bernoulli class of the right
order?**  `shtarkov_bernClass_le` shows `S ≤ n + 1`, hence the exact minimax
regret of the memoryless binary class of block length `n` obeys

  `(1/2) log₂ n − 2  ≤  regret  ≤  log₂ (n + 1)`.

So the truth is pinned between `(1/2) log₂ n` and `log₂ n`; the classical
`(1/2) log₂ n + O(1)` answer sits at the lower end, and no bound better than
linear in `log n` is possible.  Closing the factor-of-two gap requires the
Stirling-type estimate discussed in `FUTURE_DIRECTIONS.md`.
-/

open PriceOfUniversality

open Finset Real

/-! ## Bridge: the average-case price never exceeds the worst-case price -/


variable {A : Type*} [Fintype A] [Nonempty A] {Θ : Type*} [Fintype Θ] [Nonempty Θ]




/-! ## A concrete class realising the exact price `log₂ m` -/


variable {m : ℕ}









/-! ## The Bernoulli class: matching upper bound of order `log n` -/

/-- The maximum likelihood of a string with `k` ones is attained on the grid. -/
lemma exists_eq_mlik (n k : ℕ) :
    ∃ j : Fin (n + 1), mlik n k = ((j : ℝ) / n) ^ k * (1 - (j : ℝ) / n) ^ (n - k) := by
  obtain ⟨j₀, -, h₀⟩ :=
    Finset.exists_max_image (univ : Finset (Fin (n + 1)))
      (fun j : Fin (n + 1) => ((j : ℝ) / n) ^ k * (1 - (j : ℝ) / n) ^ (n - k)) univ_nonempty
  exact ⟨j₀, le_antisymm
    ((Finset.sup'_le_iff univ_nonempty _).2 fun j _ => h₀ j (mem_univ j))
    (Finset.le_sup' (α := ℝ)
      (fun j : Fin (n + 1) => ((j : ℝ) / n) ^ k * (1 - (j : ℝ) / n) ^ (n - k))
      (mem_univ j₀))⟩





open PriceOfUniversality in
theorem solution(n : ℕ) : shtarkov (bernClass n) ≤ (n : ℝ) + 1 := by
  rw [shtarkov_bernClass]
  have hterm : ∀ k ∈ range (n + 1), (n.choose k : ℝ) * mlik n k ≤ 1 := by
    intro k hk
    obtain ⟨j, hj⟩ := exists_eq_mlik n k
    rw [hj, bern_eq_binw]
    have h01 := grid_mem_Icc j
    have hle : binw n ((j : ℝ) / n) k ≤ ∑ i ∈ range (n + 1), binw n ((j : ℝ) / n) i :=
      Finset.single_le_sum (f := fun i => binw n ((j : ℝ) / n) i)
        (fun i _ => binw_nonneg h01.1 h01.2 n i) hk
    rw [binw_sum] at hle
    exact hle
  calc ∑ k ∈ range (n + 1), (n.choose k : ℝ) * mlik n k
      ≤ ∑ _k ∈ range (n + 1), (1:ℝ) := Finset.sum_le_sum hterm
    _ = (n : ℝ) + 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        push_cast
        ring
