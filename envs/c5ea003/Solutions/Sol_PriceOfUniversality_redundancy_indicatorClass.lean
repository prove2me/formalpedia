-- Prove2me | solution 1 for PriceOfUniversality.redundancy_indicatorClass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:22:32.080588+00:00
-- url     : https://prove2.me/submissions/92db35b2-8949-4bf6-8b56-29b98c626be0

-- Sol generated from Novelty/UniversalRedundancySharpness.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyProduct
import Definitions.Def_Novelty_UniversalRedundancySharpness
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






open PriceOfUniversality in
theorem solution(θ : Fin m) (L : Fin m → ℕ) :
    redundancy (indicatorClass m θ) L = (L θ : ℝ) := by
  have hexp : expLen (indicatorClass m θ) L = (L θ : ℝ) := by
    rw [expLen]
    rw [Finset.sum_eq_single θ]
    · simp [indicatorClass]
    · intro b _ hb
      simp [indicatorClass, hb]
    · intro h; exact absurd (mem_univ θ) h
  have hent : entropy (indicatorClass m θ) = 0 := by
    rw [entropy]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases h : a = θ <;> simp [indicatorClass, h]
  rw [redundancy, hexp, hent, sub_zero]
