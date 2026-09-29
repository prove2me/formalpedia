-- Prove2me | solution 1 for PriceOfUniversality.mutualInfo_le_logb_shtarkov
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:17:48.926528+00:00
-- url     : https://prove2.me/submissions/0fc49425-83c8-4976-882f-153102be64dc

-- Sol generated from Novelty/UniversalRedundancySharpness.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyProduct
import Definitions.Def_Novelty_UniversalRedundancySharpness
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_kl_compensation
import Theorems.Thm_PriceOfUniversality_kl_nml_le_logb_shtarkov
import Theorems.Thm_PriceOfUniversality_kl_nonneg
import Theorems.Thm_PriceOfUniversality_mixture_isPMF
import Theorems.Thm_PriceOfUniversality_nml_isPMF
import Theorems.Thm_PriceOfUniversality_shtarkov_pos
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
omit [Nonempty A] in
theorem solution{pri : Θ → ℝ} {p : Θ → A → ℝ}
    (hpri : IsPMF pri) (hpripos : ∀ θ, 0 < pri θ) (hp : ∀ θ, IsPMF (p θ))
    (hpos : ∀ a, 0 < maxLik p a) :
    mutualInfo pri p ≤ logb 2 (shtarkov p) := by
  have hS := shtarkov_pos hp
  have hnmlpos : ∀ a : A, 0 < nml p a := fun a => div_pos (hpos a) hS
  have hcomp := kl_compensation hpri hpripos hp hnmlpos
  have hklnn : 0 ≤ kl (mixture pri p) (nml p) :=
    kl_nonneg (mixture_isPMF hpri hp) hnmlpos (le_of_eq (nml_isPMF hp).total)
  have havg : ∑ θ, pri θ * kl (p θ) (nml p) ≤ logb 2 (shtarkov p) := by
    calc ∑ θ, pri θ * kl (p θ) (nml p)
        ≤ ∑ θ, pri θ * logb 2 (shtarkov p) :=
          Finset.sum_le_sum fun θ _ =>
            mul_le_mul_of_nonneg_left (kl_nml_le_logb_shtarkov hp hpos θ) (hpri.nonneg θ)
      _ = logb 2 (shtarkov p) := by rw [← Finset.sum_mul, hpri.total, one_mul]
  linarith
