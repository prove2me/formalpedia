-- Prove2me | solution 1 for Cryptography.GoodSeeds.exists_two_accepting_challenges
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:31:31.785545+00:00
-- url     : https://prove2.me/submissions/1678cd34-364e-4c56-84e3-8a743dae1822

-- Sol generated from Cryptography/GoodSeeds/Rewinding.lean
import Mathlib
import Definitions.Def_Cryptography_GoodSeeds_Core
import Definitions.Def_Cryptography_GoodSeeds_Rewinding
import Theorems.Thm_Cryptography_GoodSeeds_mem_goodSeeds

/-!
# Heavy rows, rewinding, and knowledge extraction from a seed fraction

The seed space of a two-move (sigma) protocol is a product
`R ×ˢ C` — prover randomness times verifier challenge — and the accepting event
`acc r c` cuts out a subset of it.  Knowledge extraction proceeds by *rewinding*:
one needs a single randomness `r` that accepts on **two distinct challenges**.

This file supplies the counting bridge between the two pictures, entirely in
terms of the `frac` operator of `Cryptography.GoodSeeds.Core`.

## Main results

* `card_good_product_eq_sum_rows` — the accepting seeds of the product space are
  counted row by row.  This is the level-set decomposition of `Core` applied to
  the cost function `Prod.fst`.
* `frac_product_eq_average_row_frac` — the global accepting fraction is the
  *average* of the row fractions.
* `exists_two_accepting_challenges` — **rewinding threshold.**  As soon as the
  accepting fraction exceeds `1 / |C|` there is a randomness accepting on two
  distinct challenges.  (Sharp: `frac_eq_one_div_card_of_unique` below exhibits
  an accepting set of fraction exactly `1 / |C|` with no such randomness, so the
  strict inequality cannot be weakened.)
* `heavy_row_lemma` — **the splitting/heavy-row lemma.**  If the global accepting
  fraction is `e`, then at least an `e / 2` fraction of the randomnesses are
  themselves `e / 2`-heavy.
* `exists_two_accepting_challenges_of_heavy` — combining the two: a quantitative
  rewinding statement with an explicit fraction of good randomnesses.

-- !-- Lab Notes -- !--
Hypothesis (HR1): the `1/|C|` rewinding threshold is *exactly* the point at which
the pigeonhole flips, i.e. it is attained by a genuine configuration and is not an
artefact of a lossy estimate.
Experiment: build the "one accepting challenge per row" configuration
`acc r c ↔ c = φ r` for an arbitrary `φ : ρ → χ` and compute its fraction.
Outcome: confirmed — `frac_eq_one_div_card_of_unique` gives fraction exactly
`1/|C|` while no row has two accepting challenges.  Hence
`exists_two_accepting_challenges` is sharp and the strict `<` is necessary.
Analysis: the two theorems together are a dichotomy at the threshold, exactly
parallel to the `monitoring_frequency_dichotomy` pattern already in the catalog:
below/at the threshold an adversarial configuration exists, above it extraction is
forced.
Hypothesis (HR2): the constant `2` in the heavy-row lemma is not special; the
same argument gives, for any `0 < α < 1`, that at least a `(1-α)e` fraction of
rows are `αe`-heavy.
Experiment: `heavy_row_lemma_general` below, proved by the identical splitting
computation with `α` in place of `1/2`.
Outcome: confirmed, and `heavy_row_lemma` is the specialisation `α = 1/2`.
Critique: all bounds are stated over *nonempty* `R` and `C`; on an empty space
`frac` degenerates to `0` (Lean's `x / 0 = 0`) and the statements are vacuous
rather than false.  Guards are therefore explicit everywhere.
-/

open Cryptography
open GoodSeeds

open Finset

variable {ρ χ : Type*}
variable {R : Finset ρ} {C : Finset χ} {acc : ρ → χ → Prop} [∀ r, DecidablePred (acc r)]


/-- The accepting seeds of a product seed space are counted row by row. -/
theorem card_good_product_eq_sum_rows :
    (goodSeeds (R ×ˢ C) (fun p => acc p.1 p.2)).card
      = ∑ r ∈ R, (goodSeeds C (acc r)).card := by
  simp only [goodSeeds, Finset.card_filter]
  rw [Finset.sum_product]


/-! ### The rewinding threshold -/

/-- If no randomness accepts two distinct challenges, then each row contributes at
most one accepting seed. -/
theorem card_row_le_one_of_no_collision {r : ρ}
    (h : ∀ c₁ ∈ C, ∀ c₂ ∈ C, acc r c₁ → acc r c₂ → c₁ = c₂) :
    (goodSeeds C (acc r)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  exact h a (mem_goodSeeds.1 ha).1 b (mem_goodSeeds.1 hb).1
    (mem_goodSeeds.1 ha).2 (mem_goodSeeds.1 hb).2



/-! ### The heavy-row (splitting) lemma -/





open Cryptography.GoodSeeds in
theorem solution(hR : R.Nonempty) (hC : C.Nonempty)
    (h : 1 / (C.card : ℚ) < frac (R ×ˢ C) (fun p => acc p.1 p.2)) :
    ∃ r ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ ∧ acc r c₁ ∧ acc r c₂ := by
  by_contra hcon
  push_neg at hcon
  have hrow : ∀ r ∈ R, (goodSeeds C (acc r)).card ≤ 1 := by
    intro r hr
    refine card_row_le_one_of_no_collision (C := C) (acc := acc) ?_
    intro c₁ hc₁ c₂ hc₂ h₁ h₂
    by_contra hne
    exact hne (hcon r hr c₁ hc₁ c₂ hc₂ hne h₁ h₂ |>.elim)
  have hcard : (goodSeeds (R ×ˢ C) (fun p => acc p.1 p.2)).card ≤ R.card := by
    rw [card_good_product_eq_sum_rows (R := R) (C := C) (acc := acc)]
    calc ∑ r ∈ R, (goodSeeds C (acc r)).card ≤ ∑ _r ∈ R, 1 := Finset.sum_le_sum hrow
      _ = R.card := by simp
  have hn : (0 : ℚ) < (R.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hR
  have hm : (0 : ℚ) < (C.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hC
  have hle : frac (R ×ˢ C) (fun p => acc p.1 p.2) ≤ 1 / (C.card : ℚ) := by
    unfold frac
    rw [Finset.card_product]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((goodSeeds (R ×ˢ C) (fun p => acc p.1 p.2)).card : ℚ) ≤ (R.card : ℚ) := by
      exact_mod_cast hcard
    nlinarith
  exact absurd hle (not_le.2 h)
