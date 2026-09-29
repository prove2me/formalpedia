-- Prove2me | solution 1 for Cryptography.GoodSeeds.frac_eq_one_div_card_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:34:31.307199+00:00
-- url     : https://prove2.me/submissions/3765770d-166b-4e84-a334-4d7d33b58e6b

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




/-! ### The heavy-row (splitting) lemma -/





open Cryptography.GoodSeeds in
theorem solution[DecidableEq χ]
    (hR : R.Nonempty) (hC : C.Nonempty) (f : ρ → χ)
    (hf : ∀ r ∈ R, f r ∈ C) :
    frac (R ×ˢ C) (fun p => p.2 = f p.1) = 1 / (C.card : ℚ) ∧
      ∀ r ∈ R, ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ = f r → c₂ = f r → c₁ = c₂ := by
  have hn : (0 : ℚ) < (R.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hR
  have hm : (0 : ℚ) < (C.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hC
  constructor
  · have hrow : ∀ r ∈ R, (goodSeeds C (fun c => c = f r)).card = 1 := by
      intro r hr
      have : goodSeeds C (fun c => c = f r) = {f r} := by
        ext c
        simp only [mem_goodSeeds, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hf r hr, h⟩⟩
      rw [this, Finset.card_singleton]
    have hcard : (goodSeeds (R ×ˢ C) (fun p => p.2 = f p.1)).card = R.card := by
      rw [card_good_product_eq_sum_rows (R := R) (C := C) (acc := fun r c => c = f r)]
      rw [Finset.sum_congr rfl hrow]
      simp
    unfold frac
    rw [hcard, Finset.card_product]
    push_cast
    field_simp
  · intro r _ c₁ _ c₂ _ h₁ h₂
    rw [h₁, h₂]
