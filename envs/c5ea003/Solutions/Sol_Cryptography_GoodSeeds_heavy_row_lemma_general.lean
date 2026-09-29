-- Prove2me | solution 1 for Cryptography.GoodSeeds.heavy_row_lemma_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:32:57.805212+00:00
-- url     : https://prove2.me/submissions/923ccdc5-d4a4-4656-9da9-fc8d58b042fb

-- Sol generated from Cryptography/GoodSeeds/Rewinding.lean
import Mathlib
import Definitions.Def_Cryptography_GoodSeeds_Core
import Definitions.Def_Cryptography_GoodSeeds_Rewinding
import Theorems.Thm_Cryptography_GoodSeeds_frac_le_one
import Theorems.Thm_Cryptography_GoodSeeds_frac_nonneg

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

/-- **The global accepting fraction is the average of the row fractions.** -/
theorem frac_product_eq_average_row_frac (hR : R.Nonempty) :
    frac (R ×ˢ C) (fun p => acc p.1 p.2)
      = (∑ r ∈ R, frac C (acc r)) / (R.card : ℚ) := by
  have hn : (0 : ℚ) < (R.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hR
  unfold frac
  rw [card_good_product_eq_sum_rows (R := R) (C := C) (acc := acc)]
  rw [Finset.card_product]
  push_cast
  rw [← Finset.sum_div, div_div]
  ring

/-! ### The rewinding threshold -/




/-! ### The heavy-row (splitting) lemma -/





open Cryptography.GoodSeeds in
theorem solution(hR : R.Nonempty) (hC : C.Nonempty)
    {α e : ℚ} (hα₀ : 0 < α)
    (he : e = frac (R ×ˢ C) (fun p => acc p.1 p.2)) :
    (1 - α) * e ≤ frac R (fun r => α * e ≤ frac C (acc r)) := by
  classical
  have hn : (0 : ℚ) < (R.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hR
  have hm : (0 : ℚ) < (C.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hC
  have he0 : 0 ≤ e := he ▸ frac_nonneg
  set P : ρ → Prop := fun r => α * e ≤ frac C (acc r) with hP
  set H : Finset ρ := goodSeeds R P with hH
  -- the average identity
  have havg : e * (R.card : ℚ) = ∑ r ∈ R, frac C (acc r) := by
    rw [he, frac_product_eq_average_row_frac (R := R) (C := C) (acc := acc) hR]
    field_simp
  -- split the sum over heavy and light rows
  have hsplit : ∑ r ∈ R, frac C (acc r)
      = (∑ r ∈ R.filter P, frac C (acc r)) + ∑ r ∈ R.filter (fun r => ¬ P r), frac C (acc r) :=
    (Finset.sum_filter_add_sum_filter_not R P _).symm
  have hheavy : ∑ r ∈ R.filter P, frac C (acc r) ≤ (H.card : ℚ) := by
    calc ∑ r ∈ R.filter P, frac C (acc r) ≤ ∑ _r ∈ R.filter P, (1 : ℚ) :=
          Finset.sum_le_sum fun r _ => frac_le_one
      _ = (H.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hH, goodSeeds]
  have hlight : ∑ r ∈ R.filter (fun r => ¬ P r), frac C (acc r) ≤ α * e * (R.card : ℚ) := by
    have hbound : ∀ r ∈ R.filter (fun r => ¬ P r), frac C (acc r) ≤ α * e := by
      intro r hr
      have := (Finset.mem_filter.1 hr).2
      rw [hP] at this
      exact le_of_lt (not_le.1 this)
    calc ∑ r ∈ R.filter (fun r => ¬ P r), frac C (acc r)
        ≤ ∑ _r ∈ R.filter (fun r => ¬ P r), α * e := Finset.sum_le_sum hbound
      _ = ((R.filter (fun r => ¬ P r)).card : ℚ) * (α * e) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R.card : ℚ) * (α * e) := by
          have hcle : ((R.filter (fun r => ¬ P r)).card : ℚ) ≤ (R.card : ℚ) := by
            exact_mod_cast Finset.card_filter_le R _
          have : (0 : ℚ) ≤ α * e := by positivity
          exact mul_le_mul_of_nonneg_right hcle this
      _ = α * e * (R.card : ℚ) := by ring
  -- put it together
  have hkey : (1 - α) * e * (R.card : ℚ) ≤ (H.card : ℚ) := by
    have := havg.trans_le (hsplit ▸ add_le_add hheavy hlight)
    nlinarith
  have : frac R P = (H.card : ℚ) / (R.card : ℚ) := rfl
  rw [this, le_div_iff₀ hn]
  exact hkey
