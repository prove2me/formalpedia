-- Prove2me | solution 1 for Cryptography.GoodSeeds.exists_two_accepting_challenges_of_heavy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:34:30.168217+00:00
-- url     : https://prove2.me/submissions/4e0615f5-0f85-496a-82d3-ffb4d638e6c4

-- Sol generated from Cryptography/GoodSeeds/Rewinding.lean
import Mathlib
import Definitions.Def_Cryptography_GoodSeeds_Core
import Definitions.Def_Cryptography_GoodSeeds_Rewinding
import Theorems.Thm_Cryptography_GoodSeeds_frac_congr
import Theorems.Thm_Cryptography_GoodSeeds_frac_eq_zero_iff
import Theorems.Thm_Cryptography_GoodSeeds_heavy_row_lemma_general
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




/-! ### The rewinding threshold -/




/-! ### The heavy-row (splitting) lemma -/


/-- **The heavy-row lemma.**  At least an `e / 2` fraction of the prover
randomnesses are themselves `e / 2`-heavy, where `e` is the global accepting
fraction.  (Specialisation `α = 1/2` of `heavy_row_lemma_general`.) -/
theorem heavy_row_lemma (hR : R.Nonempty) (hC : C.Nonempty) {e : ℚ}
    (he : e = frac (R ×ˢ C) (fun p => acc p.1 p.2)) :
    e / 2 ≤ frac R (fun r => e / 2 ≤ frac C (acc r)) := by
  have h := heavy_row_lemma_general (R := R) (C := C) (acc := acc) hR hC
    (α := 1/2) (e := e) (by norm_num) he
  have h1 : (1 - (1/2 : ℚ)) * e = e / 2 := by ring
  have h2 : ∀ r : ρ, ((1/2 : ℚ) * e ≤ frac C (acc r)) ↔ (e / 2 ≤ frac C (acc r)) := by
    intro r; rw [show (1/2 : ℚ) * e = e / 2 by ring]
  rw [h1] at h
  refine h.trans (le_of_eq (frac_congr fun r _ => (h2 r)))



open Cryptography.GoodSeeds in
theorem solution(hR : R.Nonempty) (hC : C.Nonempty)
    {e : ℚ} (he : e = frac (R ×ˢ C) (fun p => acc p.1 p.2))
    (hbig : 2 / (C.card : ℚ) < e) :
    ∃ r ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ ∧ acc r c₁ ∧ acc r c₂ := by
  classical
  have hm : (0 : ℚ) < (C.card : ℚ) := by exact_mod_cast Finset.card_pos.2 hC
  have hheavy := heavy_row_lemma (R := R) (C := C) (acc := acc) hR hC he
  have hepos : 0 < e := lt_of_le_of_lt (by positivity) hbig
  -- some row is heavy
  have hne : (goodSeeds R (fun r => e / 2 ≤ frac C (acc r))).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have : frac R (fun r => e / 2 ≤ frac C (acc r)) = 0 := by
      refine (frac_eq_zero_iff hR).2 ?_
      intro r hrR hPr
      have : r ∈ goodSeeds R (fun r => e / 2 ≤ frac C (acc r)) := mem_goodSeeds.2 ⟨hrR, hPr⟩
      rw [hemp] at this
      simp at this
    rw [this] at hheavy
    linarith
  obtain ⟨r, hr⟩ := hne
  obtain ⟨hrR, hrheavy⟩ := mem_goodSeeds.1 hr
  -- a heavy row has more than one accepting challenge
  have h1 : 1 / (C.card : ℚ) < frac C (acc r) := by
    have : 1 / (C.card : ℚ) < e / 2 := by
      rw [div_lt_div_iff₀ hm (by norm_num)]
      rw [div_lt_iff₀ hm] at hbig
      linarith
    linarith
  have hcard : 1 < (goodSeeds C (acc r)).card := by
    by_contra hle
    push_neg at hle
    have : ((goodSeeds C (acc r)).card : ℚ) ≤ 1 := by exact_mod_cast hle
    have : frac C (acc r) ≤ 1 / (C.card : ℚ) := by
      unfold frac
      rw [div_le_div_iff₀ hm hm]
      nlinarith
    linarith
  obtain ⟨c₁, hc₁, c₂, hc₂, hne12⟩ := Finset.one_lt_card.1 hcard
  exact ⟨r, hrR, c₁, (mem_goodSeeds.1 hc₁).1, c₂, (mem_goodSeeds.1 hc₂).1, hne12,
    (mem_goodSeeds.1 hc₁).2, (mem_goodSeeds.1 hc₂).2⟩
