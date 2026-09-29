-- Prove2me | Theorems.Thm_Cryptography_GoodSeeds_exists_two_accepting_challenges_of_heavy
-- name    : Cryptography.GoodSeeds.exists_two_accepting_challenges_of_heavy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:40:00.832511+00:00
-- url     : https://prove2.me/theorems/da918541-bac9-4d4f-b4e2-582c77887072
-- title:
--   Quantitative rewinding.
-- statement:
--   **Quantitative rewinding.**  If the accepting fraction `e` satisfies
--   `2 / |C| < e`, then a strictly positive fraction — at least `e / 2` — of the
--   prover randomnesses admit two distinct accepting challenges.
--
--   ```lean
--   theorem Cryptography.GoodSeeds.exists_two_accepting_challenges_of_heavy(hR : R.Nonempty) (hC : C.Nonempty)
--       {e : ℚ} (he : e = frac (R ×ˢ C) (fun p => acc p.1 p.2))
--       (hbig : 2 / (C.card : ℚ) < e) :
--       ∃ r ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ ∧ acc r c₁ ∧ acc r c₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/GoodSeeds/Rewinding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/GoodSeeds/Rewinding.lean#L223

-- Thm stub generated from Cryptography/GoodSeeds/Rewinding.lean
import Mathlib
import Definitions.Def_Cryptography_GoodSeeds_Core
import Definitions.Def_Cryptography_GoodSeeds_Rewinding

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

theorem Cryptography.GoodSeeds.exists_two_accepting_challenges_of_heavy(hR : R.Nonempty) (hC : C.Nonempty)
    {e : ℚ} (he : e = frac (R ×ˢ C) (fun p => acc p.1 p.2))
    (hbig : 2 / (C.card : ℚ) < e) :
    ∃ r ∈ R, ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ ∧ acc r c₁ ∧ acc r c₂ := by sorry
