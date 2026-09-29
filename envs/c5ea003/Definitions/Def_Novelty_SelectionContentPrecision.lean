-- Prove2me | Definitions.Def_Novelty_SelectionContentPrecision
-- name    : Novelty_SelectionContentPrecision
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:28.720344+00:00
-- url     : https://prove2.me/theorems/80390679-183c-4fa1-b68b-c6a344f17c0e
-- title:
--   Aether Catalog definitions — Novelty_SelectionContentPrecision
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SelectionContentPrecision`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SelectionContentPrecision.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation

/-!
# Selection interfaces carry precision requirements; content containers do not

This file formalises the *structural law* extracted in NET-95, the one that
explains why the weight axis and the cache-key axis behave so differently under
quantisation:

* weights and cache **values** are *content containers*: they are consumed by a
  convex (probability-weighted) average, so a `δ`-accurate quantiser perturbs the
  output by at most `δ`.  Degradation has a modulus of continuity in the
  quantiser step — it can only fall off smoothly, which is exactly the measured
  behaviour of the k-quant ladder from 6.6 down to 2.6 bpw
  (`Novelty.WeightQuantFloorLadder`).
* cache **keys** are a *selection interface*: they are consumed by an `argmax`.
  We prove that no modulus of continuity exists at all: for every `δ > 0` and
  every target error `C`, there is a score configuration and a `δ`-accurate
  quantiser whose top-1 decision flips and whose read-out error is exactly `C`.
  This is the wall that NET-92/93 measured between 8-bit and 5-bit keys.

The dissociation is therefore not empirical folklore but a theorem:
`content_smooth_selection_cliff`.

We build on `Novelty.KVDecisionDissociation`, reusing `IsStrictTop` (the top-1
decision) and `strictTop_of_margin` (the margin certificate), and add the
quantisation-theoretic layer:

* `content_error_le` / `content_error_sharp` — content error is exactly `Θ(δ)`.
* `selection_flip_at_every_precision` — selection error is `Θ(1)`, at every `δ`.
* `selection_has_no_modulus_of_continuity` — hence no bound `f(δ)` can exist.
* `selection_stable_at_bit_depth` / `selection_unstable_at_bit_depth` — the cliff
  is located at `b ≈ log₂(1/g)` where `g` is the top-1 margin: `b` bits are enough
  when `2 / 2 ^ b < g`, and are already too few when `g ≤ 1 / 2 ^ b`.
* `flips_le_small_margin_count` — the quantitative version over a whole sequence:
  the number of positions whose decision breaks is at most the number of
  positions whose margin is below `2 δ`.  The cliff is the margin distribution's
  cumulative mass, not a property of the bit width.
-/

namespace Catalog.Novelty.SelectionContentPrecision

open Finset Catalog.Novelty.KVDecisionDissociation

/-- A quantiser that is accurate to within `δ` everywhere. -/
def IsDeltaAccurate (q : ℝ → ℝ) (δ : ℝ) : Prop := ∀ x, |q x - x| ≤ δ

/-- A probability weight vector (the attention distribution). -/
def IsProb {n : ℕ} (p : Fin n → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-! ## 1. Content containers have a modulus of continuity -/



/-! ## 2. Selection interfaces have none -/




/-! ## 3. Where the key cliff sits: the margin, not the bit width -/



/-! ## 4. How many decisions break: the margin distribution -/


end Catalog.Novelty.SelectionContentPrecision


