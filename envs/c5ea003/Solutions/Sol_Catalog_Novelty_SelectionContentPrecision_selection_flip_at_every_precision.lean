-- Prove2me | solution 1 for Catalog.Novelty.SelectionContentPrecision.selection_flip_at_every_precision
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:21:29.595579+00:00
-- url     : https://prove2.me/submissions/249d5edf-7b56-4404-84cd-da69496e6ec1

-- Sol generated from Novelty/SelectionContentPrecision.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation
import Definitions.Def_Novelty_SelectionContentPrecision

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

open Catalog.Novelty.SelectionContentPrecision

open Finset Catalog.Novelty.KVDecisionDissociation



/-! ## 1. Content containers have a modulus of continuity -/



/-! ## 2. Selection interfaces have none -/




/-! ## 3. Where the key cliff sits: the margin, not the bit width -/



/-! ## 4. How many decisions break: the margin distribution -/



open Catalog.Novelty.SelectionContentPrecision in
theorem solution(δ C : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) :
    ∃ (u val : Fin 2 → ℝ) (q : ℝ → ℝ),
      IsDeltaAccurate q δ ∧ IsStrictTop u 0 ∧ IsStrictTop (fun i => q (u i)) 1 ∧
        |val 1 - val 0| = C ∧ u 0 - u 1 ≤ δ := by
  refine ⟨![δ / 2, 0], ![0, C], fun x => if x ≤ δ / 4 then x + δ / 2 else x - δ / 2, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ≤ δ / 4 <;> simp [hx] <;>
      rw [abs_of_nonneg (by linarith)] <;> linarith
  · intro j hj
    fin_cases j
    · exact absurd rfl hj
    · simpa using hδ
  · intro j hj
    fin_cases j
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hle : (0:ℝ) ≤ δ / 4 := by linarith
      have hnot : ¬ (δ / 2 ≤ δ / 4) := by intro h; linarith
      simp [hle, hnot]
      linarith
    · exact absurd rfl hj
  · exact ⟨by simp [abs_of_nonneg hC], by simp; linarith⟩
