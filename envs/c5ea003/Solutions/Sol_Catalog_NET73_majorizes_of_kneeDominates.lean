-- Prove2me | solution 1 for Catalog.NET73.majorizes_of_kneeDominates
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:45.851466+00:00
-- url     : https://prove2.me/submissions/32c76867-487b-4d76-9919-206bbdae7c10

-- Sol generated from Applications/NET73MajorizationDuality.lean
import Mathlib
import Definitions.Def_Applications_NET73KneeDecoupling
import Definitions.Def_Applications_NET73MajorizationDuality
import Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_le
import Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_spec
/-
# NET-73, cycle 3: knee dominance is exactly majorization, and mixtures are sandwiched

Cycles 1–2 refuted tokens-per-word as the mechanism and identified concentration
statistics as the controlling quantities.  This cycle asks: *how much* of a
domain does the knee curve `τ ↦ k*(τ)` remember, and what happens to a corpus
that mixes domains?

* `Catalog.NET73.kneeDominates_iff_majorizes` — **duality.**  One domain needs
  no more keys than another at *every* tolerance iff its capture curve dominates
  pointwise, i.e. iff its attention mass vector majorizes the other's.  So the
  knee curve is a faithful order-isomorphic shadow of the majorization order on
  attention profiles — the "relational structure" NET-73 points at is exactly a
  majorization order.
* `Catalog.NET73.knee_curve_determines_capture` — the knee curve determines the
  capture curve: two domains with the same knees at all tolerances have the same
  attention concentration (though possibly wildly different tokenizers).
* `Catalog.NET73.kneeAt_mix_sandwich` — **mixtures interleave.**  A corpus that
  mixes two domains with weights `λ, 1-λ` has a knee between the two component
  knees: `min ≤ k*_mix(τ) ≤ max`.  Consequence
  (`mixed_corpus_knee_between`): mixing a code-like domain (small knee) with a
  French-like domain (large knee) can never push the knee outside the observed
  range, so the NET-73 spread is not a mixing artefact.
-/

open Catalog.NET73

open AttentionProfile

/-! ## 1. Two orders on domains -/







/-! ## 2. Mixed corpora -/







open Catalog.NET73 in
theorem solution{P Q : AttentionProfile}
    (h : KneeDominates P Q) : CaptureMajorizes P Q := by
  intro k
  by_contra hlt
  push_neg at hlt
  have hP0 : 0 ≤ P.cum k := by
    have := P.cum_mono (Nat.zero_le k)
    rwa [P.cum_zero] at this
  have hQ1 : Q.cum k ≤ 1 := Q.cum_le_one k
  set τ := (P.cum k + Q.cum k) / 2 with hτdef
  have hτ0 : 0 < τ := by rw [hτdef]; linarith
  have hτ1 : τ < 1 := by rw [hτdef]; linarith
  have hPτ : P.cum k < τ := by rw [hτdef]; linarith
  have hτQ : τ ≤ Q.cum k := by rw [hτdef]; linarith
  have hQle : Q.kneeAt τ ≤ k := Q.kneeAt_le hτQ
  have hPgt : k < P.kneeAt τ := by
    by_contra hle
    push_neg at hle
    have hmono := P.cum_mono hle
    have hspec := P.kneeAt_spec hτ1
    linarith
  have hdom := h τ hτ0 hτ1
  omega
