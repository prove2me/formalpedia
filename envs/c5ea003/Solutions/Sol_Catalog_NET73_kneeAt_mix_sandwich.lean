-- Prove2me | solution 1 for Catalog.NET73.kneeAt_mix_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:44.583599+00:00
-- url     : https://prove2.me/submissions/8c423724-9b42-44fe-b212-dc8a10a477d1

-- Sol generated from Applications/NET73MajorizationDuality.lean
import Mathlib
import Definitions.Def_Applications_NET73KneeDecoupling
import Definitions.Def_Applications_NET73MajorizationDuality
import Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_le
import Theorems.Thm_Catalog_NET73_AttentionProfile_kneeAt_spec
import Theorems.Thm_Catalog_NET73_AttentionProfile_lt_of_lt_kneeAt
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


@[simp] lemma mixProfile_cum (lam : ℚ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P Q : AttentionProfile) (k : ℕ) :
    (mixProfile lam h0 h1 P Q).cum k = lam * P.cum k + (1 - lam) * Q.cum k := rfl





open Catalog.NET73 in
theorem solution{lam τ : ℚ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P Q : AttentionProfile) (hτ1 : τ < 1) :
    min (P.kneeAt τ) (Q.kneeAt τ) ≤ (mixProfile lam h0 h1 P Q).kneeAt τ ∧
      (mixProfile lam h0 h1 P Q).kneeAt τ ≤ max (P.kneeAt τ) (Q.kneeAt τ) := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have hP : (mixProfile lam h0 h1 P Q).kneeAt τ < P.kneeAt τ :=
      lt_of_lt_of_le hlt (min_le_left _ _)
    have hQ : (mixProfile lam h0 h1 P Q).kneeAt τ < Q.kneeAt τ :=
      lt_of_lt_of_le hlt (min_le_right _ _)
    have hPc := P.lt_of_lt_kneeAt hP
    have hQc := Q.lt_of_lt_kneeAt hQ
    have hspec := (mixProfile lam h0 h1 P Q).kneeAt_spec hτ1
    rw [mixProfile_cum] at hspec
    have hA : lam * P.cum ((mixProfile lam h0 h1 P Q).kneeAt τ) ≤ lam * τ :=
      mul_le_mul_of_nonneg_left hPc.le h0
    rcases lt_or_ge lam 1 with hl | hl
    · have hB : (1 - lam) * Q.cum ((mixProfile lam h0 h1 P Q).kneeAt τ) < (1 - lam) * τ :=
        mul_lt_mul_of_pos_left hQc (by linarith)
      linarith
    · have hpos : (0 : ℚ) < lam := lt_of_lt_of_le zero_lt_one hl
      have hA' : lam * P.cum ((mixProfile lam h0 h1 P Q).kneeAt τ) < lam * τ :=
        mul_lt_mul_of_pos_left hPc hpos
      have h1l : (1 : ℚ) - lam = 0 := by linarith
      have hB : (1 - lam) * Q.cum ((mixProfile lam h0 h1 P Q).kneeAt τ) = 0 := by
        rw [h1l]; ring
      have hlamτ : lam * τ = τ := by
        have : lam = 1 := le_antisymm h1 hl
        rw [this]; ring
      linarith
  · refine (mixProfile lam h0 h1 P Q).kneeAt_le ?_
    rw [mixProfile_cum]
    have hP : τ ≤ P.cum (max (P.kneeAt τ) (Q.kneeAt τ)) :=
      le_trans (P.kneeAt_spec hτ1) (P.cum_mono (le_max_left _ _))
    have hQ : τ ≤ Q.cum (max (P.kneeAt τ) (Q.kneeAt τ)) :=
      le_trans (Q.kneeAt_spec hτ1) (Q.cum_mono (le_max_right _ _))
    nlinarith
