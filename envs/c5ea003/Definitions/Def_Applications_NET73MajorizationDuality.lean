-- Prove2me | Definitions.Def_Applications_NET73MajorizationDuality
-- name    : Applications_NET73MajorizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:09.725448+00:00
-- url     : https://prove2.me/theorems/f7f0bf38-f404-42c9-bf01-4b4fb68a1810
-- title:
--   Aether Catalog definitions — Applications_NET73MajorizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NET73MajorizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NET73MajorizationDuality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_NET73KneeDecoupling
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

namespace Catalog.NET73

open AttentionProfile

/-! ## 1. Two orders on domains -/

/-- `P` needs no more keys than `Q`, at every admissible tolerance. -/
def KneeDominates (P Q : AttentionProfile) : Prop :=
  ∀ τ : ℚ, 0 < τ → τ < 1 → P.kneeAt τ ≤ Q.kneeAt τ

/-- `P`'s attention is at least as concentrated as `Q`'s: its top-`k` keys
capture at least as much mass, for every `k`.  For mass vectors of equal total
this is exactly the majorization order. -/
def CaptureMajorizes (P Q : AttentionProfile) : Prop := ∀ k, Q.cum k ≤ P.cum k





/-! ## 2. Mixed corpora -/

/-- A corpus mixing two domains with weights `lam` and `1 - lam`. -/
noncomputable def mixProfile (lam : ℚ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P Q : AttentionProfile) : AttentionProfile where
  tpw := lam * P.tpw + (1 - lam) * Q.tpw
  cum := fun k => lam * P.cum k + (1 - lam) * Q.cum k
  cum_zero := by simp [P.cum_zero, Q.cum_zero]
  cum_mono := by
    intro a b hab
    have hP := P.cum_mono hab
    have hQ := Q.cum_mono hab
    have : (0 : ℚ) ≤ 1 - lam := by linarith
    nlinarith
  cum_le_one := by
    intro k
    have hP := P.cum_le_one k
    have hQ := Q.cum_le_one k
    nlinarith
  approaches_one := by
    intro τ hτ
    obtain ⟨kP, hkP⟩ := P.approaches_one τ hτ
    obtain ⟨kQ, hkQ⟩ := Q.approaches_one τ hτ
    refine ⟨max kP kQ, ?_⟩
    have hP : τ ≤ P.cum (max kP kQ) := le_trans hkP (P.cum_mono (le_max_left _ _))
    have hQ : τ ≤ Q.cum (max kP kQ) := le_trans hkQ (Q.cum_mono (le_max_right _ _))
    nlinarith





end Catalog.NET73


