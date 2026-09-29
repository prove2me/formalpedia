-- Prove2me | Theorems.Thm_Catalog_NET73_majorizes_of_kneeDominates
-- name    : Catalog.NET73.majorizes_of_kneeDominates
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:28:26.64491+00:00
-- url     : https://prove2.me/theorems/3c7e4233-1219-439e-96d2-b7a920172248
-- title:
--   Knee dominance implies majorization: if `P` ever captured strictly less at
-- statement:
--   Knee dominance implies majorization: if `P` ever captured strictly less at
--   some `k`, a tolerance placed in the gap would make `P` need more keys.
--
--   ```lean
--   theorem Catalog.NET73.majorizes_of_kneeDominates{P Q : AttentionProfile}
--       (h : KneeDominates P Q) : CaptureMajorizes P Q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/NET73MajorizationDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/NET73MajorizationDuality.lean#L47

-- Thm stub generated from Applications/NET73MajorizationDuality.lean
import Mathlib
import Definitions.Def_Applications_NET73KneeDecoupling
import Definitions.Def_Applications_NET73MajorizationDuality
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

theorem Catalog.NET73.majorizes_of_kneeDominates{P Q : AttentionProfile}
    (h : KneeDominates P Q) : CaptureMajorizes P Q := by sorry
