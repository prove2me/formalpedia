-- Prove2me | Theorems.Thm_DestructiveVerification_transcript_indistinguishable_card
-- name    : DestructiveVerification.transcript_indistinguishable_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:10:41.770423+00:00
-- url     : https://prove2.me/theorems/d42ca5bf-51c2-4d08-9c0b-16b6b05a455a
-- title:
--   Sharpened indistinguishability.
-- statement:
--   **Sharpened indistinguishability.**  If two dishes give the same verdict for
--   the first `#D` runs of a test, they give the same verdict forever.  This matches
--   the destruction-depth horizon: `#D` runs settle every question that repeated
--   testing can ask about a dish.
--
--   ```lean
--   theorem DestructiveVerification.transcript_indistinguishable_card[Fintype D] (t : Test D) (d e : D)
--       (h : ∀ j < Fintype.card D, transcript t d j = transcript t e j) (m : ℕ) :
--       transcript t d m = transcript t e m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DestructiveVerificationSharpBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DestructiveVerificationSharpBound.lean#L197

-- Thm stub generated from Combinatorics/DestructiveVerificationSharpBound.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationIndistinguishability
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
/-
# Destructive verification VI: `#D` runs decide everything

`Combinatorics.DestructiveVerificationIndistinguishability` proves that two
dishes agreeing on the first `2 · #D` verdicts of a test agree forever.  This
file halves the constant: **`#D` runs suffice**, matching the destruction-depth
horizon of `transcript_rigid`.  So a single number — the number of dishes —
governs both phenomena: after `#D` runs a transcript can no longer change its
mind, and after `#D` runs two dishes can no longer part company.

The improvement needs genuinely more structure than the previous bound.  We
replace the pigeonhole recurrence by the **minimal** recurrence of an orbit
(`DestructiveVerification.exists_minimal_recurrence`), which gives three things
at once: the first `i + p` orbit points are pairwise distinct (so `i + p ≤ #D`),
every orbit point is one of them, and the period `p` divides every eventual
period of the orbit (`period_dvd_of_eventual_period`).

Then the two orbits are compared by an **orbit dichotomy**:

* if they never meet, their point sets are disjoint, so
  `(i₁ + p₁) + (i₂ + p₂) ≤ #D` and the Fine–Wilf window
  `max i₁ i₂ + p₁ + p₂ - gcd p₁ p₂` fits inside `#D`;
* if they do meet (`orbit_period_eq_of_meet`), each period is an eventual period
  of the other orbit, so `p₁ = p₂`, the gcd absorbs one of them, and the window
  collapses to `max i₁ i₂ + p₁ ≤ #D`.

Main results: `DestructiveVerification.transcript_indistinguishable_card` and
its prefix form `DestructiveVerification.indistinguishable_iff_card_prefix`.
Exhaustive enumeration (see `ComputationalEvidence.md`) shows the true threshold
is `#D - 1`; the remaining gap of one is recorded as Conjecture 1 of
`FUTURE_DIRECTIONS.md`.
-/

open DestructiveVerification

variable {D : Type*}

/-! ## 1. The minimal recurrence of an orbit -/






/-! ## 2. The orbit dichotomy -/



/-! ## 3. `#D` runs decide observational equivalence -/

theorem DestructiveVerification.transcript_indistinguishable_card[Fintype D] (t : Test D) (d e : D)
    (h : ∀ j < Fintype.card D, transcript t d j = transcript t e j) (m : ℕ) :
    transcript t d m = transcript t e m := by sorry
