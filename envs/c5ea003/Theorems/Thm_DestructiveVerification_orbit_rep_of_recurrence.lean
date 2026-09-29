-- Prove2me | Theorems.Thm_DestructiveVerification_orbit_rep_of_recurrence
-- name    : DestructiveVerification.orbit_rep_of_recurrence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:10:53.547124+00:00
-- url     : https://prove2.me/theorems/9c5040ab-dd05-48a0-80d6-fe2dcb4e560b
-- title:
--   Every orbit point of `d` is one of the first `i + p` points, once
-- statement:
--   Every orbit point of `d` is one of the first `i + p` points, once
--   `f^[i+p] d = f^[i] d`.
--
--   ```lean
--   theorem DestructiveVerification.orbit_rep_of_recurrence{f : D → D} {d : D} {i p : ℕ} (hp : 0 < p)
--       (hrec : f^[i + p] d = f^[i] d) (m : ℕ) : ∃ j < i + p, f^[m] d = f^[j] d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DestructiveVerificationSharpBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DestructiveVerificationSharpBound.lean#L44

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

theorem DestructiveVerification.orbit_rep_of_recurrence{f : D → D} {d : D} {i p : ℕ} (hp : 0 < p)
    (hrec : f^[i + p] d = f^[i] d) (m : ℕ) : ∃ j < i + p, f^[m] d = f^[j] d := by sorry
