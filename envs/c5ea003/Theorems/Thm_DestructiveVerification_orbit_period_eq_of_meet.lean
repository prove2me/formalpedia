-- Prove2me | Theorems.Thm_DestructiveVerification_orbit_period_eq_of_meet
-- name    : DestructiveVerification.orbit_period_eq_of_meet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:10:52.785968+00:00
-- url     : https://prove2.me/theorems/b27f7289-11b8-4fa4-9ac0-f96d996aa5a4
-- title:
--   If two orbits meet, their minimal periods coincide: they are running around
-- statement:
--   If two orbits meet, their minimal periods coincide: they are running around
--   the same cycle.
--
--   ```lean
--   theorem DestructiveVerification.orbit_period_eq_of_meet[Fintype D] {f : D → D} {d e : D} {i₁ p₁ i₂ p₂ : ℕ}
--       (hp₁ : 0 < p₁) (hrec₁ : f^[i₁ + p₁] d = f^[i₁] d)
--       (hdist₁ : ∀ a b, a < b → b < i₁ + p₁ → f^[a] d ≠ f^[b] d)
--       (hp₂ : 0 < p₂) (hrec₂ : f^[i₂ + p₂] e = f^[i₂] e)
--       (hdist₂ : ∀ a b, a < b → b < i₂ + p₂ → f^[a] e ≠ f^[b] e)
--       {a b : ℕ} (hab : f^[a] d = f^[b] e) : p₁ = p₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DestructiveVerificationSharpBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DestructiveVerificationSharpBound.lean#L137

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

theorem DestructiveVerification.orbit_period_eq_of_meet[Fintype D] {f : D → D} {d e : D} {i₁ p₁ i₂ p₂ : ℕ}
    (hp₁ : 0 < p₁) (hrec₁ : f^[i₁ + p₁] d = f^[i₁] d)
    (hdist₁ : ∀ a b, a < b → b < i₁ + p₁ → f^[a] d ≠ f^[b] d)
    (hp₂ : 0 < p₂) (hrec₂ : f^[i₂ + p₂] e = f^[i₂] e)
    (hdist₂ : ∀ a b, a < b → b < i₂ + p₂ → f^[a] e ≠ f^[b] e)
    {a b : ℕ} (hab : f^[a] d = f^[b] e) : p₁ = p₂ := by sorry
