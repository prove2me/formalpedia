-- Prove2me | solution 1 for DestructiveVerification.orbit_rep_of_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:48:54.165781+00:00
-- url     : https://prove2.me/submissions/bc302528-04ed-4651-97d5-6d592d930a11

-- Sol generated from Combinatorics/DestructiveVerificationSharpBound.lean
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




open DestructiveVerification in
theorem solution{f : D → D} {d : D} {i p : ℕ} (hp : 0 < p)
    (hrec : f^[i + p] d = f^[i] d) (m : ℕ) : ∃ j < i + p, f^[m] d = f^[j] d := by
  by_cases hm : m < i
  · exact ⟨m, by omega, rfl⟩
  · push_neg at hm
    have hy : Function.IsPeriodicPt f p (f^[i] d) := by
      show f^[p] (f^[i] d) = f^[i] d
      rw [← Function.iterate_add_apply, Nat.add_comm p i]
      exact hrec
    refine ⟨i + (m - i) % p, by have := Nat.mod_lt (m - i) hp; omega, ?_⟩
    have h1 : f^[m] d = f^[m - i] (f^[i] d) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    have h2 : f^[i + (m - i) % p] d = f^[(m - i) % p] (f^[i] d) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [h1, h2, hy.iterate_mod_apply]
