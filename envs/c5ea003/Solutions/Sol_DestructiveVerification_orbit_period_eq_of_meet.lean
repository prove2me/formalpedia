-- Prove2me | solution 1 for DestructiveVerification.orbit_period_eq_of_meet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:48:53.557559+00:00
-- url     : https://prove2.me/submissions/916ab866-1e1e-4ecb-998a-551f8eb25fdd

-- Sol generated from Combinatorics/DestructiveVerificationSharpBound.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationIndistinguishability
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
import Theorems.Thm_DestructiveVerification_iterate_period_of_recurrence
import Theorems.Thm_DestructiveVerification_period_dvd_of_eventual_period
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
theorem solution[Fintype D] {f : D → D} {d e : D} {i₁ p₁ i₂ p₂ : ℕ}
    (hp₁ : 0 < p₁) (hrec₁ : f^[i₁ + p₁] d = f^[i₁] d)
    (hdist₁ : ∀ a b, a < b → b < i₁ + p₁ → f^[a] d ≠ f^[b] d)
    (hp₂ : 0 < p₂) (hrec₂ : f^[i₂ + p₂] e = f^[i₂] e)
    (hdist₂ : ∀ a b, a < b → b < i₂ + p₂ → f^[a] e ≠ f^[b] e)
    {a b : ℕ} (hab : f^[a] d = f^[b] e) : p₁ = p₂ := by
  have hshift : ∀ c, f^[c + a] d = f^[c + b] e := by
    intro c
    rw [Function.iterate_add_apply, Function.iterate_add_apply, hab]
  -- `p₁` is an eventual period of the orbit of `e`
  have hp₁e : ∀ m, b + i₁ ≤ m → f^[m + p₁] e = f^[m] e := by
    intro m hm
    have hc : (m - b) + b = m := by omega
    have h1 : f^[m] e = f^[(m - b) + a] d := by rw [hshift (m - b), hc]
    have h2 : f^[m + p₁] e = f^[((m - b) + p₁) + b] e := by congr 1; omega
    rw [h2, ← hshift ((m - b) + p₁), h1]
    have h3 : (m - b) + p₁ + a = ((m - b) + a) + p₁ := by omega
    rw [h3]
    exact iterate_period_of_recurrence hrec₁ ((m - b) + a) (by omega)
  -- and symmetrically
  have hp₂d : ∀ m, a + i₂ ≤ m → f^[m + p₂] d = f^[m] d := by
    intro m hm
    have hc : (m - a) + a = m := by omega
    have h1 : f^[m] d = f^[(m - a) + b] e := by rw [← hshift (m - a), hc]
    have h2 : f^[m + p₂] d = f^[((m - a) + p₂) + a] d := by congr 1; omega
    rw [h2, hshift ((m - a) + p₂), h1]
    have h3 : (m - a) + p₂ + b = ((m - a) + b) + p₂ := by omega
    rw [h3]
    exact iterate_period_of_recurrence hrec₂ ((m - a) + b) (by omega)
  have hd1 : p₂ ∣ p₁ :=
    period_dvd_of_eventual_period hp₂ hrec₂ hdist₂ hp₁e
  have hd2 : p₁ ∣ p₂ :=
    period_dvd_of_eventual_period hp₁ hrec₁ hdist₁ hp₂d
  exact Nat.dvd_antisymm hd2 hd1
