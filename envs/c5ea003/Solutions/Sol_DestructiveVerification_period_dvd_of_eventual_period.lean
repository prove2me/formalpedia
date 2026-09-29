-- Prove2me | solution 1 for DestructiveVerification.period_dvd_of_eventual_period
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:47:19.961405+00:00
-- url     : https://prove2.me/submissions/30acb215-c919-4cc3-98c3-86ae523356f3

-- Sol generated from Combinatorics/DestructiveVerificationSharpBound.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationIndistinguishability
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
import Theorems.Thm_DestructiveVerification_eq_mod_period
import Theorems.Thm_DestructiveVerification_iterate_period_of_recurrence
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
theorem solution[Fintype D] {f : D → D} {d : D} {i p : ℕ}
    (hp : 0 < p) (hrec : f^[i + p] d = f^[i] d)
    (hdist : ∀ a b, a < b → b < i + p → f^[a] d ≠ f^[b] d)
    {q J : ℕ} (hJ : ∀ m, J ≤ m → f^[m + q] d = f^[m] d) :
    p ∣ q := by
  set s : ℕ → D := fun m => f^[i + m] d with hs
  have hsper : ∀ m, s (m + p) = s m := by
    intro m
    have h1 : i + (m + p) = (i + m) + p := by omega
    simp only [hs, h1]
    exact iterate_period_of_recurrence hrec (i + m) (by omega)
  have hsmod : ∀ m, s m = s (m % p) := eq_mod_period s hp hsper
  set M := i + p * (J + 1) with hM
  have hMJ : J ≤ M := by nlinarith
  have hM1 : f^[M] d = f^[i] d := by
    have : f^[M] d = s (p * (J + 1)) := rfl
    rw [this, hsmod (p * (J + 1))]
    simp [hs, Nat.mul_mod_right]
  have hM2 : f^[M + q] d = f^[i + q % p] d := by
    have h1 : f^[M + q] d = s (p * (J + 1) + q) := by
      simp only [hs, hM]; congr 1; omega
    rw [h1, hsmod (p * (J + 1) + q)]
    have h2 : (p * (J + 1) + q) % p = q % p := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [h2]
  have hkey : f^[i + q % p] d = f^[i] d := by rw [← hM2, hJ M hMJ, hM1]
  by_contra hcon
  have hr : 0 < q % p := by
    rcases Nat.eq_zero_or_pos (q % p) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hcon
    · exact h
  have hrlt : q % p < p := Nat.mod_lt _ hp
  exact hdist i (i + q % p) (by omega) (by omega) hkey.symm
