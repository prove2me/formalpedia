-- Prove2me | solution 1 for DestructiveVerification.card_add_card_le_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:38:25.221739+00:00
-- url     : https://prove2.me/submissions/a4e6fee7-1e3b-4d19-948a-89e7a3b2d0c8

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



/-- The points of a minimal recurrence are `i + p` distinct dishes, so
`i + p ≤ #D`. -/
theorem card_orbit_of_minimal [Fintype D] [DecidableEq D] {f : D → D} {d : D} {i p : ℕ}
    (hdist : ∀ a b, a < b → b < i + p → f^[a] d ≠ f^[b] d) :
    ((Finset.range (i + p)).image (fun j => f^[j] d)).card = i + p := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hdist a b h hb hab
  · exact hdist b a h ha hab.symm



/-! ## 2. The orbit dichotomy -/



/-! ## 3. `#D` runs decide observational equivalence -/




open DestructiveVerification in
theorem solution[Fintype D] [DecidableEq D] {f : D → D} {d e : D} {i₁ p₁ i₂ p₂ : ℕ}
    (hdist₁ : ∀ a b, a < b → b < i₁ + p₁ → f^[a] d ≠ f^[b] d)
    (hdist₂ : ∀ a b, a < b → b < i₂ + p₂ → f^[a] e ≠ f^[b] e)
    (hmeet : ∀ a b, f^[a] d ≠ f^[b] e) :
    (i₁ + p₁) + (i₂ + p₂) ≤ Fintype.card D := by
  set S₁ := (Finset.range (i₁ + p₁)).image (fun j => f^[j] d) with hS₁
  set S₂ := (Finset.range (i₂ + p₂)).image (fun j => f^[j] e) with hS₂
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    rintro x hx₁ hx₂
    simp only [hS₁, hS₂, Finset.mem_image, Finset.mem_range] at hx₁ hx₂
    obtain ⟨j₁, -, rfl⟩ := hx₁
    obtain ⟨j₂, -, hj₂⟩ := hx₂
    exact hmeet j₁ j₂ hj₂.symm
  have hcard : S₁.card + S₂.card = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
  rw [card_orbit_of_minimal hdist₁, card_orbit_of_minimal hdist₂] at hcard
  rw [hcard]
  exact Finset.card_le_univ _
