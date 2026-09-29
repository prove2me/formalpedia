-- Prove2me | solution 1 for DestructiveVerification.transcript_indistinguishable_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:52:05.268428+00:00
-- url     : https://prove2.me/submissions/8987a7c3-1ff6-41cb-8249-000b83c48f48

-- Sol generated from Combinatorics/DestructiveVerificationSharpBound.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationIndistinguishability
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
import Theorems.Thm_DestructiveVerification_card_add_card_le_of_disjoint
import Theorems.Thm_DestructiveVerification_exists_orbit_recurrence
import Theorems.Thm_DestructiveVerification_iterate_period_of_recurrence
import Theorems.Thm_DestructiveVerification_orbit_period_eq_of_meet
import Theorems.Thm_DestructiveVerification_transcript_agree_of_window
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


/-- **Minimal recurrence.**  Every orbit in a finite dish space has a shortest
recurrence `f^[i+p] d = f^[i] d`; its first `i + p` points are pairwise
distinct. -/
theorem exists_minimal_recurrence [Fintype D] (f : D → D) (d : D) :
    ∃ i p, 0 < p ∧ f^[i + p] d = f^[i] d ∧
      (∀ a b, a < b → b < i + p → f^[a] d ≠ f^[b] d) := by
  classical
  have hex : ∃ k, ∃ i p, 0 < p ∧ i + p = k ∧ f^[k] d = f^[i] d := by
    obtain ⟨i, p, hp, _, hrec⟩ := exists_orbit_recurrence f d
    exact ⟨i + p, i, p, hp, rfl, hrec⟩
  obtain ⟨i, p, hp, hik, hrec⟩ := Nat.find_spec hex
  refine ⟨i, p, hp, by rw [hik]; exact hrec, ?_⟩
  intro a b hab hb hcon
  have hmin := Nat.find_min hex (m := b) (by omega)
  exact hmin ⟨a, b - a, by omega, by omega, hcon.symm⟩

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

theorem minimal_recurrence_card_le [Fintype D] {f : D → D} {d : D} {i p : ℕ}
    (hdist : ∀ a b, a < b → b < i + p → f^[a] d ≠ f^[b] d) :
    i + p ≤ Fintype.card D := by
  classical
  have h := card_orbit_of_minimal (f := f) (d := d) (i := i) (p := p) hdist
  have hle := Finset.card_le_univ ((Finset.range (i + p)).image (fun j => f^[j] d))
  omega


/-! ## 2. The orbit dichotomy -/



/-! ## 3. `#D` runs decide observational equivalence -/




open DestructiveVerification in
theorem solution[Fintype D] (t : Test D) (d e : D)
    (h : ∀ j < Fintype.card D, transcript t d j = transcript t e j) (m : ℕ) :
    transcript t d m = transcript t e m := by
  classical
  set f := residue t with hf
  obtain ⟨i₁, p₁, hp₁, hrec₁, hdist₁⟩ := exists_minimal_recurrence f d
  obtain ⟨i₂, p₂, hp₂, hrec₂, hdist₂⟩ := exists_minimal_recurrence f e
  have hle₁ : i₁ + p₁ ≤ Fintype.card D := minimal_recurrence_card_le hdist₁
  have hle₂ : i₂ + p₂ ≤ Fintype.card D := minimal_recurrence_card_le hdist₂
  have hper₁ : ∀ m, i₁ ≤ m → transcript t d (m + p₁) = transcript t d m := by
    intro m hm
    simp only [transcript]
    rw [iterate_period_of_recurrence hrec₁ m hm]
  have hper₂ : ∀ m, i₂ ≤ m → transcript t e (m + p₂) = transcript t e m := by
    intro m hm
    simp only [transcript]
    rw [iterate_period_of_recurrence hrec₂ m hm]
  have hwindow : max i₁ i₂ + p₁ + p₂ - Nat.gcd p₁ p₂ ≤ Fintype.card D := by
    by_cases hmeet : ∃ a b, f^[a] d = f^[b] e
    · obtain ⟨a, b, hab⟩ := hmeet
      have hpp : p₁ = p₂ :=
        orbit_period_eq_of_meet hp₁ hrec₁ hdist₁ hp₂ hrec₂ hdist₂ hab
      subst hpp
      have hg : Nat.gcd p₁ p₁ = p₁ := Nat.gcd_self p₁
      rw [hg]
      omega
    · push_neg at hmeet
      have hsum := card_add_card_le_of_disjoint hdist₁ hdist₂ hmeet
      omega
  exact transcript_agree_of_window t d e hp₁ hp₂ hper₁ hper₂ hwindow h m
