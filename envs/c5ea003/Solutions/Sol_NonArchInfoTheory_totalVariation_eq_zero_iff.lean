-- Prove2me | solution 1 for NonArchInfoTheory.totalVariation_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:45:24.361896+00:00
-- url     : https://prove2.me/submissions/73f84543-4428-4ebb-ba68-f5a71af494f9

/-
# `NonArchInfoTheory.totalVariation_eq_zero_iff`
Target `bcec551d` (Open; re-read live immediately before submitting).

ORDINARY PROOF — `Def_Bridges_MinEntropy` is built and its closure screens CLEAN. Gift: **SAFE**.

BINDERS. History is `CE,CE,CE,CE,CE,CE` — **no WA has ever published an expected type here**, so
unlike most targets tonight the telescope is read off the statement plus the section variable line
(`variable {α : Type*} [Fintype α]`, line 31/42): `{α : Type*} [Fintype α] (μ ν : FinProbDist α)`.
This is the case where I cannot check against a rejection, so the type-match gate is the only
authority.

DEFINITIONS (read from source):
    structure FinProbDist (α) [Fintype α] where
      mass : α → ℝ ; mass_nonneg : ∀ x, 0 ≤ mass x ; mass_sum_one : ∑ x, mass x = 1
    totalVariation μ ν = (1 / 2) * ∑ x, |μ.mass x - ν.mass x|

MATHS. A sum of NON-NEGATIVE terms vanishes exactly when every term does, and `|r| = 0 ↔ r = 0`,
so the distance is zero precisely when the masses agree pointwise — which is equality of the
distributions.

THE STRUCTURE-EQUALITY STEP IS THE CRUX, and it is not `ext`. `#check @FinProbDist.ext` returns
**Unknown constant**: no extensionality lemma is generated for this structure. Equality must come from
`cases p; cases q; congr` — the two remaining fields are PROPOSITIONS, hence proof-irrelevant, so
`congr` discharges them and only the `mass` field survives as a goal. That route was verified in a
probe (all five examples compiled) before this file was written; an earlier probe had aborted at the
failing `#check` and therefore tested none of it.

PROBED, NOT GUESSED — each `#check`ed, with the exact shape recorded:
  * `Finset.sum_eq_zero_iff_of_nonneg : (∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)`
    — note `{f}` and `{s}` are IMPLICIT.
  * `abs_eq_zero : |a| = 0 ↔ a = 0`   ·   `sub_eq_zero : a - b = 0 ↔ a = b`
  * `rw [totalVariation]` unfolds directly (a plain def).
-/
import Mathlib
import Definitions.Def_Bridges_MinEntropy

set_option autoImplicit false
set_option maxHeartbeats 400000

open NonArchInfoTheory Finset

open NonArchInfoTheory in
/-- **The target, verbatim.** -/
theorem solution {α : Type*} [Fintype α] (μ ν : FinProbDist α) :
    totalVariation μ ν = 0 ↔ μ = ν := by
  -- no `ext` lemma exists for this structure; Prop fields are proof-irrelevant, so `congr` suffices
  have hext : ∀ (p q : FinProbDist α), (∀ x, p.mass x = q.mass x) → p = q := by
    intro p q hpq
    cases p; cases q; congr; funext x; exact hpq x
  constructor
  · intro h
    rw [totalVariation] at h
    have hS : (∑ x : α, |μ.mass x - ν.mass x|) = 0 := by linarith
    have hnn : ∀ i ∈ (Finset.univ : Finset α), 0 ≤ |μ.mass i - ν.mass i| :=
      fun i _ => abs_nonneg _
    refine hext μ ν ?_
    intro x
    have hx := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS x (Finset.mem_univ x)
    exact sub_eq_zero.mp (abs_eq_zero.mp hx)
  · intro h
    subst h
    rw [totalVariation]
    simp
