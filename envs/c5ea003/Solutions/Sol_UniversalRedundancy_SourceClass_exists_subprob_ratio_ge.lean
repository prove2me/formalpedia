-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.exists_subprob_ratio_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T08:20:25.670431+00:00
-- url     : https://prove2.me/submissions/fc353a20-1497-4f88-af91-a0a034c32ecd

/-
# `UniversalRedundancy.SourceClass.exists_subprob_ratio_ge`
Target `03418397` (Open; re-read live immediately before submitting).

ORDINARY PROOF — screen CLEAN (exit 0). Gift check with the corrected logic: **SAFE**.
Bundle already built. I already own this machinery: `de54ce0e nml_sum_one` (accepted) established
boundedness of the likelihood family and `1 ≤ shtarkovSum` in this same structure.

BINDERS — no WA (history is CE,CE,CE,CE). The statement declares its arguments INLINE —
`[Nonempty Θ] (q : X → ℝ) (hq : ∑ x, q x ≤ 1)` — over the section variables
`{X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)` (bundle line 65). Gate is the authority.

WHAT THE CEs REVEAL. All three failed identically, projecting `S.univ_nonempty` — a field
`SourceClass` does not have. They needed `X` non-empty, which the statement does not assume.

That looks at first like the statement is FALSE for empty `X`, since `∃ x` would have no witness.
It is not: `SourceClass` carries `sum_one : ∀ θ, ∑ x, prob θ x = 1`, and over an empty `X` that sum
is `0 ≠ 1`. **So no `SourceClass` exists over an empty `X`** — non-emptiness of `X` is a CONSEQUENCE
of the structure, and `[Nonempty Θ]` is exactly what supplies the `θ₀` needed to invoke `sum_one`
and derive it. That is why the hypothesis is there.

MATHS. Contrapositive/averaging: if `maxLik x < q x * Cₛ` for EVERY `x`, summing over the (non-empty)
`X` gives `Cₛ = ∑ maxLik x < (∑ q x) * Cₛ ≤ 1 * Cₛ = Cₛ`, a contradiction. The strict summed
inequality needs `X` non-empty, and the final step needs `0 < Cₛ`.

PROBED, NOT GUESSED — reusing what `de54ce0e` established:
  * `le_ciSup : BddAbove (Set.range f) → ∀ c, f c ≤ iSup f` — needs boundedness, since a real `⨆`
    over an unbounded family collapses to 0.
  * each `prob θ x` is one non-negative term of a sum equal to 1, hence `≤ 1` — the bound.
  * `Finset.sum_lt_sum_of_nonempty` for the strict summed inequality.
-/
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core

set_option autoImplicit false
set_option maxHeartbeats 1000000

open UniversalRedundancy


open UniversalRedundancy in
/-- **The target, verbatim.** -/
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ]
    (q : X → ℝ) (hq : ∑ x, q x ≤ 1) :
    ∃ x, q x * S.shtarkovSum ≤ S.maxLik x := by
  classical
  obtain ⟨θ₀⟩ := (inferInstance : Nonempty Θ)
  -- X is non-empty BECAUSE a SourceClass exists over it: an empty sum cannot equal 1
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := S.sum_one θ₀
    simp at this
  -- the likelihood family is bounded, so `maxLik` is a genuine supremum
  have hbdd : ∀ x : X, BddAbove (Set.range (fun θ => S.prob θ x)) := by
    intro x
    refine ⟨1, ?_⟩
    rintro _ ⟨θ, rfl⟩
    calc S.prob θ x ≤ ∑ y, S.prob θ y :=
          Finset.single_le_sum (fun i _ => S.nonneg θ i) (Finset.mem_univ x)
      _ = 1 := S.sum_one θ
  have hle : ∀ x : X, S.prob θ₀ x ≤ S.maxLik x := fun x => le_ciSup (hbdd x) θ₀
  have hCpos : 0 < S.shtarkovSum := by
    have h1 : (1 : ℝ) ≤ S.shtarkovSum := by
      calc (1 : ℝ) = ∑ x, S.prob θ₀ x := (S.sum_one θ₀).symm
        _ ≤ ∑ x, S.maxLik x := Finset.sum_le_sum (fun x _ => hle x)
        _ = S.shtarkovSum := rfl
    linarith
  by_contra hcon
  push_neg at hcon
  -- every x fails, so summing gives Cₛ < Cₛ
  have hstrict : (∑ x, S.maxLik x) < ∑ x, q x * S.shtarkovSum :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun x _ => hcon x)
  have hsum : (∑ x, q x * S.shtarkovSum) = (∑ x, q x) * S.shtarkovSum := by
    rw [← Finset.sum_mul]
  have : S.shtarkovSum < S.shtarkovSum := by
    calc S.shtarkovSum = ∑ x, S.maxLik x := rfl
      _ < ∑ x, q x * S.shtarkovSum := hstrict
      _ = (∑ x, q x) * S.shtarkovSum := hsum
      _ ≤ 1 * S.shtarkovSum := by nlinarith
      _ = S.shtarkovSum := one_mul _
  exact lt_irrefl _ this
