-- Prove2me | solution 2 for UniversalRedundancy.SourceClass.nml_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T06:20:29.702094+00:00
-- url     : https://prove2.me/submissions/4ebc7b5d-0c53-4745-8a31-81b02788fe19

/-
# `UniversalRedundancy.SourceClass.nml_sum_one`
Target `de54ce0e` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — chain screened: the bundle's `Definitions.` closure has NO `Theorems.` import,
so no `sorryAx` and no axiom audit.

    structure SourceClass where prob, nonneg : 0 ≤ prob θ x, sum_one : ∑ x, prob θ x = 1
    maxLik x    = ⨆ θ, S.prob θ x        -- indexed sup over a POSSIBLY INFINITE Θ
    shtarkovSum = ∑ x, S.maxLik x
    nml x       = S.maxLik x / S.shtarkovSum

Claim `∑ x, nml x = 1` is `(∑ x, maxLik x) / shtarkovSum`, so the entire content is
**`shtarkovSum ≠ 0`**.

THE CATCH, and why `[Nonempty Θ]` is a hypothesis. `Θ` carries only `Nonempty`, not `Finite`, and
a real `⨆` over an UNBOUNDED family is junk — `Real.iSup_of_not_bddAbove` returns 0. So `maxLik` is
a genuine supremum only once boundedness is shown. It is: each `prob θ x` is one non-negative term
of a sum equal to 1, hence `≤ 1`, so the family is bounded above by 1.

With that, `le_ciSup` gives `prob θ₀ x ≤ maxLik x` for a fixed `θ₀` — which is what `Nonempty Θ`
supplies — and summing over `x` gives `1 = ∑ prob θ₀ x ≤ ∑ maxLik x = shtarkovSum`. Positive, so
the division is legitimate.

The bundle advertises `one_le_shtarkovSum : 1 ≤ Cₛ` in its header — exactly this fact — but
skeleton subtraction stripped every theorem, so it is derived here rather than cited.

PROBED, NOT GUESSED (all `#check`ed against vendored Mathlib):
  * `le_ciSup : BddAbove (range f) → ∀ c, f c ≤ iSup f`
  * `ciSup_le' : (∀ i, f i ≤ a) → ⨆ i, f i ≤ a`   (no `Nonempty` side condition)
  * `Real.iSup_nonneg : (∀ i, 0 ≤ f i) → 0 ≤ ⨆ i, f i`
  * `Real.iSup_of_not_bddAbove : ¬BddAbove (range f) → ⨆ i, f i = 0`  (the junk-value warning)
-/
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset UniversalRedundancy UniversalRedundancy.SourceClass in
/-- **The target, verbatim.** -/
theorem solution {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ) [Nonempty Θ] :
    ∑ x, S.nml x = 1 := by
  -- each prob is one non-negative term of a sum equal to 1, so the family is bounded by 1
  have hbdd : ∀ x : X, BddAbove (Set.range (fun θ => S.prob θ x)) := by
    intro x
    refine ⟨1, ?_⟩
    rintro _ ⟨θ, rfl⟩
    calc S.prob θ x ≤ ∑ y, S.prob θ y :=
          Finset.single_le_sum (fun i _ => S.nonneg θ i) (Finset.mem_univ x)
      _ = 1 := S.sum_one θ
  -- boundedness makes maxLik a genuine supremum, so it dominates every source
  have hle : ∀ (θ : Θ) (x : X), S.prob θ x ≤ S.maxLik x := fun θ x => le_ciSup (hbdd x) θ
  -- Nonempty Θ supplies a source to compare against; its total is 1
  obtain ⟨θ₀⟩ := (inferInstance : Nonempty Θ)
  have hone : (1 : ℝ) ≤ S.shtarkovSum := by
    calc (1 : ℝ) = ∑ x, S.prob θ₀ x := (S.sum_one θ₀).symm
      _ ≤ ∑ x, S.maxLik x := Finset.sum_le_sum (fun x _ => hle θ₀ x)
      _ = S.shtarkovSum := rfl
  have hne : S.shtarkovSum ≠ 0 := by linarith
  show ∑ x, S.maxLik x / S.shtarkovSum = 1
  rw [← Finset.sum_div]
  show (∑ x, S.maxLik x) / S.shtarkovSum = 1
  rw [show (∑ x, S.maxLik x) = S.shtarkovSum from rfl]
  exact div_self hne
