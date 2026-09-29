-- Prove2me | solution 2 for MomentHierarchy.partitionCount_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T04:54:12.715467+00:00
-- url     : https://prove2.me/submissions/cc09673d-a2b0-4c2a-9b49-d2fde54111a0

/-
# `MomentHierarchy.partitionCount_two`
Target `5775c4b6` (Open, not deprecated at draft time; re-read live immediately before submitting).

NOT YET COMPILED — drafted while the build lock was held by the companion target's ship.

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`partitionCount k = Nat.card (Setoid (Fin k))` is the k-th Bell number. Verified by exhaustive
enumeration: 1, 1, 2, 5, 15, 52 for k = 0..5, matching Bell with NO indexing shift. At k = 2 the
only equivalence relations are the discrete one (`0|1`) and the total one (`01`).

`decide` IS UNAVAILABLE: `partitionCount` is noncomputable and Lean synthesises neither
`Fintype (Setoid (Fin 2))` nor `DecidableEq (Setoid (Fin 2))` (both probed, both fail). The two
elements must be exhibited rather than enumerated by the kernel.

PROBED, NOT GUESSED:
  * `Nat.card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y, x ≠ y ∧ {x, y} = Set.univ`
  * `Setoid.bot_def : ⇑⊥ = fun x1 x2 => x1 = x2`   (discrete)
  * `Setoid.top_def : ⇑⊤ = ⊤`                       (total)
  * `Setoid.ext : (∀ a b, s a b ↔ t a b) → s = t`
  * `Set.eq_univ_iff_forall : s = Set.univ ↔ ∀ x, x ∈ s`
  * the reflexivity accessor on a BOUND setoid is `s.iseqv.refl a`, not `s.refl a`
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy
import Definitions.Def_Logic_MomentHierarchyBell

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MomentHierarchy

/-- An equivalence relation on `Fin 2` that relates `0` and `1` relates everything. -/
theorem setoid_fin_two_top {s : Setoid (Fin 2)} (h : s 0 1) : s = ⊤ := by
  apply Setoid.ext
  intro a b
  constructor
  · intro _
    rw [Setoid.top_def]
    trivial
  · intro _
    fin_cases a <;> fin_cases b
    · exact s.iseqv.refl _
    · exact h
    · exact s.iseqv.symm h
    · exact s.iseqv.refl _

/-- An equivalence relation on `Fin 2` that does not relate `0` and `1` is the discrete one. -/
theorem setoid_fin_two_bot {s : Setoid (Fin 2)} (h : ¬ s 0 1) : s = ⊥ := by
  apply Setoid.ext
  intro a b
  rw [Setoid.bot_def]
  constructor
  · intro hs
    by_contra hne
    fin_cases a <;> fin_cases b
    · exact hne rfl
    · exact h hs
    · exact h (s.iseqv.symm hs)
    · exact hne rfl
  · intro hab
    subst hab
    exact s.iseqv.refl a

/-- **The target, verbatim.** -/
theorem solution : partitionCount 2 = 2 := by
  show Nat.card (Setoid (Fin 2)) = 2
  rw [Nat.card_eq_two_iff]
  refine ⟨⊥, ⊤, ?_, ?_⟩
  · -- the discrete and total relations differ, because 0 ≠ 1 in Fin 2
    intro hbt
    have h01 : ((⊥ : Setoid (Fin 2)) : Fin 2 → Fin 2 → Prop) 0 1 := by
      rw [hbt, Setoid.top_def]; trivial
    rw [Setoid.bot_def] at h01
    exact absurd h01 (by decide)
  · -- and they exhaust the type: every setoid is one or the other
    rw [Set.eq_univ_iff_forall]
    intro s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h : s 0 1
    · exact Or.inr (setoid_fin_two_top h)
    · exact Or.inl (setoid_fin_two_bot h)
