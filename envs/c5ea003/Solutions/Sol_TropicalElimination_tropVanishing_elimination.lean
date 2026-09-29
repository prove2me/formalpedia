-- Prove2me | solution 1 for TropicalElimination.tropVanishing_elimination
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T05:44:36.259067+00:00
-- url     : https://prove2.me/submissions/3aaa491a-566d-4f78-85a6-fde8ec32989f

import Mathlib
import Definitions.Def_Tropical_TropicalLinearSpaceElimination

/-- Bad-coordinate analysis, the half where `X s ≤ Y s`. -/
theorem b388_bad_aux1 {E α : Type*} [LinearOrder α] (X Y : E → α)
    (hX : ∀ i, ∃ j, j ≠ i ∧ X j ≤ X i) (hY : ∀ i, ∃ j, j ≠ i ∧ Y j ≤ Y i)
    (e s : E) (hXY : X e = Y e) (hse : s ≠ e) (hle : X s ≤ Y s)
    (hbad : ∀ j, j ≠ s → j ≠ e → min (X s) (Y s) < min (X j) (Y j)) :
    X s = X e ∧ Y s = X e := by
  have hm : min (X s) (Y s) = X s := min_eq_left hle
  have hXj : ∀ j, j ≠ s → j ≠ e → X s < X j := fun j h1 h2 => by
    have := lt_of_lt_of_le (hbad j h1 h2) (min_le_left _ _)
    rwa [hm] at this
  have hYj : ∀ j, j ≠ s → j ≠ e → X s < Y j := fun j h1 h2 => by
    have := lt_of_lt_of_le (hbad j h1 h2) (min_le_right _ _)
    rwa [hm] at this
  -- step 1: X e ≤ X s
  obtain ⟨j1, hj1s, hj1⟩ := hX s
  have h1 : X e ≤ X s := by
    by_cases hj1e : j1 = e
    · rw [hj1e] at hj1; exact hj1
    · exact absurd hj1 (not_le.mpr (hXj j1 hj1s hj1e))
  -- step 2: X s ≤ X e
  obtain ⟨j2, hj2e, hj2⟩ := hX e
  have h2 : X s ≤ X e := by
    by_cases hj2s : j2 = s
    · rw [hj2s] at hj2; exact hj2
    · exact absurd (le_trans hj2 h1) (not_le.mpr (hXj j2 hj2s hj2e))
  have hXe : X s = X e := le_antisymm h2 h1
  -- step 3: Y s ≤ Y e
  obtain ⟨j3, hj3e, hj3⟩ := hY e
  have h3 : Y s ≤ X e := by
    by_cases hj3s : j3 = s
    · rw [hj3s, ← hXY] at hj3; exact hj3
    · rw [← hXY, ← hXe] at hj3
      exact absurd hj3 (not_le.mpr (hYj j3 hj3s hj3e))
  exact ⟨hXe, le_antisymm h3 (hXe ▸ hle)⟩

/-- Bad-coordinate analysis: a coordinate `s ≠ e` whose `min (X s) (Y s)` is strictly below
every other coordinate's (except `e`) has `X s = Y s = X e`. -/
theorem b388_bad_aux {E α : Type*} [LinearOrder α] (X Y : E → α)
    (hX : ∀ i, ∃ j, j ≠ i ∧ X j ≤ X i) (hY : ∀ i, ∃ j, j ≠ i ∧ Y j ≤ Y i)
    (e s : E) (hXY : X e = Y e) (hse : s ≠ e)
    (hbad : ∀ j, j ≠ s → j ≠ e → min (X s) (Y s) < min (X j) (Y j)) :
    X s = X e ∧ Y s = X e := by
  rcases le_total (X s) (Y s) with h | h
  · exact b388_bad_aux1 X Y hX hY e s hXY hse h hbad
  · have hbad' : ∀ j, j ≠ s → j ≠ e → min (Y s) (X s) < min (Y j) (X j) := by
      intro j h1 h2
      rw [min_comm (Y s), min_comm (Y j)]
      exact hbad j h1 h2
    obtain ⟨h1, h2⟩ := b388_bad_aux1 Y X hY hX e s hXY.symm hse h hbad'
    exact ⟨h2.trans hXY.symm, h1.trans hXY.symm⟩

open TropicalElimination in
theorem b388_exists_add_eq (a : TT) (ha : a ≠ ⊤) (b : TT) : ∃ v : TT, a + v = b := by
  induction b using WithTop.recTopCoe with
  | top => exact ⟨⊤, by simp⟩
  | coe q =>
    lift a to ℚ using ha
    exact ⟨((q - a : ℚ) : TT), by norm_cast; ring⟩

open TropicalElimination in
/-- The construction around the unique bad coordinate `s`: raise `z0` at `s` alone. -/
theorem b388_core {E : Type*} [DecidableEq E] (c z0 : E → TT) (e s : E) (hse : s ≠ e)
    (hze : z0 e = ⊤) (hcs : c s ≠ ⊤) (hbad : ∀ j, j ≠ s → c s + z0 s < c j + z0 j) :
    ∃ v, z0 s ≤ v ∧ Function.update z0 s v ∈ tropVanishing c := by
  have hes : e ≠ s := Ne.symm hse
  by_cases hA : ∃ k, k ≠ e ∧ k ≠ s ∧ ∀ j, j ≠ e → j ≠ s → j ≠ k → c k + z0 k < c j + z0 j
  · obtain ⟨k, hke, hks, hk⟩ := hA
    obtain ⟨v, hv⟩ := b388_exists_add_eq (c s) hcs (c k + z0 k)
    refine ⟨v, ?_, ?_⟩
    · have h1 := hbad k hks
      rw [← hv] at h1
      exact (WithTop.add_le_add_iff_left hcs).1 h1.le
    · intro i
      by_cases his : i = s
      · rw [his]
        refine ⟨k, hks, ?_⟩
        rw [Function.update_self, Function.update_of_ne hks, hv]
      by_cases hie : i = e
      · rw [hie]
        refine ⟨s, hse, ?_⟩
        rw [Function.update_of_ne hes, hze, add_top]
        exact le_top
      by_cases hik : i = k
      · rw [hik]
        refine ⟨s, Ne.symm hks, ?_⟩
        rw [Function.update_self, Function.update_of_ne hks, hv]
      · refine ⟨k, Ne.symm hik, ?_⟩
        rw [Function.update_of_ne hks, Function.update_of_ne his]
        exact (hk i hie his hik).le
  · push_neg at hA
    refine ⟨⊤, le_top, ?_⟩
    intro i
    by_cases his : i = s
    · rw [his]
      refine ⟨e, hes, ?_⟩
      rw [Function.update_self, Function.update_of_ne hes, hze, add_top, add_top]
    by_cases hie : i = e
    · rw [hie]
      refine ⟨s, hse, ?_⟩
      rw [Function.update_self, Function.update_of_ne hes, hze, add_top, add_top]
    · obtain ⟨j, hje, hjs, hji, hj⟩ := hA i hie his
      refine ⟨j, hji, ?_⟩
      rw [Function.update_of_ne hjs, Function.update_of_ne his]
      exact hj

set_option maxHeartbeats 4000000 in
open TropicalElimination in
theorem solution {E : Type*} [Nontrivial E] [Fintype E] [Nonempty E] [Fintype E] [DecidableEq E]
    [Nontrivial E] (c : E → TT) :
    SatisfiesElimination (tropVanishing c) := by
  intro x hx y hy e hxy hxe
  obtain ⟨z0, hz0e, hz0i⟩ : ∃ z0 : E → TT, z0 e = ⊤ ∧ ∀ i, i ≠ e → z0 i = min (x i) (y i) :=
    ⟨fun i => if i = e then ⊤ else min (x i) (y i), by simp, fun i hi => by simp [hi]⟩
  have side : ∀ z : E → TT, z ∈ tropVanishing c → z e = ⊤ → (∀ i, z0 i ≤ z i) →
      (∀ i, x i ≠ y i → z i = z0 i) →
      ∃ z ∈ tropVanishing c, z e = ⊤ ∧ (∀ i, min (x i) (y i) ≤ z i) ∧
        ∀ i, x i ≠ y i → z i = min (x i) (y i) := by
    intro z hz hze hle heq
    refine ⟨z, hz, hze, ?_, ?_⟩
    · intro i
      by_cases hi : i = e
      · rw [hi, hze]; exact le_top
      · rw [← hz0i i hi]; exact hle i
    · intro i hne
      have hi : i ≠ e := by
        rintro rfl
        exact hne hxy
      rw [heq i hne, hz0i i hi]
  by_cases hbad : ∃ s, s ≠ e ∧ ∀ j, j ≠ s → c s + z0 s < c j + z0 j
  · obtain ⟨s, hse, hs⟩ := hbad
    have hfin : c s + z0 s ≠ ⊤ := by
      have := hs e (Ne.symm hse)
      rw [hz0e, add_top] at this
      exact this.ne
    have hcs : c s ≠ ⊤ := (WithTop.add_ne_top.1 hfin).1
    have hxs : x s = y s := by
      have key := b388_bad_aux (fun i => c i + x i) (fun i => c i + y i) hx hy e s
        (by simp only [hxy]) hse (by
          intro j hjs hje
          have := hs j hjs
          rw [hz0i s hse, hz0i j hje, ← min_add_add_left, ← min_add_add_left] at this
          exact this)
      exact WithTop.add_left_cancel hcs (key.1.trans key.2.symm)
    obtain ⟨v, hv, hmem⟩ := b388_core c z0 e s hse hz0e hcs hs
    apply side (Function.update z0 s v) hmem
    · rw [Function.update_of_ne (Ne.symm hse), hz0e]
    · intro i
      by_cases his : i = s
      · rw [his, Function.update_self]; exact hv
      · rw [Function.update_of_ne his]
    · intro i hne
      have his : i ≠ s := by
        rintro rfl
        exact hne hxs
      rw [Function.update_of_ne his]
  · push_neg at hbad
    apply side z0 ?_ hz0e (fun i => le_rfl) (fun i _ => rfl)
    intro i
    by_cases hie : i = e
    · obtain ⟨j, hj⟩ := exists_ne e
      refine ⟨j, by rw [hie]; exact hj, ?_⟩
      rw [hie, hz0e, add_top]
      exact le_top
    · exact hbad i hie
