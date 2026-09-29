-- Prove2me | solution 1 for mme_CW_fourth_left_grade_fiber_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:23:00.784133+00:00
-- url     : https://prove2.me/submissions/d6a08605-82f1-49ea-b610-4e4c4998b870

import Definitions.Def_mme_stothers_fourth_data

open MME MME.StothersFourth
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZFourthAvailability

theorem coordGrade_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (cwSquareCoordGrade q) := by
  intro a
  fin_cases a
  · exact ⟨⟨0, by omega⟩, by simp [cwSquareCoordGrade]⟩
  · exact ⟨⟨1, by omega⟩, by simp [cwSquareCoordGrade, hq.ne']⟩
  · exact ⟨⟨q + 1, by omega⟩, by simp [cwSquareCoordGrade]⟩

theorem pairGrade_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (cwSquarePairGrade q) := by
  intro a
  let l : Fin 3 := ⟨min a.val 2, by omega⟩
  let r : Fin 3 := ⟨a.val - 2, by omega⟩
  obtain ⟨x, hx⟩ := coordGrade_surjective q hq l
  obtain ⟨y, hy⟩ := coordGrade_surjective q hq r
  refine ⟨(x, y), Fin.ext ?_⟩
  change (cwSquareCoordGrade q x).val + (cwSquareCoordGrade q y).val = a.val
  rw [hx, hy]
  dsimp [l, r]
  omega

end MME.DWZFourthAvailability
open MME.DWZFourthAvailability

/-- The canonical fourth-power coarse fiber has a basis coordinate with
left-square grade `a` precisely when both half-grades are in range. -/
theorem solution (q : ℕ) (hq : 0 < q)
    (k : Fin 9) (a : Fin 5) :
    (∃ x : (Fin (q + 2) × Fin (q + 2)) × (Fin (q + 2) × Fin (q + 2)),
      cwFourthPairGrade q x = k ∧ cwSquarePairGrade q x.1 = a) ↔
      a.val ≤ k.val ∧ k.val ≤ a.val + 4 := by
  constructor
  · rintro ⟨x, hk, ha⟩
    have hk' := congrArg Fin.val hk
    change (cwSquarePairGrade q x.1).val + (cwSquarePairGrade q x.2).val = k.val at hk'
    rw [ha] at hk'
    have := (cwSquarePairGrade q x.2).isLt
    omega
  · rintro ⟨hleft, hright⟩
    let b : Fin 5 := ⟨k.val - a.val, by omega⟩
    obtain ⟨l, hl⟩ := pairGrade_surjective q hq a
    obtain ⟨r, hr⟩ := pairGrade_surjective q hq b
    refine ⟨(l, r), ?_, hl⟩
    apply Fin.ext
    change (cwSquarePairGrade q l).val + (cwSquarePairGrade q r).val = k.val
    rw [hl, hr]
    dsimp [b]
    omega
