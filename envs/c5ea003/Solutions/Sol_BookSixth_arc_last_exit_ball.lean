-- Prove2me | solution 1 for BookSixth.arc_last_exit_ball
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T15:58:03.959009+00:00
-- url     : https://prove2.me/submissions/7d890830-b0dd-4869-8124-762504b0b735

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem solution {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M)
    (r : ℝ) (hr : 0 < r)
    (hrend : r < dist (D.vertex (D.right e)) (D.vertex (D.left e))) :
    ∃ t : EdgeParameter, 0 < t.val ∧ t.val < 1 ∧
      dist (D.arc e t) (D.vertex (D.left e)) = r ∧
      ∀ s : EdgeParameter, t.val < s.val →
        r < dist (D.arc e s) (D.vertex (D.left e)) := by
  let g : EdgeParameter → ℝ := fun t =>
    dist (D.arc e t) (D.vertex (D.left e))
  have hg : Continuous g := (D.continuous_arc e).dist continuous_const
  have hg0 : g 0 = 0 := by
    dsimp [g]
    rw [show (0 : EdgeParameter) = ⟨0, by constructor <;> norm_num⟩ from rfl,
      D.start]
    exact dist_self _
  have hg1 : r < g 1 := by
    dsimp only [g]
    rw [show (1 : EdgeParameter) = ⟨1, by constructor <;> norm_num⟩ from rfl,
      D.finish]
    exact hrend
  have h01 : (0 : EdgeParameter) ≤ 1 := by norm_num
  have hlevel : ({t : EdgeParameter | g t = r} : Set EdgeParameter).Nonempty := by
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc h01 hg.continuousOn
      (show r ∈ Set.Icc (g 0) (g 1) from ⟨by rw [hg0]; exact hr.le, hg1.le⟩)
    exact ⟨t, ht⟩
  have hcompact : IsCompact {t : EdgeParameter | g t = r} :=
    (isClosed_eq hg continuous_const).isCompact
  obtain ⟨t, ht⟩ := hcompact.exists_isGreatest hlevel
  have htr : g t = r := ht.1
  have ht0 : 0 < t.val := by
    by_contra h
    have htzero : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt h) t.property.1)
    rw [htzero, hg0] at htr
    exact (ne_of_gt hr) htr.symm
  have ht1 : t.val < 1 := by
    by_contra h
    have htone : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt h))
    rw [htone] at htr
    exact (ne_of_gt hg1) htr
  refine ⟨t, ht0, ht1, htr, ?_⟩
  intro s hts
  change r < g s
  by_contra h
  have hs1 : s ≤ (1 : EdgeParameter) := s.property.2
  obtain ⟨u, hu, hur⟩ := intermediate_value_Icc hs1 hg.continuousOn
    (show r ∈ Set.Icc (g s) (g 1) from ⟨le_of_not_gt h, hg1.le⟩)
  have hut : u ≤ t := ht.2 hur
  have htu : t < u := lt_of_lt_of_le hts hu.1
  exact (not_lt_of_ge hut) htu
