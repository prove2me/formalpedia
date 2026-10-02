-- Prove2me | solution 1 for BookSixth.arc_small_radius_last_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T16:48:52.899652+00:00
-- url     : https://prove2.me/submissions/df2d1ebb-ed32-46b3-90ba-a4184e055af4

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_arc_last_exit_ball
open BookSixth

theorem solution {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M)
    (a : EdgeParameter) (ha : 0 < a.val) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ t : EdgeParameter, 0 < t.val ∧ t.val < a.val ∧
        dist (D.arc e t) (D.vertex (D.left e)) = r ∧
        ∀ s : EdgeParameter, t.val < s.val →
          r < dist (D.arc e s) (D.vertex (D.left e)) := by
  let g : EdgeParameter → ℝ := fun t =>
    dist (D.arc e t) (D.vertex (D.left e))
  have hg : Continuous g := (D.continuous_arc e).dist continuous_const
  have hK : IsCompact {s : EdgeParameter | a.val ≤ s.val} :=
    (isClosed_le continuous_const continuous_subtype_val).isCompact
  have hpos : ∀ s ∈ ({s : EdgeParameter | a.val ≤ s.val} : Set EdgeParameter),
      0 < g s := by
    intro s hs
    apply dist_pos.mpr
    intro heq
    have hz : s = ⟨0, by constructor <;> norm_num⟩ :=
      D.simple_arc e (heq.trans (D.start e).symm)
    have hval : s.val = 0 := congrArg Subtype.val hz
    change a.val ≤ s.val at hs
    linarith
  obtain ⟨R, hR, hbound⟩ := hK.exists_forall_le' hg.continuousOn hpos
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  have hend : r < dist (D.vertex (D.right e)) (D.vertex (D.left e)) := by
    have h := hbound (⟨1, by constructor <;> norm_num⟩ : EdgeParameter) a.property.2
    change R ≤ dist (D.arc e ⟨1, by constructor <;> norm_num⟩)
      (D.vertex (D.left e)) at h
    rw [D.finish] at h
    exact hrR.trans_le h
  obtain ⟨t, ht0, ht1, htr, hafter⟩ := BookSixth.arc_last_exit_ball D e r hr hend
  refine ⟨t, ht0, ?_, htr, hafter⟩
  by_contra hnot
  have h := hbound t (le_of_not_gt hnot)
  change R ≤ dist (D.arc e t) (D.vertex (D.left e)) at h
  rw [htr] at h
  exact (not_lt_of_ge h) hrR
