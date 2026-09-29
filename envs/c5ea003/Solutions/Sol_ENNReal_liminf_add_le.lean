-- Prove2me | solution 1 for ENNReal.liminf_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T10:46:36.03345+00:00
-- url     : https://prove2.me/submissions/3c72cf46-8359-48eb-b9be-47b7597520ed

import Mathlib

open Filter

theorem solution {ι : Type*} (l : Filter ι) [l.NeBot] (F G : ι → ENNReal) :
    Filter.liminf (fun x => F x + G x) l
      ≤ Filter.liminf F l + Filter.limsup G l := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro eps heps hfin
  set B : ENNReal := Filter.limsup G l with hBdef
  have hBfin : B < ⊤ := lt_of_le_of_lt le_add_self hfin
  have hepsne : (eps : ENNReal) ≠ 0 := by simpa using ne_of_gt heps
  have hBlt : B < B + (eps : ENNReal) :=
    ENNReal.lt_add_right (ne_of_lt hBfin) hepsne
  have hev : ∀ᶠ x in l, G x < B + (eps : ENNReal) :=
    Filter.eventually_lt_of_limsup_lt (by rw [← hBdef]; exact hBlt)
  have hle : Filter.liminf (fun x => F x + G x) l
      ≤ Filter.liminf (fun x => F x + (B + (eps : ENNReal))) l := by
    refine Filter.liminf_le_liminf ?_
    filter_upwards [hev] with x hx
    exact add_le_add (le_refl _) (le_of_lt hx)
  have hconst : Filter.liminf (fun x => F x + (B + (eps : ENNReal))) l
      = Filter.liminf F l + (B + (eps : ENNReal)) :=
    liminf_add_const l F (B + (eps : ENNReal)) (by isBoundedDefault) (by isBoundedDefault)
  rw [hconst] at hle
  refine le_trans hle (le_of_eq ?_)
  rw [← add_assoc]
