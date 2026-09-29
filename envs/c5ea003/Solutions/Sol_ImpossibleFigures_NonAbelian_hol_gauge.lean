-- Prove2me | solution 1 for ImpossibleFigures.NonAbelian.hol_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:51:28.767281+00:00
-- url     : https://prove2.me/submissions/6fd137ad-1472-4b22-9e7c-d1b58294a56f

import Mathlib
import Definitions.Def_Geometry_NonAbelianHolonomy
open ImpossibleFigures.NonAbelian in
theorem solution {V E G : Type*} [Group G] {s t : E → V} (H : V → G) (ω : E → G) {a b : V}
    {l : List (Bool × E)}
    (h : IsWalk s t a b l) : hol (gauge s t H ω) l = H b * hol ω l * (H a)⁻¹ := by
  induction h with
  | nil v => simp [hol]
  | @cons a' b' p l' hstart hw ih =>
    -- one gauged step conjugates the step holonomy by the gauge at its endpoints
    have hstep : stepHol (gauge s t H ω) p
        = H (stepEnd s t p) * stepHol ω p * (H (stepStart s t p))⁻¹ := by
      obtain ⟨d, e⟩ := p
      cases d <;> simp only [stepHol, stepEnd, stepStart, ImpossibleFigures.NonAbelian.gauge, cond_true, cond_false] <;> group
    simp only [hol]
    rw [ih, hstep, hstart]
    group
