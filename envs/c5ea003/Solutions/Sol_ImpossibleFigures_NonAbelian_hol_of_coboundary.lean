-- Prove2me | solution 1 for ImpossibleFigures.NonAbelian.hol_of_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:00:12.332496+00:00
-- url     : https://prove2.me/submissions/188ce006-e5aa-40e0-861f-8d8fcfd0188c

import Mathlib
import Definitions.Def_Geometry_NonAbelianHolonomy
open ImpossibleFigures.NonAbelian in
theorem solution {V E G : Type*} [Group G] {s t : E → V} {ω : E → G} (H : V → G)
    (hω : ∀ e, ω e = H (t e) * (H (s e))⁻¹) {a b : V} {l : List (Bool × E)}
    (h : IsWalk s t a b l) : hol ω l = H b * (H a)⁻¹ := by
  -- every step contributes `H(end) · H(start)⁻¹`, in either orientation
  have hstep : ∀ p : Bool × E, stepHol ω p = H (stepEnd s t p) * (H (stepStart s t p))⁻¹ := by
    rintro ⟨_ | _, e⟩ <;> simp [stepHol, stepEnd, stepStart, hω]
  -- so the holonomy telescopes along the walk
  induction h with
  | nil v => simp [hol]
  | cons hstart hw ih =>
    rw [hol, ih, hstep, hstart]
    group
