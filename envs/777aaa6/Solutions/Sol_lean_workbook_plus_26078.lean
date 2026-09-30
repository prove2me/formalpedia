-- Prove2me | solution 1 for lean_workbook_plus_26078
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:39:01.070681+00:00
-- url     : https://prove2.me/submissions/706ce106-c41f-43b6-99be-c98f048431f7

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (h : ∀ x, f (f x) = x) :
    Function.Bijective f := by
  constructor
  · intro a b hab
    calc
      a = f (f a) := (h a).symm
      _ = f (f b) := congrArg f hab
      _ = b := h b
  · intro y
    exact ⟨f y, h y⟩

#print axioms solution
