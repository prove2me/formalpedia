-- Prove2me | solution 1 for lean_workbook_plus_82204
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:23.412774+00:00
-- url     : https://prove2.me/submissions/98eb2ebd-ba02-4a78-9f4e-138bde2d8103

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℕ → ℕ) (hf: Function.Bijective f) (h1: ∃ x y : ℕ, f x + f y = f (x*y)) : ∃ k : ℕ, f k = 1 :=
  hf.2 1
