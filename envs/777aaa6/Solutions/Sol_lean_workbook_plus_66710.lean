-- Prove2me | solution 1 for lean_workbook_plus_66710
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:29:56.81088+00:00
-- url     : https://prove2.me/submissions/17d57a05-af03-4679-ac26-2e4ccdde8758

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u : ℝ) (f : ℝ → ℝ) (hf: f = fun x => if x < u then (x + u) / 2 else x) : ∀ x ≥ u, f x = x ∧ ∀ x < u, f x = (x + u) / 2 := by
  (intros; simp_all)
