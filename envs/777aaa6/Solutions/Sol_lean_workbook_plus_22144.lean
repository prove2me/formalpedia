-- Prove2me | solution 1 for lean_workbook_plus_22144
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:11.599135+00:00
-- url     : https://prove2.me/submissions/3beedfca-8896-4704-9c42-e21af346c5ff

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (f : ℝ → ℝ)
    (hf : ∀ x y, f (f x ^ 2 + f y) = x * f x + y) : f 0 = 0 := by
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := hf 0 a
    have hb := hf 0 b
    simp only [zero_mul, zero_add] at ha hb
    rw [hab] at ha
    exact ha.symm.trans hb
  have ht : f ((f 0)^2 + f 0) = 0 := by simpa using hf 0 0
  have hc : f (f 0) = 0 := by
    have hh := hf ((f 0)^2 + f 0) 0
    rw [ht] at hh
    simpa using hh
  have he := hinj (hc.trans ht.symm)
  have hs : (f 0)^2 = 0 := by linarith only [he]
  exact sq_eq_zero_iff.mp hs
