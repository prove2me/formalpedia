-- Prove2me | solution 1 for flt_three
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-11T17:27:42.406406+00:00
-- url     : https://prove2.me/submissions/463ba66f-2bb5-4c99-91d6-0d79799f3b0c

import Theorems.Thm_flt_three
import Mathlib.NumberTheory.FLT.Three

theorem solution (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 :=
  fermatLastTheoremThree a b c (by omega) (by omega) (by omega)
