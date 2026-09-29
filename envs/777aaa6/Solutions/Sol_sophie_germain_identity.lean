-- Prove2me | solution 1 for sophie_germain_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T05:41:08.62616+00:00
-- url     : https://prove2.me/submissions/e6cab6b3-57b7-4754-8c39-fc92e0ad59f7

import Theorems.Thm_sophie_germain_identity
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) : a ^ 4 + 4 * b ^ 4 = (a ^ 2 + 2 * b ^ 2 + 2 * a * b) * (a ^ 2 + 2 * b ^ 2 - 2 * a * b) := by
  ring
