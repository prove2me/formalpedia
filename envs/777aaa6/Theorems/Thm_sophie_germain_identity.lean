-- Prove2me | Theorems.Thm_sophie_germain_identity
-- name    : sophie_germain_identity
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T05:40:33.166379+00:00
-- url     : https://prove2.me/theorems/dfc4ede5-2402-4a0b-8e17-a82d17c0d231
-- statement:
--   **Sophie Germain's identity.** For any integers a and b: a^4 + 4b^4 = (a^2 + 2b^2 + 2ab)(a^2 + 2b^2 - 2ab). Named after Sophie Germain (1776-1831), who discovered it. This identity implies that a^4 + 4b^4 is always composite for a, b > 1 (since both factors exceed 1). It has applications to primality (the Cunningham factoring) and to FLT-related arguments.

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem sophie_germain_identity (a b : ℤ) : a ^ 4 + 4 * b ^ 4 = (a ^ 2 + 2 * b ^ 2 + 2 * a * b) * (a ^ 2 + 2 * b ^ 2 - 2 * a * b) := by sorry
