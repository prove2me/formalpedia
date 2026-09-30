-- Prove2me | solution 1 for lean_workbook_plus_65543
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:12:32.178113+00:00
-- url     : https://prove2.me/submissions/718f2aee-c52b-41bd-aab0-3279a4397a8a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

def quartic_pairing_form {R : Type*} [CommRing R] (a b c d : R) : R :=
  7 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 -
    12 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) +
    (a + b + c + d) * (5 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) -
      5 * (a ^ 2 * (b + c + d) + b ^ 2 * (c + d + a) +
        c ^ 2 * (d + a + b) + d ^ 2 * (a + b + c)) +
      6 * (b * c * d + a * c * d + a * b * d + a * b * c))

theorem quartic_pairing_identity {R : Type*} [CommRing R] (a b c d : R) :
    quartic_pairing_form a b c d =
      2 * ((a - b) ^ 2 * (c - d) ^ 2 + (a - c) ^ 2 * (b - d) ^ 2 +
        (a - d) ^ 2 * (b - c) ^ 2) := by
  unfold quartic_pairing_form
  ring

theorem quartic_pairing_nonnegative (a b c d : ℝ) :
    0 ≤ quartic_pairing_form a b c d := by
  rw [quartic_pairing_identity]
  positivity

theorem solution {a b c d : ℝ} :
    7 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 -
      12 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) +
      (a + b + c + d) * (5 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) -
        5 * (a ^ 2 * (b + c + d) + b ^ 2 * (c + d + a) +
          c ^ 2 * (d + a + b) + d ^ 2 * (a + b + c)) +
        6 * (b * c * d + a * c * d + a * b * d + a * b * c)) =
    2 * ((a - b) ^ 2 * (c - d) ^ 2 + (a - c) ^ 2 * (b - d) ^ 2 +
      (a - d) ^ 2 * (b - c) ^ 2) :=
  quartic_pairing_identity a b c d

#print axioms solution
#print axioms quartic_pairing_nonnegative
