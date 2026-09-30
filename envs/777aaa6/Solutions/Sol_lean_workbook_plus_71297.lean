-- Prove2me | solution 1 for lean_workbook_plus_71297
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:58.279262+00:00
-- url     : https://prove2.me/submissions/3b60a137-d7c2-4ef9-852e-65a5bcfb51e9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c p q r u v w : ℤ)
    (hu : u = a * p + b * r + c * q)
    (hv : v = a * q + b * p + c * r)
    (hw : w = a * r + b * q + c * p) :
    (a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) *
      (p ^ 3 + q ^ 3 + r ^ 3 - 3 * p * q * r) =
      u ^ 3 + v ^ 3 + w ^ 3 - 3 * u * v * w := by
  rw [hu, hv, hw]
  ring

#print axioms solution
