-- Prove2me | Theorems.Thm_Zeta9Note_irrational_of_small_nonzero_integer_forms
-- name    : Zeta9Note.irrational_of_small_nonzero_integer_forms
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T07:32:30.821616+00:00
-- url     : https://prove2.me/theorems/1c49008f-d9a4-4eb9-b34e-e88d1fae3378
-- title:
--   Arbitrarily small nonzero integer forms imply irrationality
-- statement:
--   Let x be real. If, for every positive tolerance, there are integers b and a with b + a x nonzero and |b + a x| below that tolerance, then x is irrational. This is a criterion; it does not assert that such pairs exist for any particular number, and in particular it says nothing about ζ(9).
-- source:
--   Classical one-form irrationality criterion; abstract layer of the v0.1 research note (Zenodo 10.5281/zenodo.22951155), statement and proof in formalization/Zeta9Note.lean.

import Mathlib

namespace Zeta9Note

theorem irrational_of_small_nonzero_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b a : ℤ,
        (b : ℝ) + (a : ℝ) * x ≠ 0 ∧
        |(b : ℝ) + (a : ℝ) * x| < ε) :
    Irrational x := by sorry

end Zeta9Note
