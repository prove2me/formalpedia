-- Prove2me | Theorems.Thm_syracuse_contraction_length_iff_dvd
-- name    : syracuse_contraction_length_iff_dvd
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T17:05:22.866356+00:00
-- url     : https://prove2.me/theorems/7db4057e-cc88-4016-8fa9-892e44aca1f0
-- title:
--   Exactly when the next Syracuse block uses two halvings at every step
-- statement:
--   For positive odd $y$, the first $d$ Syracuse steps all use exactly two halvings if and only if $2\cdot4^d\mid y-1$. In the formal statement a step from $x$ uses exactly two halvings when $3x+1=4T(x)$. The equivalence holds for arbitrary $d$, including zero.
-- source:
--   Converse and uniform characterization for the block identity https://prove2.me/theorems/401a4606-9af3-4b29-b0be-13ca8ceb3233.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_contraction_length_iff_dvd (y d : ℕ) (hy : 0 < y) (ho : ¬ 2 ∣ y) :
    (∀ i : ℕ, i < d →
      3*syracuseStep^[i] y+1 = 4*syracuseStep^[i+1] y) ↔
    2*4^d ∣ y-1 := by sorry
