-- Prove2me | Theorems.Thm_syracuse_exact_contraction_block
-- name    : syracuse_exact_contraction_block
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T12:36:43.759021+00:00
-- url     : https://prove2.me/theorems/401a4606-9af3-4b29-b0be-13ca8ceb3233
-- title:
--   Exact iterates along a block of Syracuse steps with two halvings each
-- statement:
--   For $u>0$ and $d\ge0$ set $y=1+2\cdot4^d u$. If $0\le i\le d$, the $i$th Syracuse iterate equals $1+2\cdot3^i4^{d-i}u$. The first $d$ steps are strictly decreasing.
-- source:
--   Syracuse valuation-two iteration for https://prove2.me/theorems/2608ffdc-2f1d-4f5a-bf8d-7c3af9948d46.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_exact_contraction_block (d u : ℕ) (hu : 0 < u) :
    let y := 1+2*(4^d*u)
    (∀ i : ℕ, i ≤ d → syracuseStep^[i] y = 1+2*(3^i*(4^(d-i)*u))) ∧
    (∀ i : ℕ, i < d → syracuseStep^[i+1] y < syracuseStep^[i] y) := by sorry
