-- Prove2me | Theorems.Thm_section5_roundCoord_error
-- name    : section5_roundCoord_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:23:43.973052+00:00
-- url     : https://prove2.me/theorems/cfa724eb-a95a-445c-a7f8-f5ef2882435c
-- title:
--   Coordinate rounding error is bounded by one grid spacing
-- statement:
--   For a natural grid parameter $M$, set $\Delta_M=\sqrt{4\pi/M}$, $R_M=M\Delta_M/2$, and $r_M(t)=-R_M+\Delta_M\lfloor(t+R_M)/\Delta_M\rfloor$. For $M\ge1$ and every $x\in\mathbb R$,
--
--   $$
--   |x-r_M(x)|\le\Delta_M.
--   $$
--
--   This is the scalar error bound for the coordinatewise grid-rounding operation.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5GaussianRounding.lean, section5_roundCoord_error, lines 7–20.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_roundCoord_error {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    |x-roundCoord M x| ≤ gridSpacing M := by sorry
