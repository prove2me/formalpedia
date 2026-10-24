-- Prove2me | Theorems.Thm_MeasureEquivalenceMission_lp_iff_le_two
-- name    : MeasureEquivalenceMission.lp_iff_le_two
-- status  : Proved
-- author  : @username
-- created : 2026-10-24T01:41:18.106151+00:00
-- url     : https://prove2.me/theorems/c8a2283b-9b38-4d9e-b33e-136fec2447eb
-- title:
--   Exact exponent threshold for reduction to measure equivalence
-- statement:
--   For every finite real exponent $p\ge1$, let $E_p$ on $\mathbb R^{\mathbb N}$ mean $\sum_n|x_n-y_n|^p<\infty$, and let $\equiv_m$ be mutual absolute continuity of probabilities on Cantor space. Then
--
--   $$E_p\le_B\equiv_m\quad\Longleftrightarrow\quad p\le2.$$
--
--   A reduction must be Borel measurable and preserve and reflect equivalence for every pair of arbitrary real sequences. Both endpoints $p=1$ and $p=2$ are included. This is the main exponent classification.
-- source:
--   Sequence-space equivalence relations and mutual absolute continuity, owner-supplied research manuscript, 24 October 2026; theorem labelled thm:lp; Classification.lean, lp_iff_le_two_cantor.

import Definitions.Def_MeasureEquivalenceSequences

open MeasureEquivalenceMission

theorem MeasureEquivalenceMission.lp_iff_le_two (p : ℝ) (hp : 1 ≤ p) :
    BorelReducesToMeasureEquivalence (LpDifference p) ↔ p ≤ 2 := by sorry
