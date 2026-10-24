-- Prove2me | Theorems.Thm_MeasureEquivalenceMission_c0_not_reducible
-- name    : MeasureEquivalenceMission.c0_not_reducible
-- status  : Proved
-- author  : @username
-- created : 2026-10-24T01:41:48.91178+00:00
-- url     : https://prove2.me/theorems/cd76f74d-070a-45da-8e62-705f788bfe38
-- title:
--   Null-sequence equivalence does not reduce to measure equivalence
-- statement:
--   Let $E_{c_0}$ on all real sequences be defined by $x_n-y_n\to0$, and let $\equiv_m$ mean mutual absolute continuity of probabilities on Cantor space. Then
--
--   $$E_{c_0}\not\le_B\equiv_m.$$
--
--   There is no Borel measurable map to Cantor probabilities that makes $x_n-y_n\to0$ equivalent to mutual absolute continuity of the two outputs for every pair $x,y$. The sequences have no individual boundedness or convergence assumptions. This is the companion main theorem.
-- source:
--   Sequence-space equivalence relations and mutual absolute continuity, owner-supplied research manuscript, 24 October 2026; theorem labelled thm:c0; Classification.lean, c0_not_reducible_cantor.

import Definitions.Def_MeasureEquivalenceSequences

open MeasureEquivalenceMission

theorem MeasureEquivalenceMission.c0_not_reducible :
    ¬ BorelReducesToMeasureEquivalence NullDifference := by sorry
