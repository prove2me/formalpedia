-- Prove2me | Theorems.Thm_Erdos180_proposedFamilyFree_six_cycle
-- name    : Erdos180.proposedFamilyFree_six_cycle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:01:11.648028+00:00
-- url     : https://prove2.me/theorems/011e9be6-194e-4803-a654-b81ab2f05512
-- title:
--   An $\mathcal{F}$-free host contains no $C_6$
-- statement:
--   If a host graph contains no member of $\mathcal{F}$ then it contains no six-cycle.
--
--   With the preceding lemma this gives $B$ girth at least eight, the property Lemma 3.2 uses to
--   know that a non-backtracking four-edge walk cannot close up, and Lemma 3.3 uses to know that a
--   radius-three neighbourhood is a tree.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L701-L706

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Circulant

open Erdos180
open Finset SimpleGraph

theorem Erdos180.proposedFamilyFree_six_cycle
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 6).Free host := by sorry
