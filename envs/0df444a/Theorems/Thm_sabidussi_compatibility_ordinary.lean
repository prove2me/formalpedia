-- Prove2me | Theorems.Thm_sabidussi_compatibility_ordinary
-- name    : sabidussi_compatibility_ordinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:16:09.650873+00:00
-- url     : https://prove2.me/theorems/b961f561-8d16-438e-9f26-6321520140ab
-- title:
--   sabidussi compatibility ordinary: sabidussi compatibility ordinary
-- statement:
--   The sabidussi compatibility ordinary construction uses the sabidussi compatibility ordinary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Solution.lean#L10-L15
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Solution.lean#L10-L15

import Definitions.Def_Sabidussi
import Definitions.Def_Sabidussi_Solution
set_option autoImplicit true

theorem sabidussi_compatibility_ordinary
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Sabidussi.LoopMultigraph V E} (T : G.EulerTour)
    (hmin : ∀ v : V, 4 ≤ G.degree v) :
    ∃ S : G.OrdinaryCircuitDecomposition, S.Compatible T := by sorry
