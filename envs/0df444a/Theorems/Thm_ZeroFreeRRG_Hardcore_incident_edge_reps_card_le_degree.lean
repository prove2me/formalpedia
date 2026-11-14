-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_incident_edge_reps_card_le_degree
-- name    : ZeroFreeRRG.Hardcore.incident_edge_reps_card_le_degree
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:08:14.600441+00:00
-- url     : https://prove2.me/theorems/448409a5-45a0-48e8-9e60-546431abc380
-- title:
--   Incident edge occurrences are bounded by the degree
-- statement:
--   In a configuration-model matching on degree-d vertices, the number of edge occurrences incident to any vertex is at most d, including loops and repeated edges.
-- source:
--   Chunyang Wang et al., Zero-freeness for random regular graphs up to the replica symmetry breaking threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, proof of Lemma 4.20, Step 1 (supporting argument).

import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.incident_edge_reps_card_le_degree (d n : ℕ) (M : Matching n d) (v : Fin n) :
    ((edgeReps M).filter (fun x => x.1 = v ∨ (M.1 x).1 = v)).card ≤ d := by sorry
