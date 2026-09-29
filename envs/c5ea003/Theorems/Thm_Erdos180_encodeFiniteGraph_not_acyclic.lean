-- Prove2me | Theorems.Thm_Erdos180_encodeFiniteGraph_not_acyclic
-- name    : Erdos180.encodeFiniteGraph_not_acyclic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:04:43.236857+00:00
-- url     : https://prove2.me/theorems/27094e70-2ebc-4989-9334-3cac59b11269
-- title:
--   Encoding preserves the presence of a cycle
-- statement:
--   If a finite graph is not acyclic, neither is its canonical `Fin`-indexed encoding.
--
--   The encoding is only a change of vertex labels, used to make $\mathcal{F}$ a genuine finite
--   set; this lemma transports the cycle condition across it.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1736-L1743

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Erdos180
open Finset SimpleGraph

theorem Erdos180.encodeFiniteGraph_not_acyclic
    {α : Type*} [Fintype α]
    (graph : SimpleGraph α) (h : ¬ graph.IsAcyclic) :
    ¬ (encodeFiniteGraph graph).graph.IsAcyclic := by sorry
