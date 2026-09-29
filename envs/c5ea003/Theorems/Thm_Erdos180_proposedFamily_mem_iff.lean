-- Prove2me | Theorems.Thm_Erdos180_proposedFamily_mem_iff
-- name    : Erdos180.proposedFamily_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T01:59:27.118192+00:00
-- url     : https://prove2.me/theorems/c922840b-7f6b-47f3-96d0-81e8a0fa27f2
-- title:
--   Membership in the forbidden family $\mathcal{F}$
-- statement:
--   A finite graph belongs to $\mathcal{F}$ if and only if it is $C_4$, or $C_6$, or the
--   encoded admissible quotient of the template $J_0$, or the encoded admissible quotient of the
--   template $K_0$:
--
--   $$\mathcal{F} \;=\; \{C_4, C_6\} \cup \mathcal{J} \cup \mathcal{K}.$$
--
--   This is Definition 2.5 of the source in the form in which the rest of the argument consumes
--   it. The forbidden family is $\mathcal{F} = \{C_4, C_6\} \cup \mathcal{J} \cup \mathcal{K}$ (Definition 2.5 of the source), where $\mathcal{J}$ and $\mathcal{K}$ are the admissible quotients of two properly $2$-coloured templates $J_0$ and $K_0$ assembled from the subdivisions $S_2, S_3$ of $K_{3,2}, K_{3,3}$ (Definitions 2.1-2.4).
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L658-L667

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum

open Erdos180
open Finset SimpleGraph

theorem Erdos180.proposedFamily_mem_iff {graph : FiniteGraph} :
    graph ∈ proposedFamily ↔
      (((graph = finiteCycle 4 ∨ graph = finiteCycle 6) ∨
        (∃ f : JVertex → JVertex, JAdmissible f ∧
          encodeFiniteGraph (quotientGraph jTemplate f) = graph)) ∨
        (∃ f : KVertex → KVertex, KAdmissible f ∧
          encodeFiniteGraph (quotientGraph kTemplate f) = graph)) := by sorry
