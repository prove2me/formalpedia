-- Prove2me | Theorems.Thm_Erdos180_kQuotient_mem_proposedFamily
-- name    : Erdos180.kQuotient_mem_proposedFamily
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:01:51.122337+00:00
-- url     : https://prove2.me/theorems/1eb13617-3cd0-4a11-ac7b-6e2cc3aeb662
-- title:
--   Admissible quotients of $K_0$ belong to $\mathcal{F}$
-- statement:
--   For every admissible identification $f$ of the template $K_0$, the encoded quotient
--   $K_0/\!\approx$ is a member of $\mathcal{F}$, i.e. $\mathcal{K} \subseteq \mathcal{F}$
--   (Definitions 2.4 and 2.5).
--
--   Excluding $\mathcal{K}$ is what forces every edge of $B$ to meet the bad-vertex set $U$ in
--   Proposition 3.4: two copies of $S_3$ centred at the endpoints of an edge, together with that
--   edge, form an admissible quotient of $K_0$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L713-L716

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum

open Erdos180
open Finset SimpleGraph

theorem Erdos180.kQuotient_mem_proposedFamily
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    encodeFiniteGraph (quotientGraph kTemplate f) ∈ proposedFamily := by sorry
