-- Prove2me | Theorems.Thm_Erdos180_four_cycle_mem_proposedFamily
-- name    : Erdos180.four_cycle_mem_proposedFamily
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:00:04.845897+00:00
-- url     : https://prove2.me/theorems/b6fe24b0-9dd5-41d2-8263-d9f674829d20
-- title:
--   $C_4$ belongs to the forbidden family
-- statement:
--   The four-cycle is a member of $\mathcal{F}$, immediately from Definition 2.5. Excluding
--   $C_4$ is what makes the common-neighbour graph $R_S$ well behaved: a related pair has a
--   *unique* common neighbour, since two would close a four-cycle (Lemma 3.1(1)).
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L684-L686

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum

open Erdos180
open Finset SimpleGraph

theorem Erdos180.four_cycle_mem_proposedFamily :
    finiteCycle 4 ∈ proposedFamily := by sorry
