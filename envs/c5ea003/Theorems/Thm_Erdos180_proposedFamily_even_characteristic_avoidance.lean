-- Prove2me | Theorems.Thm_Erdos180_proposedFamily_even_characteristic_avoidance
-- name    : Erdos180.proposedFamily_even_characteristic_avoidance
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:20:52.472284+00:00
-- url     : https://prove2.me/theorems/33182c50-c6ab-48a7-993b-a99ea4a55f7c
-- title:
--   Even-characteristic witnesses avoid $\mathcal{J}$
-- statement:
--   For every admissible identification of $J_0$ and every $j \ge 1$, the corresponding member
--   of $\mathcal{J}$ does not embed into the incidence graph of $W(2^j)$.
--
--   Proposition 4.2 of the source: for even $q$ the graph $I_q$ is $\mathcal{J}$-free. Taking
--   $q = 2^j$ therefore supplies a dense witness for every member of $\{C_4, C_6\} \cup \mathcal{J}$;
--   the members of $\mathcal{K}$ are handled by odd $q = 3^j$, using the fact that every triad of the
--   dual quadrangle $Q(4,q)$ has zero or two centres.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L8947-L8954

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.FieldTheory.Finite.GaloisField

open Erdos180
open SimpleGraph

theorem Erdos180.proposedFamily_even_characteristic_avoidance :
    ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)) := by sorry
