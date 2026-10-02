-- Prove2me | Definitions.Def_arexychen_erdos180_families_oneedge
-- name    : arexychen_erdos180_families_oneedge
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-09T07:18:49.410528+00:00
-- url     : https://prove2.me/theorems/329ffbe5-6597-43a9-b620-854486330fef
-- title:
--   A labelled one-edge host
-- statement:
--   For natural $n\ge2$, define a simple graph on $\operatorname{Fin}(n)$ whose only unordered edge is $\{0,1\}$. The remaining vertices are isolated. The proof that the two labelled endpoints differ is retained in the definition.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/OneEdge.lean#L60-L65

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

namespace Arexychen


open Filter
open Asymptotics

noncomputable section

namespace Erdos180

universe u v w





/-- The labelled graph on `Fin n` with exactly the edge joining `0` and `1`.
The hypothesis `2 ≤ n` supplies the two distinct vertices. -/
def oneEdgeHost (n : ℕ) (hn : 2 ≤ n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet
    ({s((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))} :
      Set (Sym2 (Fin n)))





end Erdos180

end
end Arexychen


