-- Prove2me | solution 1 for Arexychen.Erdos180.exists_maximalMatching_edgeCover
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:32:06.51201+00:00
-- url     : https://prove2.me/submissions/8bac0961-6d59-45ab-b480-374ebd0c17b1

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





end Erdos180
end
end Arexychen

section
open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180 in
/-- A maximal matching exists, and the vertices it saturates cover every edge. -/
theorem solution
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ M : G.Subgraph,
      M.IsMatching ∧
        Maximal (fun N : G.Subgraph => N.IsMatching) M ∧
          ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ M.verts ∨ y ∈ M.verts := by
  classical
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  rcases Finite.exists_le_maximal
      (α := G.Subgraph) (p := fun N : G.Subgraph => N.IsMatching) hbot with
    ⟨M, _hbot_le, hmax⟩
  refine ⟨M, hmax.1, hmax, ?_⟩
  intro x y hxy
  by_contra hnot
  push Not at hnot
  have hdisj : Disjoint M.support (G.subgraphOfAdj hxy).support := by
    rw [hmax.1.support_eq_verts, SimpleGraph.support_subgraphOfAdj]
    rw [Set.disjoint_left]
    intro z hz hzxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzxy
    rcases hzxy with rfl | rfl
    · exact hnot.1 hz
    · exact hnot.2 hz
  have hsup_match : (M ⊔ G.subgraphOfAdj hxy).IsMatching :=
    hmax.1.sup (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hxy) hdisj
  have hsup_le_M : M ⊔ G.subgraphOfAdj hxy ≤ M :=
    hmax.2 hsup_match le_sup_left
  have hedge_le_M : G.subgraphOfAdj hxy ≤ M :=
    le_trans le_sup_right hsup_le_M
  have hxM : x ∈ M.verts :=
    hedge_le_M.1 (by simp)
  exact hnot.1 hxM
end
namespace Arexychen
noncomputable section
namespace Erdos180








end Erdos180

end
end Arexychen
