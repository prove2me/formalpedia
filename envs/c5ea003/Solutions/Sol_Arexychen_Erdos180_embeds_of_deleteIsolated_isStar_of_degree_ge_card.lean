-- Prove2me | solution 1 for Arexychen.Erdos180.embeds_of_deleteIsolated_isStar_of_degree_ge_card
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:34:12.107521+00:00
-- url     : https://prove2.me/submissions/497e94f5-91d6-49af-bdaa-ecee97faaf70

import Definitions.Def_arexychen_erdos180_core
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
/-- If the non-isolated part of `H` is a star and a target vertex has at least
`|V(H)|` neighbors, then `H` embeds into the target graph.  Isolated vertices
of `H` are harmless: they are sent injectively to unused neighbors, and only
edge preservation is required. -/
theorem solution
    {α : Type u} {β : Type v} [Fintype α]
    (H : SimpleGraph α) (G : SimpleGraph β) (v : β)
    [Fintype (G.neighborSet v)]
    (hstar : IsStar (deleteIsolated H))
    (hdeg : Fintype.card α ≤ G.degree v) :
    EmbedsAsSubgraph H G := by
  classical
  rcases hstar with ⟨c, hc⟩
  let c0 : α := c
  have hcard : Fintype.card α ≤ Fintype.card (G.neighborSet v) := by
    simpa only [G.card_neighborSet_eq_degree] using hdeg
  rcases Function.Embedding.nonempty_of_card_le hcard with
    ⟨leaf : α ↪ G.neighborSet v⟩
  let f : α → β := fun x => if x = c0 then v else leaf x
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = c0
    · by_cases hy : y = c0
      · exact hx.trans hy.symm
      · exfalso
        have hv_leaf : v = (leaf y : β) := by
          simpa [f, hx, hy] using hxy
        exact (leaf y).property.ne hv_leaf
    · by_cases hy : y = c0
      · exfalso
        have hleaf_v : (leaf x : β) = v := by
          simpa [f, hx, hy] using hxy
        exact (leaf x).property.ne hleaf_v.symm
      · have hleaf : (leaf x : β) = (leaf y : β) := by
          simpa [f, hx, hy] using hxy
        exact leaf.injective (Subtype.ext hleaf)
  · intro x y hxy
    have hx_support : x ∈ H.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨y, hxy⟩
    have hy_support : y ∈ H.support := by
      rw [SimpleGraph.mem_support]
      exact ⟨x, hxy.symm⟩
    let sx : H.support := ⟨x, hx_support⟩
    let sy : H.support := ⟨y, hy_support⟩
    have hred : (deleteIsolated H).Adj sx sy := by
      simpa [deleteIsolated, sx, sy] using hxy
    have hstar_adj : (starGraph c).Adj sx sy := by
      rw [hc] at hred
      exact hred
    rcases hstar_adj with hcenter | hcenter
    · have hx : x = c0 := by
        exact congrArg Subtype.val hcenter.1
      have hy : y ≠ c0 := by
        intro hy
        exact hcenter.2 (Subtype.ext hy)
      have hfx : f x = v := by
        simp [f, hx]
      have hfy : f y = (leaf y : β) := by
        simp [f, hy]
      rw [hfx, hfy]
      exact (leaf y).property
    · have hy : y = c0 := by
        exact congrArg Subtype.val hcenter.1
      have hx : x ≠ c0 := by
        intro hx
        exact hcenter.2 (Subtype.ext hx)
      have hfx : f x = (leaf x : β) := by
        simp [f, hx]
      have hfy : f y = v := by
        simp [f, hy]
      rw [hfx, hfy]
      exact ((leaf x).property).symm
end
namespace Arexychen
noncomputable section
namespace Erdos180












end Erdos180

end
end Arexychen
