-- Prove2me | solution 1 for Arexychen.Erdos180.edgeCount_deleteIsolated_le_of_embeds
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:37:24.246232+00:00
-- url     : https://prove2.me/submissions/dc458108-6ad6-4a20-bb92-fd9ca549b3d5

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
/-- An embedding sends every non-isolated edge of the source injectively into
an edge of the target. -/
theorem solution
    {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β)
    [Finite G.edgeSet]
    (hemb : EmbedsAsSubgraph H G) :
    edgeCount (deleteIsolated H) ≤ edgeCount G := by
  rcases hemb with ⟨f, hf, hmap⟩
  let g : H.support → β := fun x => f (x : α)
  let edgeMap : (deleteIsolated H).edgeSet → G.edgeSet := fun e =>
    ⟨Sym2.map g e.1, by
      rcases e with ⟨e, he⟩
      change Sym2.map g e ∈ G.edgeSet
      induction e using Sym2.inductionOn with
      | _ x y =>
          change s(g x, g y) ∈ G.edgeSet
          rw [SimpleGraph.mem_edgeSet]
          have hxy : (deleteIsolated H).Adj x y := by
            simpa [SimpleGraph.mem_edgeSet] using he
          exact hmap (by simpa [deleteIsolated, g] using hxy)⟩
  have h_edgeMap_injective : Function.Injective edgeMap := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hcoe :
        Sym2.map g e₁.1 = Sym2.map g e₂.1 := by
      exact congrArg Subtype.val h
    have hvertex : Function.Injective g := by
      intro x y hxy
      change f (x : α) = f (y : α) at hxy
      exact Subtype.ext (hf hxy)
    exact (Sym2.map.injective hvertex) hcoe
  exact Nat.card_le_card_of_injective edgeMap h_edgeMap_injective
end
namespace Arexychen
noncomputable section
namespace Erdos180










end Erdos180

end
end Arexychen
