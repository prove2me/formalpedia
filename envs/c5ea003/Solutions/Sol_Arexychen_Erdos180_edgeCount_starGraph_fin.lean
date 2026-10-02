-- Prove2me | solution 1 for Arexychen.Erdos180.edgeCount_starGraph_fin
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:29:15.979555+00:00
-- url     : https://prove2.me/submissions/108ce5fb-167d-460e-8462-af4ce247d1fb

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
/-- The labelled star on `Fin n`, centered at `0`, has exactly `n - 1` edges. -/
theorem solution {n : ℕ} (hn : 1 ≤ n) :
    edgeCount (starGraph (⟨0, by omega⟩ : Fin n)) = n - 1 := by
  classical
  let c : Fin n := ⟨0, by omega⟩
  let G : SimpleGraph (Fin n) := starGraph c
  have hedge : edgeCount G = G.edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have hinc : G.edgeFinset = G.incidenceFinset c := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [G, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_incidenceFinset,
          SimpleGraph.mk'_mem_incidenceSet_iff, SimpleGraph.mem_edgeSet, starGraph]
        constructor
        · intro hxy
          refine ⟨hxy, ?_⟩
          rcases hxy with hxy | hxy
          · exact Or.inl hxy.1.symm
          · exact Or.inr hxy.1.symm
        · intro hxy
          exact hxy.1
  have hneighbors : G.neighborFinset c = Finset.univ.erase c := by
    ext v
    simp [G, SimpleGraph.mem_neighborFinset, starGraph]
  calc
    edgeCount G = G.edgeFinset.card := hedge
    _ = (G.incidenceFinset c).card := by rw [hinc]
    _ = G.degree c := SimpleGraph.card_incidenceFinset_eq_degree G c
    _ = (G.neighborFinset c).card := (SimpleGraph.card_neighborFinset_eq_degree G c).symm
    _ = (Finset.univ.erase c).card := by rw [hneighbors]
    _ = n - 1 := by simp
end
namespace Arexychen
noncomputable section
namespace Erdos180






end Erdos180

end
end Arexychen
