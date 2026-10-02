-- Prove2me | solution 1 for Arexychen.Erdos180.edgeCount_matchingHost
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:26:25.280005+00:00
-- url     : https://prove2.me/submissions/30093612-5ffb-4e62-b7a5-4c6b580ab650

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_matching
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
/-- The matching host on `Fin n` has exactly `⌊n/2⌋` edges. -/
theorem solution (n : ℕ) :
    edgeCount (matchingHost n) = n / 2 := by
  classical
  let G : SimpleGraph (Fin n) := matchingHost n
  let edgeEmb : Fin (n / 2) → G.edgeSet := fun k =>
    ⟨matchingHostEdge n k, by
      rw [matchingHostEdge, SimpleGraph.mem_edgeSet]
      exact ⟨k, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hinj : Function.Injective edgeEmb := by
    intro k l h
    apply Fin.ext
    have hs : matchingHostEdge n k = matchingHostEdge n l :=
      congrArg Subtype.val h
    rw [matchingHostEdge, matchingHostEdge, Sym2.eq, Sym2.rel_iff] at hs
    rcases hs with hs | hs
    · have hv := congrArg Fin.val hs.1
      simp [matchingHostLeft] at hv
      omega
    · have hv := congrArg Fin.val hs.1
      simp [matchingHostLeft, matchingHostRight] at hv
      omega
  have hsurj : Function.Surjective edgeEmb := by
    intro e
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : G.Adj x y := by
          simpa [G, SimpleGraph.mem_edgeSet] using he
        rcases hxy with ⟨k, h | h⟩
        · refine ⟨k, ?_⟩
          apply Subtype.ext
          simp [edgeEmb, matchingHostEdge, h.1, h.2]
        · refine ⟨k, ?_⟩
          apply Subtype.ext
          calc
            matchingHostEdge n k =
                s(matchingHostRight n k, matchingHostLeft n k) := by
              simp [matchingHostEdge, Sym2.eq_swap]
            _ = s(x, y) := by simp [h.1, h.2]
  have hcard : Fintype.card (Fin (n / 2)) = Fintype.card G.edgeSet :=
    Fintype.card_of_bijective (f := edgeEmb) ⟨hinj, hsurj⟩
  rw [edgeCount, Nat.card_eq_fintype_card]
  simpa using hcard.symm
end
namespace Arexychen
noncomputable section
namespace Erdos180






end Erdos180

end
end Arexychen
