-- Prove2me | Definitions.Def_arexychen_erdos180_families_matching
-- name    : arexychen_erdos180_families_matching
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-09T07:19:01.67285+00:00
-- url     : https://prove2.me/theorems/84949f52-39da-4d39-84e3-4eb24d20327e
-- title:
--   A labelled matching host on any number of vertices
-- statement:
--   For every natural $n$, the graph on $\operatorname{Fin}(n)$ has the disjoint edges $\{2k,2k+1\}$ for $0\le k<\lfloor n/2\rfloor$, with an isolated last vertex when $n$ is odd. The bundle defines the two endpoint maps, the unordered edge map, and the graph. It includes the short proved endpoint-inequality lemma required for looplessness.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Matching.lean#L12-L84

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

/-- Left endpoint of the `k`th edge in the labelled matching host on `Fin n`. -/
def matchingHostLeft (n : ℕ) (k : Fin (n / 2)) : Fin n :=
  ⟨2 * k.val, by have hk := k.isLt; omega⟩

/-- Right endpoint of the `k`th edge in the labelled matching host on `Fin n`. -/
def matchingHostRight (n : ℕ) (k : Fin (n / 2)) : Fin n :=
  ⟨2 * k.val + 1, by have hk := k.isLt; omega⟩

theorem matchingHost_left_ne_right (n : ℕ) (k : Fin (n / 2)) :
    matchingHostLeft n k ≠ matchingHostRight n k := by
  intro h
  have hv := congrArg Fin.val h
  simp [matchingHostLeft, matchingHostRight] at hv

/-- The labelled `n`-vertex host consisting of the disjoint edges
`{0,1}, {2,3}, ...`, with one isolated vertex left over when `n` is odd. -/
def matchingHost (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := ∃ k : Fin (n / 2),
    (x = matchingHostLeft n k ∧ y = matchingHostRight n k) ∨
      (x = matchingHostRight n k ∧ y = matchingHostLeft n k)
  symm := by
    intro x y h
    rcases h with ⟨k, h | h⟩
    · exact ⟨k, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨k, Or.inl ⟨h.2, h.1⟩⟩
  loopless := by
    constructor
    intro x h
    rcases h with ⟨k, h | h⟩
    · exact matchingHost_left_ne_right n k (h.1.symm.trans h.2)
    · exact matchingHost_left_ne_right n k (h.2.symm.trans h.1)



/-- The unordered edge corresponding to the `k`th pair of the matching host. -/
def matchingHostEdge (n : ℕ) (k : Fin (n / 2)) : Sym2 (Fin n) :=
  s(matchingHostLeft n k, matchingHostRight n k)







end Erdos180

end
end Arexychen


