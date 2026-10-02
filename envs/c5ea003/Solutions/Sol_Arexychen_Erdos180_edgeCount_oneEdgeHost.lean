-- Prove2me | solution 1 for Arexychen.Erdos180.edgeCount_oneEdgeHost
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:38:04.484946+00:00
-- url     : https://prove2.me/submissions/1f18bd08-5905-431f-a869-24c11af64098

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_oneedge
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
/-- The one-edge host has exactly one edge. -/
theorem solution {n : ℕ} (hn : 2 ≤ n) :
    edgeCount (oneEdgeHost n hn) = 1 := by
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  unfold oneEdgeHost edgeCount
  change Nat.card (SimpleGraph.edgeSet
    (SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin n))))) = 1
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  have hset :
      ({s(u, v)} : Set (Sym2 (Fin n))) \ Sym2.diagSet = {s(u, v)} := by
    ext e
    by_cases he : e = s(u, v)
    · subst he
      simp [Sym2.mk_isDiag_iff, huv]
    · simp [he]
  rw [hset]
  simp
end
namespace Arexychen
noncomputable section
namespace Erdos180




end Erdos180

end
end Arexychen
