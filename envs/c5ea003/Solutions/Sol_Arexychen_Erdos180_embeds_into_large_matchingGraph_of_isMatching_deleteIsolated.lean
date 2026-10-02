-- Prove2me | solution 1 for Arexychen.Erdos180.embeds_into_large_matchingGraph_of_isMatching_deleteIsolated
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T07:34:52.201693+00:00
-- url     : https://prove2.me/submissions/8b874744-c45d-467f-805e-2b2b309a20d6

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
/-- If the non-isolated part of `H` is a matching, then `H` embeds into a
canonical matching with one available edge for each vertex of `H`.  Isolated
vertices use their own private edge, while each non-isolated edge uses the
smaller of the two endpoint labels as its edge index. -/
theorem solution
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hmatch : IsMatchingGraph (deleteIsolated H)) :
    EmbedsAsSubgraph H (matchingGraph (Fintype.card α)) := by
  classical
  let enc : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have support_left {x y : α} (hxy : H.Adj x y) : x ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨y, hxy⟩
  have support_right {x y : α} (hxy : H.Adj x y) : y ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨x, hxy.symm⟩
  have unique_of_two_adj {x y z : α} (hxy : H.Adj x y) (hxz : H.Adj x z) :
      y = z := by
    have hx : x ∈ H.support := support_left hxy
    have hy : y ∈ H.support := support_right hxy
    have hz : z ∈ H.support := support_right hxz
    have hxy' : (deleteIsolated H).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
      simpa [deleteIsolated] using hxy
    have hxz' : (deleteIsolated H).Adj ⟨x, hx⟩ ⟨z, hz⟩ := by
      simpa [deleteIsolated] using hxz
    exact congrArg Subtype.val (hmatch hxy' hxz')
  let mate (x : α) (hx : x ∈ H.support) : α :=
    Classical.choose (by
      rw [SimpleGraph.mem_support] at hx
      exact hx)
  have mate_adj (x : α) (hx : x ∈ H.support) : H.Adj x (mate x hx) := by
    dsimp [mate]
    exact Classical.choose_spec (by
      rw [SimpleGraph.mem_support] at hx
      exact hx)
  have mate_mem (x : α) (hx : x ∈ H.support) : mate x hx ∈ H.support := by
    rw [SimpleGraph.mem_support]
    exact ⟨x, (mate_adj x hx).symm⟩
  have mate_eq_of_adj {x y : α} (hxy : H.Adj x y) (hx : x ∈ H.support) :
      mate x hx = y := by
    exact unique_of_two_adj (mate_adj x hx) hxy
  let idx : α → Fin (Fintype.card α) := fun x =>
    if hx : x ∈ H.support then min (enc x) (enc (mate x hx)) else enc x
  let side : α → Bool := fun x =>
    if hx : x ∈ H.support then decide (enc (mate x hx) < enc x) else false
  let f : α → Fin (Fintype.card α) × Bool := fun x => (idx x, side x)
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    have hidx : idx x = idx y := congrArg Prod.fst hxy
    have hside : side x = side y := congrArg Prod.snd hxy
    by_cases hx : x ∈ H.support
    · by_cases hy : y ∈ H.support
      · let mx := mate x hx
        let my := mate y hy
        by_cases hxlt : enc mx < enc x
        · have hylt : enc my < enc y := by
            by_contra hylt
            have hbad : side x ≠ side y := by
              simp [side, hx, hy, mx, my, hxlt, hylt]
            exact hbad hside
          have hmin : enc mx = enc my := by
            simpa [idx, hx, hy, mx, my, hxlt, hylt,
              min_eq_right (le_of_lt hxlt), min_eq_right (le_of_lt hylt)] using hidx
          have hmxmy : mx = my := enc.injective hmin
          have h1 : H.Adj mx x := by
            exact (mate_adj x hx).symm
          have h2 : H.Adj mx y := by
            simpa [mx, my, hmxmy] using (mate_adj y hy).symm
          exact unique_of_two_adj h1 h2
        · have hylt : ¬ enc my < enc y := by
            by_contra hylt
            have hbad : side x ≠ side y := by
              simp [side, hx, hy, mx, my, hxlt, hylt]
            exact hbad hside
          have hxle : enc x ≤ enc mx := le_of_not_gt hxlt
          have hyle : enc y ≤ enc my := le_of_not_gt hylt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, mx, my, hxlt, hylt,
              min_eq_left hxle, min_eq_left hyle] using hidx
          exact enc.injective hmin
      · by_cases hxlt : enc (mate x hx) < enc x
        · have hmin : enc (mate x hx) = enc y := by
            simpa [idx, hx, hy, hxlt, min_eq_right (le_of_lt hxlt)] using hidx
          have hmate : mate x hx = y := enc.injective hmin
          exact False.elim (hy (by simpa [hmate] using mate_mem x hx))
        · have hxle : enc x ≤ enc (mate x hx) := le_of_not_gt hxlt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, hxlt, min_eq_left hxle] using hidx
          have hxy' : x = y := enc.injective hmin
          exact False.elim (hy (by simpa [hxy'] using hx))
    · by_cases hy : y ∈ H.support
      · by_cases hylt : enc (mate y hy) < enc y
        · have hmin : enc x = enc (mate y hy) := by
            simpa [idx, hx, hy, hylt, min_eq_right (le_of_lt hylt)] using hidx
          have hmate : x = mate y hy := enc.injective hmin
          exact False.elim (hx (by simpa [hmate] using mate_mem y hy))
        · have hyle : enc y ≤ enc (mate y hy) := le_of_not_gt hylt
          have hmin : enc x = enc y := by
            simpa [idx, hx, hy, hylt, min_eq_left hyle] using hidx
          exact enc.injective hmin
      · have hmin : enc x = enc y := by
          simpa [idx, hx, hy] using hidx
        exact enc.injective hmin
  · intro x y hxy
    have hx : x ∈ H.support := support_left hxy
    have hy : y ∈ H.support := support_right hxy
    have hmx : mate x hx = y := mate_eq_of_adj hxy hx
    have hmy : mate y hy = x := mate_eq_of_adj hxy.symm hy
    change idx x = idx y ∧ side x ≠ side y
    constructor
    · simp [idx, hx, hy, hmx, hmy, min_comm]
    · have hne : enc x ≠ enc y := by
        intro h
        exact hxy.ne (enc.injective h)
      by_cases hlt : enc x < enc y
      · have hyx : ¬ enc y < enc x := not_lt_of_gt hlt
        simp [side, hx, hy, hmx, hmy, hlt, hyx]
      · have hyx : enc y < enc x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        simp [side, hx, hy, hmx, hmy, hlt, hyx]
end
namespace Arexychen
noncomputable section
namespace Erdos180



end Erdos180

end
end Arexychen
