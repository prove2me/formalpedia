-- Prove2me | solution 1 for ProofsInTheBook.PlanarMap.PlaneSimpleGraph.fiveColor_planeSimpleGraph
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T19:50:05.009608+00:00
-- url     : https://prove2.me/submissions/37c6dca3-7f15-45e8-8b8e-3877b49e3e7c

import Init
import Mathlib
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Definitions.Def_P2MAssembly_Chapter35Plane

set_option autoImplicit true


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.PlanarMap -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv



namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]













































end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMap
-/
/- Source module: ProofsInTheBook.PlaneSimpleGraph -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap



namespace PlaneSimpleGraph

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]













end PlaneSimpleGraph

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMap
-/
/- Source module: ProofsInTheBook.PlanarMapEuler -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap.CombMap

open ProofsInTheBook.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

















end ProofsInTheBook.PlanarMap.CombMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
-/
/- Source module: ProofsInTheBook.PlanarMapSimple -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

























































end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
-/
/- Source module: ProofsInTheBook.PlanarMapDelete -/
section
set_option autoImplicit true




namespace Equiv.Perm

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace DeleteSet





















end DeleteSet

open DeleteSet











end Equiv.Perm

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

































































section TwoEdgePathObstruction























end TwoEdgePathObstruction

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapSimple
-/
/- Source module: ProofsInTheBook.PlanarMapBoundary -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]













namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}











end BoundaryPath







namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}



















lemma root_mem_darts (C : BoundaryCycle M f) : C.root ∈ C.darts := by
  rw [← List.mem_toFinset, C.normalized.toFinset_eq]
  simp [C.normalized.root_face]



















namespace Chord

variable {C : BoundaryCycle M f} {u v : M.Vertex}



end Chord

end BoundaryCycle





namespace BoundaryArcSplit

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}









end BoundaryArcSplit



namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}











end BoundaryCycle



end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapNearTriangulation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]















namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}





end BoundaryCycle







namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





























end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapNearTriangulation
import ProofsInTheBook.PlanarMapDelete
-/
/- Source module: ProofsInTheBook.PlanarMapFilteredRotation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace FilteredRotation

variable {D : Type*} [Fintype D] [DecidableEq D]























namespace ContiguousInterval

variable {σ : Equiv.Perm D} {Del : Finset D} {n : ℕ}

















end ContiguousInterval



section FreshDart

variable {K : Type*} [Fintype K] [DecidableEq K]















variable (ρ : Equiv.Perm K) (a₀ a₁ : K)





variable {ρ a₀ a₁}





variable (ρ a₀ a₁)















variable {ρ a₀ a₁}







end FreshDart

end FilteredRotation

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFilteredRotation
-/
/- Source module: ProofsInTheBook.PlanarMapChordSplitData -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)



section ChordDarts

variable {u v : M.Vertex} (h : hNT.outerCycle.Chord u v)



















end ChordDarts



























namespace ChordSplitData

variable {hNT} {u v : M.Vertex}













































end ChordSplitData







end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapChordSplitData
-/
/- Source module: ProofsInTheBook.PlanarMapChordSplit -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]









namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}









end BoundaryPath

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

namespace ChordSplitData

variable {hNT} {u v : M.Vertex}





























































































































end ChordSplitData

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapChordSplit
-/
/- Source module: ProofsInTheBook.PlanarMapSeparation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)









namespace ChordSplitData

variable {hNT} {u v : M.Vertex}



















end ChordSplitData



namespace ChordSplitData

variable {hNT} {u v : M.Vertex}









end ChordSplitData

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap


end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapNearTriangulation
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryFan -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}











namespace FanTriangle

variable {hNT : NearTriangulation M} {v0 a b : M.Vertex}









end FanTriangle







namespace BoundaryVertexFan

variable {hNT : NearTriangulation M} {v0 : M.Vertex}









end BoundaryVertexFan

variable (hNT : NearTriangulation M) {v0 : M.Vertex}



















end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundaryFan
import ProofsInTheBook.PlanarMapDelete
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryDelete -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}
















namespace BoundaryDeletionData

variable {hNT : NearTriangulation M} {d0 : D}



/-- The deleted map has exactly one fewer graph vertex. -/
theorem smaller (data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  M.deleteVertex_V_of_orbitEquiv d0 data.vertexQuotient











end BoundaryDeletionData










end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundaryDelete
-/
/- Source module: ProofsInTheBook.PlanarMapFanSurgery -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}











namespace NeighborRotationOrder

variable {v0 : M.Vertex} {neighbors : List M.Vertex}













end NeighborRotationOrder







namespace FanSurgeryReconstruction

variable {hNT : NearTriangulation M} {d0 : D}







/-- The deleted map has exactly one fewer graph vertex. -/
theorem smaller (R : FanSurgeryReconstruction hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  R.toBoundaryDeletionData.smaller









end FanSurgeryReconstruction









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
/-
List-coloring primitives (Chapter 35 layer 4).

Design-independent groundwork for the Thomassen five-list-coloring route
(HANDOFF/CH35_DESIGN_ANSWER.md): proper colorings from lists, monotonicity
in the graph and in the lists, and the piecewise gluing lemmas — including
the rooted cut-vertex glue, which is the form that is actually true for
list colorings (naive gluing fails because the two sides may disagree at
the cut vertex).
-/
import Mathlib
-/
/- Source module: ProofsInTheBook.ListColoring -/
section
set_option autoImplicit true


namespace ProofsInTheBook.ListColoring

variable {V α : Type*}















/-- Enlarging the lists preserves list colorings. -/
theorem IsListColoring.mono_lists {G : SimpleGraph V} {L L' : V → Finset α}
    (hLL : ∀ v, L v ⊆ L' v) {c : V → α} (hc : IsListColoring G L c) :
    IsListColoring G L' c :=
  ⟨fun v => hLL v (hc.1 v), hc.2⟩

theorem ListColorable.mono_lists {G : SimpleGraph V} {L L' : V → Finset α}
    (hLL : ∀ v, L v ⊆ L' v) (h : ListColorable G L) : ListColorable G L' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.mono_lists hLL⟩

section Glue

variable {G : SimpleGraph V} {L : V → Finset α} {s t : Set V} {c₁ c₂ : V → α}

/--
The piecewise gluing lemma.  If `s` and `t` cover the vertices, every edge
lives inside `s` or inside `t`, the two partial colorings are proper and
list-valid on their regions, and they agree on the overlap, then the
piecewise function is a list coloring of `G`.
-/
theorem isListColoring_glue [DecidablePred (· ∈ s)]
    (hcover : ∀ v, v ∈ s ∨ v ∈ t)
    (hsep : ∀ ⦃u v⦄, G.Adj u v → (u ∈ s ∧ v ∈ s) ∨ (u ∈ t ∧ v ∈ t))
    (h₁p : ProperOn G s c₁) (h₁L : ListValidOn L s c₁)
    (h₂p : ProperOn G t c₂) (h₂L : ListValidOn L t c₂)
    (hagree : ∀ ⦃v⦄, v ∈ s → v ∈ t → c₁ v = c₂ v) :
    IsListColoring G L (fun v => if v ∈ s then c₁ v else c₂ v) := by
  constructor
  · intro v
    by_cases hv : v ∈ s
    · simpa [hv] using h₁L hv
    · have hvt : v ∈ t := (hcover v).resolve_left hv
      simpa [hv] using h₂L hvt
  · intro u v huv
    rcases hsep huv with ⟨hus, hvs⟩ | ⟨hut, hvt⟩
    · simpa [hus, hvs] using h₁p hus hvs huv
    · by_cases hus : u ∈ s
      · by_cases hvs : v ∈ s
        · have hu := hagree hus hut
          have hv := hagree hvs hvt
          simpa [hus, hvs, hu, hv] using h₂p hut hvt huv
        · have hu := hagree hus hut
          simpa [hus, hvs, hu] using h₂p hut hvt huv
      · by_cases hvs : v ∈ s
        · have hv := hagree hvs hvt
          simpa [hus, hvs, hv] using h₂p hut hvt huv
        · simpa [hus, hvs] using h₂p hut hvt huv



end Glue



end ProofsInTheBook.ListColoring

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapSeparation
import ProofsInTheBook.PlanarMapFanSurgery
import ProofsInTheBook.ListColoring
-/
/- Source module: ProofsInTheBook.ThomassenLists -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ThomassenLists

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.ListColoring

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {α : Type*} [DecidableEq α]

namespace CombMap

open ProofsInTheBook.PlanarMap.CombMap





namespace ThomassenLists

variable {M : CombMap D} {hNT : NearTriangulation M}
  {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}







/-- Every vertex carries a nonempty list (at least the precolor / size bounds). -/
lemma list_nonempty (h : ThomassenLists hNT p q L cp cq) (v : M.Vertex) :
    (L v).Nonempty := by
  by_cases hbv : hNT.outerCycle.IsBoundaryVertex v
  · by_cases hvp : v = p
    · subst hvp; rw [h.list_p]; exact ⟨cp, Finset.mem_singleton_self cp⟩
    · by_cases hvq : v = q
      · subst hvq; rw [h.list_q]; exact ⟨cq, Finset.mem_singleton_self cq⟩
      · exact Finset.card_pos.mp (lt_of_lt_of_le (by norm_num)
          (h.boundary_ge_three v hbv hvp hvq))
  · exact Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) (h.interior_ge_five v hbv))

end ThomassenLists





namespace ChordSplitRegions

variable {M : CombMap D} {hNT : NearTriangulation M}
  {u v p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/--
**The glue (task item 2c).**  A list coloring `c₁` of side 1 and a list coloring
`c₂` of side 2 that *agree on the chord endpoints* combine to a list coloring of
all of `M.toSimpleGraph`.  This is `ListColoring.isListColoring_glue` specialized
to the chord-split regions: the sides cover `M`, every edge is confined to one
side, and the overlap is the chord endpoints, where the two colorings agree.
-/
theorem glue (R : ChordSplitRegions hNT u v p q L cp cq)
    {c₁ c₂ : M.Vertex → α}
    (h₁p : ProperOn M.toSimpleGraph R.s₁ c₁) (h₁L : ListValidOn L R.s₁ c₁)
    (h₂p : ProperOn M.toSimpleGraph R.s₂ c₂) (h₂L : ListValidOn L R.s₂ c₂)
    (hu : c₁ u = c₂ u) (hv : c₁ v = c₂ v) :
    ∃ c : M.Vertex → α, IsListColoring M.toSimpleGraph L c := by
  classical
  refine ⟨fun w => if w ∈ R.s₁ then c₁ w else c₂ w, ?_⟩
  refine isListColoring_glue R.cover R.edge_confined h₁p h₁L h₂p h₂L ?_
  intro w hw1 hw2
  have hmem := R.overlap ⟨hw1, hw2⟩
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hwu | hwv
  · subst hwu; exact hu
  · subst hwv; exact hv

/--
**Side-2 list forcing (task item 2b).**  After a list coloring `c₁` of side 1,
the side-2 lists with `u, v` forced to `{c₁ u}`, `{c₁ v}` satisfy the Thomassen
hypotheses on side 2 with precolored edge `s(u, v)`, *as long as* side 2 is itself
a near-triangulation whose boundary/interior structure on the region `s₂` is
witnessed by the supplied predicates.

To stay faithful without the unbuilt foreign side map, the side-2 list-validity
facts are expressed against an abstract side-2 near-triangulation `hNT₂`
(produced by the surgery once `Separates` is available) together with the region
identification `ι₂ : M.Vertex → (sideMap₂).Vertex` (the kept-dart correspondence
the surgery exposes when built).  This lemma proves the **color forcing** that is
the genuinely new content of step 2b: `c₁ u ≠ c₁ v` because `uv` is an edge of
`M` (hence of side 1), so the forced singletons are a valid precolored edge.
-/
theorem chord_endpoints_colors_ne (R : ChordSplitRegions hNT u v p q L cp cq)
    {c₁ : M.Vertex → α} (h₁p : ProperOn M.toSimpleGraph R.s₁ c₁) :
    c₁ u ≠ c₁ v :=
  h₁p R.u_s₁ R.v_s₁ R.chord_adj











end ChordSplitRegions



section Deletion

variable {M : CombMap D}























/-- **Reverse adjacency: an `M`-edge avoiding `v0` lifts to a deleted-map edge.**

If `a, b` are deleted-map vertices whose `M`-images are adjacent in `M`, then `a`
and `b` are adjacent in the deleted map.  (The realizing dart survives deletion
because both its endpoints avoid `v0`, by `deletedVertexToM_ne_v0`.) -/
lemma deletedVertexToM_adj_reflect (M : CombMap D) (d0 : D)
    {a b : (M.deleteVertex d0).Vertex}
    (h : M.toSimpleGraph.Adj (deletedVertexToM M d0 a) (deletedVertexToM M d0 b)) :
    (M.deleteVertex d0).toSimpleGraph.Adj a b := by
  classical
  obtain ⟨hne, d, hd⟩ := h
  -- `d` realizes the `M`-edge between the two survivor images, so it survives.
  have htail : M.tail d ≠ M.tail d0 := by
    rw [dartEdge, Sym2.eq_iff] at hd
    rcases hd with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [ha]; exact deletedVertexToM_ne_v0 M d0 a
    · rw [ha]; exact deletedVertexToM_ne_v0 M d0 b
  have hhead : M.head d ≠ M.tail d0 := by
    rw [dartEdge, Sym2.eq_iff] at hd
    rcases hd with ⟨_, hb⟩ | ⟨_, hb⟩
    · rw [hb]; exact deletedVertexToM_ne_v0 M d0 b
    · rw [hb]; exact deletedVertexToM_ne_v0 M d0 a
  have hsurv : d ∉ M.deleteVertexSet d0 :=
    dart_notMem_deleteVertexSet_of_endpoints_ne M d0 htail hhead
  set d' : {x : D // x ∉ M.deleteVertexSet d0} := ⟨d, hsurv⟩ with hd'
  refine ⟨fun hab => hne (by rw [hab]), d', ?_⟩
  -- the deleted-map edge of `d'` maps under `deletedVertexToM` to `s(a,b)`'s images
  have key : (M.deleteVertex d0).dartEdge d' =
      s((M.deleteVertex d0).tail d', (M.deleteVertex d0).head d') := rfl
  -- transport `hd` (an `M`-edge equality) to a deleted-map edge equality
  rw [dartEdge, Sym2.eq_iff] at hd ⊢
  rcases hd with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    constructor
    · apply deletedVertexToM_injective M d0
      rw [deletedVertexToM_tail]; exact ha
    · apply deletedVertexToM_injective M d0
      rw [deletedVertexToM_head]; exact hb
  · right
    constructor
    · apply deletedVertexToM_injective M d0
      rw [deletedVertexToM_tail]; exact ha
    · apply deletedVertexToM_injective M d0
      rw [deletedVertexToM_head]; exact hb



variable {hNT : NearTriangulation M} {d0 : D} {v0 : M.Vertex}









/-- The reserved colors are genuinely absent from a fan vertex's deleted list. -/
lemma deleteFanLists_notMem (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) {γ δ : α}
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∈ fanInterior) :
    γ ∉ deleteFanLists M d0 fanInterior L γ δ q' ∧
      δ ∉ deleteFanLists M d0 fanInterior L γ δ q' := by
  rw [deleteFanLists_fan M d0 fanInterior L γ δ hq]
  constructor
  · simp
  · simp









lemma extendColoring_v0
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (c : (M.deleteVertex d0).Vertex → α) (a : α) :
    extendColoring R c a (Quotient.mk (cycleSetoid M.σ) d0) = a := by
  simp [extendColoring]

lemma extendColoring_other
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (c : (M.deleteVertex d0).Vertex → α) (a : α)
    {x : M.Vertex} (hx : x ≠ Quotient.mk (cycleSetoid M.σ) d0) :
    extendColoring R c a x = c (sectionToDeleted R x hx) := by
  simp [extendColoring, hx]



/--
**Deletion coloring extension (task item 3, the genuinely new content).**

Given the kept-dart reconstruction `R`, a list coloring `c` of the deleted map
from lists `L'` with `L' q' ⊆ L (toM q')`, and a chosen color `a ∈ L v0` that
avoids the color of every surviving `M`-neighbor of `v0`, the extended coloring
`extendColoring R c a` is a list coloring of all of `M.toSimpleGraph` from `L`.

The avoidance hypothesis `havoid` is exactly what the review's color reservation
supplies: at `v0` choose whichever of `γ, δ` differs from the color of `w`; the
fan vertices were colored from `L'` with `γ, δ` removed, and `x = p` keeps the
precolor `cp ≠ γ, δ`.  (The concrete construction of `a` and the discharge of
`havoid` from the fan/`deleteFanLists` data is `extend_avoid_of_fan` below.)
-/
theorem deleteBoundaryVertex_extend_coloring
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    {L : M.Vertex → Finset α} {L' : (M.deleteVertex d0).Vertex → Finset α}
    (hsub : ∀ q', L' q' ⊆ L (deletedVertexToM M d0 q'))
    {c : (M.deleteVertex d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex d0).toSimpleGraph L' c)
    {a : α} (ha : a ∈ L (Quotient.mk (cycleSetoid M.σ) d0))
    (havoid : ∀ ⦃u : M.Vertex⦄,
      M.toSimpleGraph.Adj (Quotient.mk (cycleSetoid M.σ) d0) u →
        extendColoring R c a u ≠ a) :
    IsListColoring M.toSimpleGraph L (extendColoring R c a) := by
  classical
  set v0 := Quotient.mk (cycleSetoid M.σ) d0 with hv0
  constructor
  · -- list validity
    intro x
    by_cases hx : x = v0
    · subst hx; rw [extendColoring_v0]; exact ha
    · rw [extendColoring_other R c a hx]
      have hmem := hc.1 (sectionToDeleted R x hx)
      have hsub' := hsub (sectionToDeleted R x hx)
      have hxeq : deletedVertexToM M d0 (sectionToDeleted R x hx) = x :=
        deletedVertexToM_sectionToDeleted R x hx
      rw [hxeq] at hsub'
      exact hsub' hmem
  · -- properness
    intro x y hxy
    by_cases hxv : x = v0
    · subst hxv
      rw [extendColoring_v0]
      exact (havoid hxy).symm
    · by_cases hyv : y = v0
      · subst hyv
        rw [extendColoring_v0]
        exact havoid (M.toSimpleGraph.symm hxy)
      · -- both survivors: pull back to a deleted-map edge
        rw [extendColoring_other R c a hxv, extendColoring_other R c a hyv]
        set qx := sectionToDeleted R x hxv with hqx
        set qy := sectionToDeleted R y hyv with hqy
        have hxeq : deletedVertexToM M d0 qx = x := deletedVertexToM_sectionToDeleted R x hxv
        have hyeq : deletedVertexToM M d0 qy = y := deletedVertexToM_sectionToDeleted R y hyv
        have hadjM : M.toSimpleGraph.Adj (deletedVertexToM M d0 qx) (deletedVertexToM M d0 qy) := by
          rw [hxeq, hyeq]; exact hxy
        have hadj' : (M.deleteVertex d0).toSimpleGraph.Adj qx qy :=
          deletedVertexToM_adj_reflect M d0 hadjM
        exact hc.2 hadj'



/-- **Every `M`-neighbour of `v0` lies on the exposed fan path.**  The fan
rotation darts are exactly the star of `v0` (`NeighborRotationOrder.vertexDarts_eq`),
and their heads are the fan-path neighbours (`heads_eq`).  Any dart realizing an
edge at `v0` has, after orienting it to tail `v0`, its head among those
neighbours. -/
theorem v0_neighbor_mem_fanPath {hNT : NearTriangulation M} {v0 : M.Vertex}
    (fan : NearTriangulation.BoundaryVertexFan hNT v0) {d0 : D}
    (htail : M.tail d0 = v0) {u : M.Vertex}
    (hadj : M.toSimpleGraph.Adj v0 u) :
    u ∈ NearTriangulation.fanPath fan.x fan.interior fan.w := by
  classical
  obtain ⟨hne, d, hd⟩ := hadj
  -- orient the dart so its tail is `v0`
  obtain ⟨d', htail', hhead'⟩ :
      ∃ d' : D, M.tail d' = v0 ∧ M.head d' = u := by
    rw [dartEdge, Sym2.eq_iff] at hd
    rcases hd with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact ⟨d, ht, hh⟩
    · exact ⟨M.α d, by rw [tail_alpha]; exact hh, by rw [head_alpha]; exact ht⟩
  -- `d'` is in the star of `v0`, hence in the rotation dart set
  have hstar : M.σ.SameCycle d0 d' := Quotient.exact (htail.trans htail'.symm)
  have hmem : d' ∈ M.vertexDarts d0 := (mem_vertexDarts M d0 d').mpr hstar
  have hrot := fan.rotation_order.vertexDarts_eq htail
  rw [hrot, List.mem_toFinset] at hmem
  -- its head is one of the listed neighbours
  have hheadmem : M.head d' ∈ fan.rotation_order.darts.map M.head :=
    List.mem_map_of_mem hmem
  rw [fan.rotation_order.heads_eq] at hheadmem
  rw [← hhead']
  exact hheadmem

/-- The reserved color of `v0` actually present in a fan-vertex deleted list is
absent from the coloring there.  This packages `deleteFanLists_notMem` against a
list coloring `c`: at a fan vertex `q'`, neither reserved color is `c q'`. -/
lemma color_ne_reserved_of_fan {d0 : D}
    {fanInterior : Finset M.Vertex} {L : M.Vertex → Finset α} {γ δ : α}
    {c : (M.deleteVertex d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex d0).toSimpleGraph
      (deleteFanLists M d0 fanInterior L γ δ) c)
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∈ fanInterior) :
    c q' ≠ γ ∧ c q' ≠ δ := by
  have hmem := hc.1 q'
  obtain ⟨hγ, hδ⟩ := deleteFanLists_notMem M d0 fanInterior L hq
  exact ⟨fun h => hγ (h ▸ hmem), fun h => hδ (h ▸ hmem)⟩

/--
**The avoidance discharge (the review's color reservation, completed).**

Working with the deleted lists `L' = deleteFanLists` and a list coloring `c` of
the deleted map, we choose the color `a ∈ {γ, δ}` of `v0` to differ from the
color of `w`, and prove the full neighbour-avoidance hypothesis of
`deleteBoundaryVertex_extend_coloring`.  The three review bullet points become the
hypotheses:

* `hγδ : γ ≠ δ` — the two reserved colors are distinct;
* `hx_avoid` — the endpoint `x` (the precolored vertex `p`, color `cp ∉ {γ, δ}`)
  has `extendColoring … x ∉ {γ, δ}`;
* the interior fan vertices avoid `γ, δ` automatically (`color_ne_reserved_of_fan`);
* `w` is avoided by the explicit choice of `a`.

It returns the chosen color `a` together with `a ∈ {γ, δ}` and the avoidance.
-/
theorem extend_avoid_of_fan {hNT : NearTriangulation M} {v0 : M.Vertex}
    (fan : NearTriangulation.BoundaryVertexFan hNT v0)
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (hd0 : Quotient.mk (cycleSetoid M.σ) d0 = v0)
    {L : M.Vertex → Finset α} {γ δ : α} (hγδ : γ ≠ δ)
    {c : (M.deleteVertex d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex d0).toSimpleGraph
      (deleteFanLists M d0 fan.interior.toFinset L γ δ) c)
    (hxp : fan.x ≠ v0)
    (hx_avoid : extendColoring R c γ fan.x ≠ γ ∧ extendColoring R c δ fan.x ≠ δ)
    (hwp : fan.w ≠ v0) :
    ∃ a : α, (a = γ ∨ a = δ) ∧
      (∀ ⦃u : M.Vertex⦄, M.toSimpleGraph.Adj v0 u → extendColoring R c a u ≠ a) := by
  classical
  -- choose `a ∈ {γ, δ}` differing from the color of `w`
  have hwsec : extendColoring R c γ fan.w = c (sectionToDeleted R fan.w (hd0 ▸ hwp))
      ∧ extendColoring R c δ fan.w = c (sectionToDeleted R fan.w (hd0 ▸ hwp)) := by
    constructor <;> rw [extendColoring_other _ _ _ (hd0 ▸ hwp)]
  set cw : α := c (sectionToDeleted R fan.w (hd0 ▸ hwp)) with hcw
  -- the value of `extendColoring` at any survivor is independent of the `v0`-color
  have hsurv_indep : ∀ {z : M.Vertex} (hz : z ≠ v0) (a₁ a₂ : α),
      extendColoring R c a₁ z = extendColoring R c a₂ z := by
    intro z hz a₁ a₂
    rw [extendColoring_other _ _ _ (hd0 ▸ hz), extendColoring_other _ _ _ (hd0 ▸ hz)]
  refine ⟨if cw = γ then δ else γ, ?_, ?_⟩
  · by_cases h : cw = γ
    · simp [h]
    · simp [h]
  · intro u hadj
    -- `u` is a fan-path vertex
    have hu : u ∈ NearTriangulation.fanPath fan.x fan.interior fan.w :=
      v0_neighbor_mem_fanPath fan (hd0) hadj
    -- the chosen color `a := if cw = γ then δ else γ`
    set a : α := if cw = γ then δ else γ with ha
    have ha_choice : a = γ ∨ a = δ := by
      by_cases h : cw = γ
      · right; simp [ha, h]
      · left; simp [ha, h]
    -- `u ≠ v0`
    have hune : u ≠ v0 := (M.toSimpleGraph.ne_of_adj hadj).symm
    simp only [NearTriangulation.fanPath, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hu
    rcases hu with (hux | huz) | huw
    · -- `u = x`: precolored / size-≥3 endpoint avoids both reserved colors
      subst hux
      have hxavoid' : extendColoring R c a fan.x ≠ γ ∧ extendColoring R c a fan.x ≠ δ := by
        constructor
        · rw [hsurv_indep hxp a γ]; exact hx_avoid.1
        · rw [hsurv_indep hxp a δ]; exact hx_avoid.2
      rcases ha_choice with h | h
      · simpa only [h] using hxavoid'.1
      · simpa only [h] using hxavoid'.2
    · -- `u = z_i` interior fan vertex: colored from list with `γ, δ` removed
      have hune' : u ≠ v0 := hune
      set q' := sectionToDeleted R u (hd0 ▸ hune') with hq'
      have hqeq : deletedVertexToM M d0 q' = u :=
        deletedVertexToM_sectionToDeleted R u (hd0 ▸ hune')
      have hqfan : deletedVertexToM M d0 q' ∈ fan.interior.toFinset := by
        rw [hqeq, List.mem_toFinset]; exact huz
      have hcq := color_ne_reserved_of_fan hc hqfan
      have heq : extendColoring R c a u = c q' := by
        rw [extendColoring_other _ _ _ (hd0 ▸ hune')]
      rw [heq]
      rcases ha_choice with h | h
      · rw [h]; exact hcq.1
      · rw [h]; exact hcq.2
    · -- `u = w`: avoided by the explicit choice of `a`
      subst huw
      have hval : extendColoring R c a fan.w = cw := by
        rw [extendColoring_other _ _ _ (hd0 ▸ hwp)]
      rw [hval, ha]
      by_cases h : cw = γ
      · rw [if_pos h, h]; exact hγδ
      · rw [if_neg h]; exact h

/-- The deleted lists are pointwise contained in `L` (through the kept-dart map):
they either keep `L` or shrink it by removing the two reserved colors. -/
lemma deleteFanLists_subset (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) (γ δ : α)
    (q' : (M.deleteVertex d0).Vertex) :
    deleteFanLists M d0 fanInterior L γ δ q' ⊆ L (deletedVertexToM M d0 q') := by
  classical
  by_cases hq : deletedVertexToM M d0 q' ∈ fanInterior
  · rw [deleteFanLists_fan M d0 fanInterior L γ δ hq]; exact Finset.sdiff_subset
  · rw [deleteFanLists_other M d0 fanInterior L γ δ hq]

/--
**The complete deletion list transport (task item 3, assembled).**

Given the fan, the kept-dart reconstruction, two distinct reserved colors
`γ, δ ∈ L v0` removed only at the fan interior vertices, a list coloring `c` of
the deleted map from `deleteFanLists`, and the review's two endpoint conditions
(the `x` endpoint avoids both reserved colors, and `x, w ≠ v0`), the coloring
extends to a list coloring of all of `M` from `L`.  Both ingredients
(`extend_avoid_of_fan` and `deleteBoundaryVertex_extend_coloring`) are combined.
-/
theorem deleteBoundaryVertex_listColorable
    {hNT : NearTriangulation M} {v0 : M.Vertex} {d0 : D}
    (fan : NearTriangulation.BoundaryVertexFan hNT v0)
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (hd0 : Quotient.mk (cycleSetoid M.σ) d0 = v0)
    {L : M.Vertex → Finset α} {γ δ : α} (hγδ : γ ≠ δ)
    (hγ : γ ∈ L v0) (hδ : δ ∈ L v0)
    {c : (M.deleteVertex d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex d0).toSimpleGraph
      (deleteFanLists M d0 fan.interior.toFinset L γ δ) c)
    (hxp : fan.x ≠ v0) (hwp : fan.w ≠ v0)
    (hx_avoid : extendColoring R c γ fan.x ≠ γ ∧ extendColoring R c δ fan.x ≠ δ) :
    ListColorable M.toSimpleGraph L := by
  obtain ⟨a, ha_choice, havoid⟩ :=
    extend_avoid_of_fan fan R hd0 hγδ hc hxp hx_avoid hwp
  have ha_mem : a ∈ L (Quotient.mk (cycleSetoid M.σ) d0) := by
    rw [hd0]; rcases ha_choice with rfl | rfl
    · exact hγ
    · exact hδ
  refine ⟨extendColoring R c a, ?_⟩
  refine deleteBoundaryVertex_extend_coloring R
    (deleteFanLists_subset M d0 fan.interior.toFinset L γ δ) hc ha_mem ?_
  intro u hadj
  exact havoid (hd0 ▸ hadj)

end Deletion

end CombMap

end ProofsInTheBook.ThomassenLists

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanSurgery
-/
/- Source module: ProofsInTheBook.PlanarMapFanConnectivity -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]




















section Reduction

variable (M : CombMap D) (v : D)







end Reduction



namespace NearTriangulation

variable {M : CombMap D}









variable {hNT : NearTriangulation M} {v0 : M.Vertex}

























end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanConnectivity
import ProofsInTheBook.PlanarMapFilteredRotation
-/
/- Source module: ProofsInTheBook.PlanarMapFanFaces -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]







namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}











































































end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
-/
/- Source module: ProofsInTheBook.PlanarMapFanMergedOrbit -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

















namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}













































end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryArcSplit -/
section
set_option autoImplicit true




set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}













end BoundaryCycleData









namespace DataDartArc

variable {M : CombMap D} {f : M.Face} {K : BoundaryCycleData M f} {u v : M.Vertex}



















end DataDartArc



namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}









end BoundaryCycleData



section Casts

variable {M : CombMap D}











end Casts





















namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}







end BoundaryPath



section BPOfDartArc

variable {M : CombMap D}



















end BPOfDartArc



namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}







end BoundaryCycleData



namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}





end BoundaryCycleData

end CombMap

end ProofsInTheBook.PlanarMap





end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.PlanarMapBoundaryArcSplit
-/
/- Source module: ProofsInTheBook.PlanarMapDeletedBoundary -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]





















namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}










namespace DeletedMergedBoundaryCertificate

variable {d0 : D}











end DeletedMergedBoundaryCertificate









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanMergedOrbit
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapOuterArc -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}




namespace MergedOuterArcData

variable {d0 : D} {r : {d : D // d ∉ M.deleteVertexSet d0}} {outerFace : M.Face}







end MergedOuterArcData















end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapOuterArc
-/
/- Source module: ProofsInTheBook.PlanarMapFanExistence -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]























namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)



















variable {hNT}















end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenLists
import ProofsInTheBook.PlanarMapFanExistence
-/
/- Source module: ProofsInTheBook.ThomassenInduction -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ThomassenInduction

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u











section Base

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/-- **The base triangle.**  When `M.V = 3`, every vertex is `p`, `q`, or a third
vertex `r ≠ p, q`.  The third vertex has list size `≥ 3` (boundary `≥ 3` / interior
`≥ 5`), so `L r \ {cp, cq}` is nonempty; coloring `p ↦ cp`, `q ↦ cq`, and everything
else by that free color gives a list coloring of `M`. -/
theorem base_case (h : ThomassenLists hNT p q L cp cq) (hV : M.V = 3) :
    ListColorable M.toSimpleGraph L := by
  classical
  have hpq : p ≠ q := h.p_ne_q
  -- `M.Vertex` is a fintype of card 3.
  have hcard : Fintype.card M.Vertex = 3 := hV
  -- obtain the third vertex.
  obtain ⟨r, hrp, hrq⟩ : ∃ r : M.Vertex, r ≠ p ∧ r ≠ q := by
    by_contra hcon
    push_neg at hcon
    -- then every vertex is p or q, so card ≤ 2, contradiction.
    have hsub : (Finset.univ : Finset M.Vertex) ⊆ {p, q} := by
      intro x _
      rcases eq_or_ne x p with hx | hx
      · simp [hx]
      · have := hcon x hx
        simp [this]
    have : Fintype.card M.Vertex ≤ 2 := by
      calc Fintype.card M.Vertex = (Finset.univ : Finset M.Vertex).card := rfl
        _ ≤ ({p, q} : Finset M.Vertex).card := Finset.card_le_card hsub
        _ ≤ 2 := by
            refine (Finset.card_insert_le _ _).trans ?_
            simp
    omega
  -- every vertex is p, q, or r.
  have hall : ∀ x : M.Vertex, x = p ∨ x = q ∨ x = r := by
    intro x
    by_contra hx
    push_neg at hx
    obtain ⟨hxp, hxq, hxr⟩ := hx
    have hsub : ({p, q, r, x} : Finset M.Vertex) ⊆ Finset.univ := Finset.subset_univ _
    have hpn : p ∉ ({q, r, x} : Finset M.Vertex) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hpq, (fun h => hrp h.symm), fun h => hxp h.symm⟩
    have hqn : q ∉ ({r, x} : Finset M.Vertex) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hrq.symm, fun h => hxq h.symm⟩
    have hrn : r ∉ ({x} : Finset M.Vertex) := by
      simp only [Finset.mem_singleton]; exact hxr.symm
    have h4 : ({p, q, r, x} : Finset M.Vertex).card = 4 := by
      rw [show ({p, q, r, x} : Finset M.Vertex)
            = insert p (insert q (insert r {x})) from rfl,
        Finset.card_insert_of_notMem hpn, Finset.card_insert_of_notMem hqn,
        Finset.card_insert_of_notMem hrn, Finset.card_singleton]
    have : 4 ≤ Fintype.card M.Vertex := by
      calc 4 = ({p, q, r, x} : Finset M.Vertex).card := h4.symm
        _ ≤ Fintype.card M.Vertex := Finset.card_le_card hsub
    omega
  -- `r` has list size at least 3.
  have hr3 : 3 ≤ (L r).card := by
    by_cases hb : hNT.outerCycle.IsBoundaryVertex r
    · exact h.boundary_ge_three r hb hrp hrq
    · exact le_trans (by norm_num) (h.interior_ge_five r hb)
  -- choose a free color for `r`, avoiding `cp, cq`.
  have hne : (L r \ {cp, cq}).Nonempty := by
    rw [← Finset.card_pos]
    have hle : ((L r) \ {cp, cq}).card ≥ (L r).card - ({cp, cq} : Finset α).card := by
      have := Finset.le_card_sdiff ({cp, cq} : Finset α) (L r)
      omega
    have h2 : ({cp, cq} : Finset α).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  obtain ⟨a, ha⟩ := hne
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ha
  obtain ⟨haL, hane⟩ := ha
  push_neg at hane
  obtain ⟨hacp, hacq⟩ := hane
  -- the coloring and its pointwise values.
  set col : M.Vertex → α := fun x => if x = p then cp else if x = q then cq else a
    with hcoldef
  have col_p : col p = cp := by simp [hcoldef]
  have col_q : col q = cq := by simp [hcoldef, hpq.symm]
  have col_r : col r = a := by simp [hcoldef, hrp, hrq]
  refine ⟨col, ?_, ?_⟩
  · -- list validity
    intro x
    rcases hall x with hx | hx | hx
    · rw [hx, col_p, h.list_p]; exact Finset.mem_singleton_self cp
    · rw [hx, col_q, h.list_q]; exact Finset.mem_singleton_self cq
    · rw [hx, col_r]; exact haL
  · -- properness: the three colors cp, cq, a are pairwise distinct, so any two
    -- vertices with distinct identities get distinct colors.
    have hcards : ∀ x y : M.Vertex, x ≠ y → col x ≠ col y := by
      intro x y hxyne
      rcases hall x with hxp | hxq | hxr <;> rcases hall y with hyp | hyq | hyr
      · exact absurd (hxp.trans hyp.symm) hxyne
      · rw [hxp, col_p, hyq, col_q]; exact h.colors_ne
      · rw [hxp, col_p, hyr, col_r]; exact fun hh => hacp hh.symm
      · rw [hxq, col_q, hyp, col_p]; exact h.colors_ne.symm
      · exact absurd (hxq.trans hyq.symm) hxyne
      · rw [hxq, col_q, hyr, col_r]; exact fun hh => hacq hh.symm
      · rw [hxr, col_r, hyp, col_p]; exact hacp
      · rw [hxr, col_r, hyq, col_q]; exact hacq
      · exact absurd (hxr.trans hyr.symm) hxyne
    intro x y hxy
    exact hcards x y (M.toSimpleGraph.ne_of_adj hxy)

end Base



section Chord

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}



end Chord



section Chordless

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}





/-- The deleted map has strictly fewer vertices. -/
theorem deleted_smaller (cod : ChordlessOracle hNT p q L cp cq) (hV : 3 ≤ M.V) :
    (M.deleteVertex cod.fanData.d0).V < M.V := by
  have hsm : (M.deleteVertex cod.fanData.d0).V = M.V - 1 := cod.recon.smaller
  omega



/-- The first fan endpoint `x = p` is not a fan *interior* vertex: the fan path
`x :: interior ++ [w]` has nodup vertex list (chordlessness), so its head `x` does
not appear in `interior`. -/
lemma fanX_notMem_interior (cod : ChordlessOracle hNT p q L cp cq) :
    (codFan cod).x ∉ (codFan cod).interior := by
  have hnodup := (codFan cod).path_nodup_of_chordless cod.chordless
  -- `fanPath x interior w = (x :: interior) ++ [w]` (`::` binds tighter than `++`).
  rw [NearTriangulation.fanPath] at hnodup
  rw [List.nodup_append] at hnodup
  have hleft : ((codFan cod).x :: (codFan cod).interior).Nodup := hnodup.1
  rw [List.nodup_cons] at hleft
  exact hleft.1

/-- **The fan endpoint `x` avoids both reserved colors in the extension.**
`x` is one of the two precolored endpoints, survives the deletion, and is not a
fan-interior vertex.  The fan-deleted list there is the corresponding singleton,
so the deleted coloring assigns the corresponding precolored color. -/
lemma chordless_hx_avoid (cod : ChordlessOracle hNT p q L cp cq)
    (h : ThomassenLists hNT p q L cp cq)
    {c : (M.deleteVertex cod.fanData.d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex cod.fanData.d0).toSimpleGraph (codLists cod) c) :
    extendColoring cod.recon c cod.γ (codFan cod).x ≠ cod.γ ∧
      extendColoring cod.recon c cod.δ (codFan cod).x ≠ cod.δ := by
  classical
  -- `x = p ≠ v0`, so `x` survives.
  have hxne : (codFan cod).x ≠ Quotient.mk (cycleSetoid M.σ) cod.fanData.d0 := by
    rw [cod.hd0]; exact cod.x_ne
  -- the section vertex at `x`.
  set q' : (M.deleteVertex cod.fanData.d0).Vertex :=
    sectionToDeleted cod.recon (codFan cod).x hxne with hq'
  have hq'toM : deletedVertexToM M cod.fanData.d0 q' = (codFan cod).x :=
    deletedVertexToM_sectionToDeleted cod.recon (codFan cod).x hxne
  -- `x`'s image is not a fan-interior vertex.
  have hnotfan : deletedVertexToM M cod.fanData.d0 q' ∉ (codFan cod).interior.toFinset := by
    rw [hq'toM, List.mem_toFinset]; exact fanX_notMem_interior cod
  -- so the fan-deleted list at `q'` is the old list at `x`.
  have hlistx : codLists cod q' = L (codFan cod).x := by
    rw [codLists, deleteFanLists_other M cod.fanData.d0 (codFan cod).interior.toFinset L
      cod.γ cod.δ hnotfan, hq'toM]
  -- the deleted coloring at `q'` is in the appropriate singleton.
  have hmem : c q' ∈ L (codFan cod).x := hlistx ▸ hc.1 q'
  -- `extendColoring _ c a x = c q'` (survivor) for any reserved color.
  have hext : ∀ a : α, extendColoring cod.recon c a (codFan cod).x = c q' := by
    intro a
    rw [extendColoring_other cod.recon c a hxne]
  rcases cod.x_precolored with ⟨hx, hcpγ, hcpδ⟩ | ⟨hx, hcqγ, hcqδ⟩
  · have hmem_cp : c q' = cp := by
      simpa [codFan, hx, h.list_p] using hmem
    constructor
    · rw [hext cod.γ, hmem_cp]; exact hcpγ
    · rw [hext cod.δ, hmem_cp]; exact hcpδ
  · have hmem_cq : c q' = cq := by
      simpa [codFan, hx, h.list_q] using hmem
    constructor
    · rw [hext cod.γ, hmem_cq]; exact hcqγ
    · rw [hext cod.δ, hmem_cq]; exact hcqδ

/-- **The chordless case.**  Given that the deleted map is list-colorable from the
fan-deleted lists `codLists`, the coloring extends across `v0` to a list coloring of
`M` (`deleteBoundaryVertex_listColorable`).  The precolored-endpoint avoidance is
discharged by `chordless_hx_avoid`. -/
theorem chordless_case (h : ThomassenLists hNT p q L cp cq)
    (cod : ChordlessOracle hNT p q L cp cq)
    (hdel : ListColorable (M.deleteVertex cod.fanData.d0).toSimpleGraph (codLists cod)) :
    ListColorable M.toSimpleGraph L := by
  obtain ⟨c, hc⟩ := hdel
  exact deleteBoundaryVertex_listColorable (codFan cod) cod.recon cod.hd0 cod.γδ_ne
    (cod.hd0 ▸ cod.γ_mem) (cod.hd0 ▸ cod.δ_mem) hc cod.x_ne cod.w_ne
    (chordless_hx_avoid cod h hc)

end Chordless



section Induction

variable {α : Type u} [DecidableEq α]







end Induction



section Corollaries

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D}

/-- **Every near-triangulation has an adjacent precolorable boundary edge.**  The
root dart of the outer cycle realizes a boundary edge `s(p, q)` with `p ≠ q`, both
boundary vertices, adjacent in `M.toSimpleGraph`. -/
theorem exists_boundary_edge (hNT : NearTriangulation M) :
    ∃ p q : M.Vertex, p ≠ q ∧
      hNT.outerCycle.IsBoundaryVertex p ∧ hNT.outerCycle.IsBoundaryVertex q ∧
      hNT.outerCycle.IsBoundaryEdge s(p, q) ∧ M.toSimpleGraph.Adj p q := by
  classical
  let d := hNT.outerCycle.root
  refine ⟨M.tail d, M.head d, hNT.simpleGraph.no_loop d, ?_, ?_, ?_, ?_⟩
  · -- tail root is a boundary vertex
    show M.tail d ∈ hNT.outerCycle.vertices
    rw [hNT.outerCycle.vertices_eq]
    exact List.mem_map_of_mem (hNT.outerCycle.root_mem_darts)
  · -- head root is a boundary vertex: it is the tail of the next boundary dart
    show M.head d ∈ hNT.outerCycle.vertices
    have hpos := hNT.outerCycle.normalized.length_pos
    have hroot0 :
        hNT.outerCycle.darts.get ⟨0, hpos⟩ = d := by
      have hh := hNT.outerCycle.normalized.head_eq
      rw [List.head?_eq_getElem?] at hh
      simp only [List.getElem?_eq_getElem hpos, Option.some.injEq] at hh
      simp only [List.get_eq_getElem]
      exact hh
    have hcons := hNT.outerCycle.consecutive_vertex ⟨0, hpos⟩
    rw [hroot0] at hcons
    rw [← hcons, hNT.outerCycle.vertices_eq]
    exact List.mem_map_of_mem (hNT.outerCycle.darts.get_mem _)
  · -- s(tail root, head root) is a boundary edge
    show s(M.tail d, M.head d) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hde : M.dartEdge d = s(M.tail d, M.head d) := rfl
    rw [← hde]
    exact List.mem_map_of_mem (hNT.outerCycle.root_mem_darts)
  · exact toSimpleGraph_adj_of_dart M hNT.simpleGraph d



end Corollaries



section FiveColor

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D}



end FiveColor

end ProofsInTheBook.ThomassenInduction

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenInduction
import ProofsInTheBook.PlanarMapChordSplit
import ProofsInTheBook.PlanarMapSeparation
-/
/- Source module: ProofsInTheBook.ChordSplitNT -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSplitNT

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u



variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}





namespace ChordSideReconstruction

variable {s : Set M.Vertex} {L : M.Vertex → Finset α}



@[simp]
lemma ι_section (R : ChordSideReconstruction hNT s L)
    {w : M.Vertex} (hw : w ∈ s) : R.ι (R.section_ hw) = w :=
  (R.ι_surj hw).choose_spec





/-- On the region, the region coloring is `c` of the section. -/
lemma colorRegion_eq (R : ChordSideReconstruction hNT s L)
    (c : R.N.Vertex → α) (default : α) {w : M.Vertex} (hw : w ∈ s) :
    R.colorRegion c default w = c (R.section_ hw) := by
  simp [colorRegion, hw]



/-- **The transported region coloring is proper on the side region.** -/
theorem colorRegion_properOn (R : ChordSideReconstruction hNT s L)
    {c : R.N.Vertex → α} (hc : IsListColoring R.N.toSimpleGraph R.Lₛ c)
    (default : α) :
    ProperOn M.toSimpleGraph s (R.colorRegion c default) := by
  intro a b ha hb hab
  -- write `a = ι x`, `b = ι y` via the section, reflect adjacency to `N`.
  set x := R.section_ ha with hx
  set y := R.section_ hb with hy
  have hax : R.ι x = a := ι_section R ha
  have hby : R.ι y = b := ι_section R hb
  rw [colorRegion_eq R c default ha, colorRegion_eq R c default hb, ← hx, ← hy]
  -- adjacency `M.Adj a b = M.Adj (ι x) (ι y)` reflects to `N.Adj x y`.
  have hadjN : R.N.toSimpleGraph.Adj x y :=
    R.ι_adj_reflect (by rw [hax, hby]; exact hab)
  exact hc.2 hadjN

/-- **The transported region coloring is list-valid on the side region.** -/
theorem colorRegion_listValidOn (R : ChordSideReconstruction hNT s L)
    {c : R.N.Vertex → α} (hc : IsListColoring R.N.toSimpleGraph R.Lₛ c)
    (default : α) :
    ListValidOn L s (R.colorRegion c default) := by
  intro w hw
  rw [colorRegion_eq R c default hw]
  have hmem : c (R.section_ hw) ∈ R.Lₛ (R.section_ hw) := hc.1 _
  rw [R.Lₛ_eq, ι_section] at hmem
  exact hmem

end ChordSideReconstruction





namespace ChordRecursionData

variable {u v p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}





/-- `color₁` is proper + list-valid on side 1 (transported from the side-1
recursion via `colorRegion_properOn`/`colorRegion_listValidOn`). -/
lemma color₁_spec (data : ChordRecursionData hNT u v p q L cp cq) (default : α)
    (ih : ∀ (m : ℕ), m < M.V → ∀ {Dₛ : Type u} [Fintype Dₛ] [DecidableEq Dₛ]
      {N : CombMap Dₛ} (hN : NearTriangulation N) (pₛ qₛ : N.Vertex)
      (Lₛ : N.Vertex → Finset α) (cpₛ cqₛ : α), N.V ≤ m →
      ThomassenLists hN pₛ qₛ Lₛ cpₛ cqₛ → ListColorable N.toSimpleGraph Lₛ) :
    ProperOn M.toSimpleGraph data.regions.s₁ (data.color₁ default ih) ∧
      ListValidOn L data.regions.s₁ (data.color₁ default ih) := by
  classical
  have hcol₁ : ListColorable data.R₁.N.toSimpleGraph data.R₁.Lₛ :=
    ih data.R₁.N.V data.R₁.smaller data.R₁.hN data.R₁.pₛ data.R₁.qₛ data.R₁.Lₛ
      data.R₁.cpₛ data.R₁.cqₛ le_rfl data.R₁.hLₛ
  refine ⟨?_, ?_⟩
  · exact data.R₁.colorRegion_properOn hcol₁.choose_spec default
  · exact data.R₁.colorRegion_listValidOn hcol₁.choose_spec default

/-- **The chord case, closed by recursion.**

Given the chord recursion data and the strong-induction hypothesis `ih`, the
underlying map `M` is list-colorable.  We color side 1 by recursion (`color₁`),
*force* the chord endpoints `u, v` to the side-1 colors, color side 2 by recursion
(through `R₂ (color₁ …)`), and glue.  No side colorings are taken as input — they
are produced by the recursive calls.  This is the drop-in replacement for the
oracle-fed `ThomassenInduction.chord_case`. -/
theorem chord_case_recursive (data : ChordRecursionData hNT u v p q L cp cq)
    (h : ThomassenLists hNT p q L cp cq)
    (ih : ∀ (m : ℕ), m < M.V → ∀ {Dₛ : Type u} [Fintype Dₛ] [DecidableEq Dₛ]
      {N : CombMap Dₛ} (hN : NearTriangulation N) (pₛ qₛ : N.Vertex)
      (Lₛ : N.Vertex → Finset α) (cpₛ cqₛ : α), N.V ≤ m →
      ThomassenLists hN pₛ qₛ Lₛ cpₛ cqₛ → ListColorable N.toSimpleGraph Lₛ) :
    ListColorable M.toSimpleGraph L := by
  classical
  -- a default color (some color of `L p`, which is nonempty).
  obtain ⟨d0, _⟩ := h.list_nonempty p
  -- side 1 by recursion.
  set c₁ := data.color₁ d0 ih with hc₁
  obtain ⟨hc₁p, hc₁L⟩ := data.color₁_spec d0 ih
  have hcuv : c₁ u ≠ c₁ v := data.regions.chord_endpoints_colors_ne hc₁p
  -- side 2 by recursion, on the forced lists.
  set R₂ := data.R₂ c₁ hcuv with hR₂
  have hcol₂ : ListColorable R₂.N.toSimpleGraph R₂.Lₛ :=
    ih R₂.N.V R₂.smaller R₂.hN R₂.pₛ R₂.qₛ R₂.Lₛ R₂.cpₛ R₂.cqₛ le_rfl R₂.hLₛ
  set c₂ := R₂.colorRegion hcol₂.choose d0 with hc₂
  have hc₂p : ProperOn M.toSimpleGraph data.regions.s₂ c₂ :=
    R₂.colorRegion_properOn hcol₂.choose_spec d0
  have hc₂Lforced : ListValidOn (data.regions.forcedLists c₁ L) data.regions.s₂ c₂ :=
    R₂.colorRegion_listValidOn hcol₂.choose_spec d0
  -- the chord endpoints are in side 1 (precolored region) and side 2.
  have hu₁ : u ∈ data.regions.s₁ := data.regions.u_s₁
  have hv₁ : v ∈ data.regions.s₁ := data.regions.v_s₁
  have hu₂ : u ∈ data.regions.s₂ := data.regions.u_s₂
  have hv₂ : v ∈ data.regions.s₂ := data.regions.v_s₂
  -- `c₁ u ∈ L u`, `c₁ v ∈ L v` (side 1 list valid on its region).
  have hc₁uL : c₁ u ∈ L u := hc₁L hu₁
  have hc₁vL : c₁ v ∈ L v := hc₁L hv₁
  -- side-2 colors at the chord endpoints equal `c₁`'s (forced singleton lists).
  have hc₂u : c₂ u = c₁ u := by
    have hmem := hc₂Lforced hu₂
    rw [data.regions.forcedLists_u] at hmem
    exact Finset.mem_singleton.mp hmem
  have hc₂v : c₂ v = c₁ v := by
    have hmem := hc₂Lforced hv₂
    rw [data.regions.forcedLists_v data.uv_ne] at hmem
    exact Finset.mem_singleton.mp hmem
  -- downgrade side-2 list validity from `forcedLists` to `L`.
  have hc₂L : ListValidOn L data.regions.s₂ c₂ := by
    intro w hw
    by_cases hwu : w = u
    · subst hwu; rw [hc₂u]; exact hc₁uL
    · by_cases hwv : w = v
      · subst hwv; rw [hc₂v]; exact hc₁vL
      · have hmem := hc₂Lforced hw
        rwa [data.regions.forcedLists_other hwu hwv] at hmem
  -- glue.
  exact data.regions.glue hc₁p hc₁L hc₂p hc₂L hc₂u.symm hc₂v.symm

end ChordRecursionData





/-- **The Thomassen induction with the chord case recursing (auxiliary).**

By strong induction on the vertex bound `n`.  The chord branch uses
`ChordRecursionData.chord_case_recursive`: it recurses on the two strictly-smaller
side near-triangulations to *produce* the side colorings, then glues — instead of
reading colorings out of an oracle.  The chordless branch is the existing recursive
`ThomassenInduction.chordless_case`. -/
theorem thomassen_aux_chordRecursive (O : ChordRecursiveDichotomy α) :
    ∀ (n : ℕ) {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), M.V ≤ n → ThomassenLists hNT p q L cp cq →
      ListColorable M.toSimpleGraph L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D _ _ M hNT p q L cp cq hVn h
    have hV3 : 3 ≤ M.V := three_le_V hNT
    rcases eq_or_lt_of_le hV3 with hV | hV
    · -- base case `M.V = 3`
      exact base_case h hV.symm
    · -- `3 < M.V`: use the recursive dichotomy.
      rcases O.decide hNT p q L cp cq hV h with ⟨u, v, data⟩ | cod
      · -- chord case: RECURSE on the two side near-triangulations.
        refine data.chord_case_recursive h ?_
        -- supply the strong-induction hypothesis in the side-recursion shape.
        intro m hm Dₛ _ _ N hN pₛ qₛ Lₛ cpₛ cqₛ hNm hLₛ
        exact ih m (lt_of_lt_of_le hm hVn) hN pₛ qₛ Lₛ cpₛ cqₛ hNm hLₛ
      · -- chordless case: recurse on the deleted map (existing machinery).
        have hsmaller : (M.deleteVertex cod.fanData.d0).V < M.V :=
          deleted_smaller cod hV3
        obtain ⟨p', q', cp', cq', hlists'⟩ := cod.deleted_lists
        have hdel : ListColorable (M.deleteVertex cod.fanData.d0).toSimpleGraph
            (codLists cod) :=
          ih (M.deleteVertex cod.fanData.d0).V (by omega)
            (deletedNT cod) p' q' (codLists cod) cp' cq' le_rfl hlists'
        exact chordless_case h cod hdel

/-- **The Thomassen induction with the chord case recursing (main theorem).**

Given the chord-recursive dichotomy `O` (chord branch supplies recursion data, NOT
colorings), every near-triangulation with the Thomassen list hypotheses is
list-colorable.  The chord case recurses on the two side near-triangulations — the
structural fix to `ThomassenInduction`'s oracle-fed chord branch. -/
theorem nearTriangulation_listColorable_chordRecursive (O : ChordRecursiveDichotomy α)
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
    (cp cq : α) (h : ThomassenLists hNT p q L cp cq) :
    ListColorable M.toSimpleGraph L :=
  thomassen_aux_chordRecursive O M.V hNT p q L cp cq le_rfl h







end ProofsInTheBook.ChordSplitNT









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitNT
-/
/- Source module: ProofsInTheBook.ChordSplitEuler -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSplitEuler

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]









section VertexCount

variable (ρ : Equiv.Perm K) {a₀ a₁ : K} (hne : a₀ ≠ a₁)























end VertexCount



section EulerReduction

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)





end EulerReduction



section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}













end ChordApplication



section NonVacuity













end NonVacuity

end ProofsInTheBook.ChordSplitEuler











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitEuler
-/
/- Source module: ProofsInTheBook.ChordSideRecon -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSideRecon

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section Connectivity

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)
















end Connectivity



section SphereAssembly

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)



end SphereAssembly



section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}









end ChordApplication



section JordanData

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  (a₀ a₁ : K) (hne : a₀ ≠ a₁)





end JordanData



section NonVacuity







end NonVacuity

end ProofsInTheBook.ChordSideRecon











end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFilteredRotation
import ProofsInTheBook.PlanarMapSeparation
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]





namespace SimplePrimalCycle

variable {M : CombMap D}



































































end SimplePrimalCycle









namespace SimplePrimalCycle

variable {M : CombMap D}



  -- c_i^- ↦ α (dart i)





















end SimplePrimalCycle





namespace CutCapSurgery

variable {M : CombMap D} {C : SimplePrimalCycle M}









end CutCapSurgery



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)











end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapSigma -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}



















































       -- c_i^- ↦ p_i

  -- c_i^- ↦ ℓ_i^- = σ⁻¹ q_i























































end SimplePrimalCycle









end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.PermTranspositionCycleCount -/
section
set_option autoImplicit true


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

open Equiv Equiv.Perm Function

variable {D : Type*} [Fintype D] [DecidableEq D]



namespace PermTranspositionCycleCount

open scoped Finset









































end PermTranspositionCycleCount





end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.RelationComponentCount -/
section
set_option autoImplicit true


open Classical

universe u

variable {V : Type u} [Fintype V]







































end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PermTranspositionCycleCount
import ProofsInTheBook.RelationComponentCount
-/
/- Source module: ProofsInTheBook.PlanarMapEulerInequality -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]















































































end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapCounts -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



namespace CutCapCount

















section SumCongr

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]



















end SumCongr

end CutCapCount



namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount
















end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapCounts
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapV -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount
































end SimplePrimalCycle

namespace CutCapCount

variable {E : Type*} [Fintype E] [DecidableEq E]













end CutCapCount

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount






























































































































































end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapV
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapF -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CutCapCount

variable {E : Type*} [Fintype E] [DecidableEq E]





end CutCapCount

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount















































end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideRecon
import ProofsInTheBook.PlanarMapCutCapCounts
import ProofsInTheBook.PlanarMapCutCapF
-/
/- Source module: ProofsInTheBook.ChordFaceCount -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.PlanarMap.CombMap.CutCapCount

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section FacePerm

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)













end FacePerm



section FaceBijection

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)





































end FaceBijection



section Dichotomy

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)











end Dichotomy



section Genus0

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)









end Genus0



section SphereAssembly

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)





end SphereAssembly



section NonVacuity







end NonVacuity



section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}





end ChordApplication



section Headline

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



end Headline

end ProofsInTheBook.ChordFaceCount















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordFaceCount
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ChordDisk -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordDisk

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section Facts

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  (a₀ a₁ : K)





end Facts



section LowerHalf

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)





end LowerHalf



section Threading

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)







end Threading



section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

















end ChordApplication



section NonVacuity











end NonVacuity



section Headline

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



end Headline



end ProofsInTheBook.ChordDisk
















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordDisk
-/
/- Source module: ProofsInTheBook.SubmapPlanar -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.SubmapPlanar

open Equiv
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]





















section OrbitSplit

variable (p : Equiv.Perm D) (S : Finset D)

open scoped Classical















end OrbitSplit





section RawRestrict

variable (M : CombMap D) (Del : Finset D)

open scoped Classical





































variable (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
  (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)

open scoped Classical













































































end RawRestrict



section ChordThreading

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSideRecon

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}













end ChordThreading

end ProofsInTheBook.SubmapPlanar

















end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.TetPearls -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Classical
open Set

namespace ProofsInTheBook.TetPearls







namespace Tet



















end Tet





namespace TetSolid







end TetSolid









namespace Segment3







































































end Segment3



namespace Tet













end Tet





















namespace Pearl








end Pearl





































end ProofsInTheBook.TetPearls

end
end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter09 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct
open Polynomial Chebyshev





















































-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)












































































































































































































































































end ProofsInTheBook.Chapter09

end

/- Original source header (imports hoisted):
import ProofsInTheBook.TetPearls
import ProofsInTheBook.Chapter09
-/
/- Source module: ProofsInTheBook.TetDihedral -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls

namespace ProofsInTheBook.TetDihedral

























































































end ProofsInTheBook.TetDihedral

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.TetDihedral
-/
/- Source module: ProofsInTheBook.SphericalKernel -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral

namespace ProofsInTheBook.SphericalKernel




























































































































end ProofsInTheBook.SphericalKernel

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalKernel
-/
/- Source module: ProofsInTheBook.SphericalArm -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.SphericalArm







































































end ProofsInTheBook.SphericalArm

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArm
-/
/- Source module: ProofsInTheBook.SphericalRotation -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm

namespace ProofsInTheBook.SphericalRotation






























































































variable {ι : Type*}

























end ProofsInTheBook.SphericalRotation

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.SphericalSZ -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.SphericalSZ


























end ProofsInTheBook.SphericalSZ

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZ
-/
/- Source module: ProofsInTheBook.SphericalCore -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ

namespace ProofsInTheBook.SphericalCore

















































end ProofsInTheBook.SphericalCore

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCore
-/
/- Source module: ProofsInTheBook.SphericalFinish -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore

namespace ProofsInTheBook.SphericalFinish









































end ProofsInTheBook.SphericalFinish

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalFinish
-/
/- Source module: ProofsInTheBook.SphericalOpening -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish

namespace ProofsInTheBook.SphericalOpening

























end ProofsInTheBook.SphericalOpening

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpening
-/
/- Source module: ProofsInTheBook.SphericalHinge -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening

namespace ProofsInTheBook.SphericalHinge



















































end ProofsInTheBook.SphericalHinge

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalHinge
-/
/- Source module: ProofsInTheBook.SphericalSZChain -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge

namespace ProofsInTheBook.SphericalSZChain































end ProofsInTheBook.SphericalSZChain

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZChain
-/
/- Source module: ProofsInTheBook.SphericalCyclicTriple -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain

namespace ProofsInTheBook.SphericalCyclicTriple









































end ProofsInTheBook.SphericalCyclicTriple

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCyclicTriple
-/
/- Source module: ProofsInTheBook.SphericalGnomonic -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple

namespace ProofsInTheBook.SphericalGnomonic






















































end ProofsInTheBook.SphericalGnomonic

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalGnomonic
-/
/- Source module: ProofsInTheBook.PlanarConvexDiag -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalArm ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalGnomonic

namespace ProofsInTheBook.PlanarConvexDiag



























end ProofsInTheBook.PlanarConvexDiag

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.SphericalSZStep -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag

namespace ProofsInTheBook.SphericalSZStep































end ProofsInTheBook.SphericalSZStep

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZStep
-/
/- Source module: ProofsInTheBook.SphericalHingeCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep

namespace ProofsInTheBook.SphericalHingeCut







































end ProofsInTheBook.SphericalHingeCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalHingeCut
-/
/- Source module: ProofsInTheBook.SphericalDiagCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut

namespace ProofsInTheBook.SphericalDiagCut

















































end ProofsInTheBook.SphericalDiagCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalDiagCut
-/
/- Source module: ProofsInTheBook.SphericalOpeningProcess -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut

namespace ProofsInTheBook.SphericalOpeningProcess

























































end ProofsInTheBook.SphericalOpeningProcess

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpeningProcess
-/
/- Source module: ProofsInTheBook.SphericalReachStuck -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess

namespace ProofsInTheBook.SphericalReachStuck





































end ProofsInTheBook.SphericalReachStuck

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalReachStuck
-/
/- Source module: ProofsInTheBook.SphericalAdmissibleSup -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck

namespace ProofsInTheBook.SphericalAdmissibleSup

































































end ProofsInTheBook.SphericalAdmissibleSup

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalAdmissibleSup
-/
/- Source module: ProofsInTheBook.SphericalArmClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup

namespace ProofsInTheBook.SphericalArmClose































































end ProofsInTheBook.SphericalArmClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmClose
-/
/- Source module: ProofsInTheBook.SphericalArmFinal -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose

namespace ProofsInTheBook.SphericalArmFinal























end ProofsInTheBook.SphericalArmFinal

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmFinal
-/
/- Source module: ProofsInTheBook.SphericalSZComplete -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose

namespace ProofsInTheBook.SphericalSZComplete













































end ProofsInTheBook.SphericalSZComplete

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZComplete
-/
/- Source module: ProofsInTheBook.SphericalStuckWitness -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete

namespace ProofsInTheBook.SphericalStuckWitness





















































end ProofsInTheBook.SphericalStuckWitness

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckWitness
-/
/- Source module: ProofsInTheBook.SphericalTerminalVis -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalStuckWitness

namespace ProofsInTheBook.SphericalTerminalVis































































end ProofsInTheBook.SphericalTerminalVis

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalTerminalVis
-/
/- Source module: ProofsInTheBook.SphericalArmUncond -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis

namespace ProofsInTheBook.SphericalArmUncond

















































end ProofsInTheBook.SphericalArmUncond

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmUncond
-/
/- Source module: ProofsInTheBook.SphericalMatchedCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond

namespace ProofsInTheBook.SphericalMatchedCut









































































































end ProofsInTheBook.SphericalMatchedCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalMatchedCut
-/
/- Source module: ProofsInTheBook.SphericalCornerStep -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut

namespace ProofsInTheBook.SphericalCornerStep















































end ProofsInTheBook.SphericalCornerStep

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCornerStep
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.SphericalConeMembership -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep

namespace ProofsInTheBook.SphericalConeMembership













































































end ProofsInTheBook.SphericalConeMembership

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalConeMembership
-/
/- Source module: ProofsInTheBook.SphericalArmDone -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership

namespace ProofsInTheBook.SphericalArmDone



















































end ProofsInTheBook.SphericalArmDone

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmDone
-/
/- Source module: ProofsInTheBook.SphericalArmFinish -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone

namespace ProofsInTheBook.SphericalArmFinish









































end ProofsInTheBook.SphericalArmFinish

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmFinish
-/
/- Source module: ProofsInTheBook.SphericalArmClose2 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish

namespace ProofsInTheBook.SphericalArmClose2















































end ProofsInTheBook.SphericalArmClose2

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmClose2
-/
/- Source module: ProofsInTheBook.SphericalStuckCollinear -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalArmClose2

namespace ProofsInTheBook.SphericalStuckCollinear















































end ProofsInTheBook.SphericalStuckCollinear

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckCollinear
-/
/- Source module: ProofsInTheBook.SphericalOpenedArmCore -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalArmClose2
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalOpenedArmCore



























end ProofsInTheBook.SphericalOpenedArmCore

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckCollinear
-/
/- Source module: ProofsInTheBook.SphericalSZInduction -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalTerminalVis
open ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalSZInduction

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































































































end ProofsInTheBook.SphericalSZInduction

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZInduction
-/
/- Source module: ProofsInTheBook.SphericalSZStepClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalStuckCollinear
open ProofsInTheBook.SphericalSZInduction

namespace ProofsInTheBook.SphericalSZStepClose

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















































end ProofsInTheBook.SphericalSZStepClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZStepClose
-/
/- Source module: ProofsInTheBook.SphericalSZFinal -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose

namespace ProofsInTheBook.SphericalSZFinal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

























































end ProofsInTheBook.SphericalSZFinal

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZFinal
-/
/- Source module: ProofsInTheBook.SphericalSZClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.SphericalSZClose

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.SphericalSZClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalCutTransport -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalCutTransport

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.SphericalCutTransport

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCutTransport
-/
/- Source module: ProofsInTheBook.ZinanFFCT -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport

namespace ProofsInTheBook.ZinanFFCT

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





























end ProofsInTheBook.ZinanFFCT

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT
-/
/- Source module: ProofsInTheBook.ZinanFFCT2 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT

namespace ProofsInTheBook.ZinanFFCT2

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




































































end ProofsInTheBook.ZinanFFCT2

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT2
-/
/- Source module: ProofsInTheBook.ZinanFFCT3 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2

namespace ProofsInTheBook.ZinanFFCT3

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT3

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT3
-/
/- Source module: ProofsInTheBook.ZinanFFCT4 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3

namespace ProofsInTheBook.ZinanFFCT4

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

































end ProofsInTheBook.ZinanFFCT4

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT4
-/
/- Source module: ProofsInTheBook.ZinanFFCT5 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT4

namespace ProofsInTheBook.ZinanFFCT5

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



















end ProofsInTheBook.ZinanFFCT5

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT5
-/
/- Source module: ProofsInTheBook.ZinanFFCT6 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT5

namespace ProofsInTheBook.ZinanFFCT6

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


























end ProofsInTheBook.ZinanFFCT6

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT6
-/
/- Source module: ProofsInTheBook.ZinanFFCT7 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT5
open ProofsInTheBook.ZinanFFCT6

namespace ProofsInTheBook.ZinanFFCT7

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT7

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT7
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.ZinanFFCT8 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT ProofsInTheBook.ZinanFFCT2 ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT4 ProofsInTheBook.ZinanFFCT5 ProofsInTheBook.ZinanFFCT6
open ProofsInTheBook.ZinanFFCT7

namespace ProofsInTheBook.ZinanFFCT8

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT8

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT8
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.ZinanFFCT9 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT8

namespace ProofsInTheBook.ZinanFFCT9

set_option maxHeartbeats 1600000
















































































end ProofsInTheBook.ZinanFFCT9

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT9
-/
/- Source module: ProofsInTheBook.ZinanFFCT10 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9

namespace ProofsInTheBook.ZinanFFCT10

set_option maxHeartbeats 1600000






















































end ProofsInTheBook.ZinanFFCT10








end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
-/
/- Source module: ProofsInTheBook.ZinanFFCT17 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT17

set_option maxHeartbeats 1600000















































































end ProofsInTheBook.ZinanFFCT17

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT17
-/
/- Source module: ProofsInTheBook.ZinanFFCT18 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT17

namespace ProofsInTheBook.ZinanFFCT18

set_option maxHeartbeats 1600000




















































end ProofsInTheBook.ZinanFFCT18

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckWitness
import ProofsInTheBook.SphericalCutTransport
-/
/- Source module: ProofsInTheBook.SphericalStuckGeneral -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalStuckWitness ProofsInTheBook.SphericalTerminalVis
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport

namespace ProofsInTheBook.SphericalStuckGeneral





































end ProofsInTheBook.SphericalStuckGeneral

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.SphericalLastCornerStuck -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose ProofsInTheBook.SphericalStuckGeneral

namespace ProofsInTheBook.SphericalLastCornerStuck





























end ProofsInTheBook.SphericalLastCornerStuck

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT18
import ProofsInTheBook.SphericalLastCornerStuck
-/
/- Source module: ProofsInTheBook.ZinanFFCT19 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT19

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


















































end ProofsInTheBook.ZinanFFCT19

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalMonitoredSup -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalMonitoredSup

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































































end ProofsInTheBook.SphericalMonitoredSup

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalSpliceTransport -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalSpliceTransport

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000























end ProofsInTheBook.SphericalSpliceTransport

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalRotation
import ProofsInTheBook.SphericalCyclicTriple
-/
/- Source module: ProofsInTheBook.SphericalCongruence -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCyclicTriple

namespace ProofsInTheBook.SphericalCongruence

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























































end ProofsInTheBook.SphericalCongruence

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalSpliceTransport
import ProofsInTheBook.SphericalCongruence
-/
/- Source module: ProofsInTheBook.SphericalArmAssembly -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCongruence

namespace ProofsInTheBook.SphericalArmAssembly

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.SphericalArmAssembly

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmAssembly
-/
/- Source module: ProofsInTheBook.SphericalOpeningOutcome -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalArmAssembly

namespace ProofsInTheBook.SphericalOpeningOutcome

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























end ProofsInTheBook.SphericalOpeningOutcome


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT19
import ProofsInTheBook.SphericalSZClose
import ProofsInTheBook.SphericalOpeningOutcome
import ProofsInTheBook.ZinanFFCT18
-/
/- Source module: ProofsInTheBook.ZinanFFCT20 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT20




















end ProofsInTheBook.ZinanFFCT20

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
-/
/- Source module: ProofsInTheBook.ZinanFFCT12 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT12

set_option maxHeartbeats 1600000



























end ProofsInTheBook.ZinanFFCT12

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT20
import ProofsInTheBook.ZinanFFCT12
-/
/- Source module: ProofsInTheBook.ZinanFFCT21 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT21

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT21

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT21
-/
/- Source module: ProofsInTheBook.ZinanFFCT22 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21

namespace ProofsInTheBook.ZinanFFCT22

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















































end ProofsInTheBook.ZinanFFCT22

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT22
-/
/- Source module: ProofsInTheBook.ZinanFFCT23 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21

namespace ProofsInTheBook.ZinanFFCT23

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT23

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT23
-/
/- Source module: ProofsInTheBook.ZinanFFCT24 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23

namespace ProofsInTheBook.ZinanFFCT24

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






















































end ProofsInTheBook.ZinanFFCT24

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT24
-/
/- Source module: ProofsInTheBook.ZinanFFCT25 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24

namespace ProofsInTheBook.ZinanFFCT25

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000













































end ProofsInTheBook.ZinanFFCT25

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.SphericalCore
-/
/- Source module: ProofsInTheBook.ZinanFFCT26 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT26

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000











































end ProofsInTheBook.ZinanFFCT26

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT26
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.ZinanFFCT27 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalSZ

namespace ProofsInTheBook.ZinanFFCT27

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT27

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT27
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalOpeningOutcome
-/
/- Source module: ProofsInTheBook.ZinanFFCT28 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.SphericalStuckGeneral ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.ZinanFFCT28

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT28

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpeningOutcome
-/
/- Source module: ProofsInTheBook.SphericalOpeningGlue -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome

namespace ProofsInTheBook.SphericalOpeningGlue

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

































end ProofsInTheBook.SphericalOpeningGlue

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT28
import ProofsInTheBook.SphericalOpeningGlue
-/
/- Source module: ProofsInTheBook.ZinanFFCT30 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalOpeningGlue

namespace ProofsInTheBook.ZinanFFCT30

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

























end ProofsInTheBook.ZinanFFCT30

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT30
import ProofsInTheBook.ZinanFFCT22
-/
/- Source module: ProofsInTheBook.ZinanFFCT33 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30

namespace ProofsInTheBook.ZinanFFCT33

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

































end ProofsInTheBook.ZinanFFCT33
end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT33
-/
/- Source module: ProofsInTheBook.ZinanFFCT34 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30 ProofsInTheBook.ZinanFFCT33

namespace ProofsInTheBook.ZinanFFCT34

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT34

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT34
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
-/
/- Source module: ProofsInTheBook.ZinanFFCT36 -/
section
set_option autoImplicit true


noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT33 ProofsInTheBook.ZinanFFCT34

namespace ProofsInTheBook.ZinanFFCT36

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
























end ProofsInTheBook.ZinanFFCT36
end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT36
-/
/- Source module: ProofsInTheBook.ZinanFFCT44 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36

namespace ProofsInTheBook.ZinanFFCT44

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT44

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT20
import ProofsInTheBook.ZinanFFCT3
import ProofsInTheBook.SphericalOpeningGlue
-/
/- Source module: ProofsInTheBook.ZinanFFCT37 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT3

namespace ProofsInTheBook.ZinanFFCT37

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































































end ProofsInTheBook.ZinanFFCT37

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT37
import ProofsInTheBook.ZinanFFCT36
-/
/- Source module: ProofsInTheBook.ZinanFFCT38 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37

namespace ProofsInTheBook.ZinanFFCT38

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



















































end ProofsInTheBook.ZinanFFCT38






end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT38
-/
/- Source module: ProofsInTheBook.ZinanFFCT39 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38

namespace ProofsInTheBook.ZinanFFCT39

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000













































end ProofsInTheBook.ZinanFFCT39

-- Brick 1 (positive content + assembly + audit)





-- Brick 2 (audit + positive content)




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT39
-/
/- Source module: ProofsInTheBook.ZinanFFCT40 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38
open ProofsInTheBook.ZinanFFCT39

namespace ProofsInTheBook.ZinanFFCT40

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000























































end ProofsInTheBook.ZinanFFCT40

-- §1 the any-h assembler

-- §3 the pure-hemi strict certificate + repaired stuck outcome + repaired clause (iii)



-- §3 the corrected outcome + repaired headline



-- refutation-resistance witnesses


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT40
-/
/- Source module: ProofsInTheBook.ZinanFFCT41 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38
open ProofsInTheBook.ZinanFFCT39
open ProofsInTheBook.ZinanFFCT40

namespace ProofsInTheBook.ZinanFFCT41

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































































end ProofsInTheBook.ZinanFFCT41

-- §1 the WB family + W-admissibility bridge

-- §2 the base sinusoid

-- §3 the cap by admissibility (the central new content)


-- §5 the WB trichotomy

-- §6/§7 the clauses at the WB sup



-- §8/§9 the base-capped outcome + headline (GlueWBaseCap discharged)


-- refutation-resistance witness


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT41
-/
/- Source module: ProofsInTheBook.ZinanFFCT42 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT41

namespace ProofsInTheBook.ZinanFFCT42

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT42

-- §1 the algebra/index micro-lemmas


-- §2 base-stuck = opened diagonal

-- §3 Brick 1 (the cyclic-identity bridge) + the vanishing-support payload


-- §4 the residual DISCHARGED + the base-stuck-free headline


-- non-vacuity guards


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT42
-/
/- Source module: ProofsInTheBook.ZinanFFCT45 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT41
open ProofsInTheBook.ZinanFFCT42

namespace ProofsInTheBook.ZinanFFCT45

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.ZinanFFCT45

-- §1 the WBS family + closure facts





-- §2 init admissibility

-- §3 deficit bound + base cap



-- §4 the trichotomy + clauses



-- §5 Brick 7: the FFCT42 base-stuck port DISCHARGED



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT42
-/
/- Source module: ProofsInTheBook.ZinanFFCT43 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.ZinanFFCT39
open ProofsInTheBook.ZinanFFCT41
open ProofsInTheBook.ZinanFFCT42

namespace ProofsInTheBook.ZinanFFCT43

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT43

-- §1 endpoint positivity

-- §2 closing edge distinct at the WB supremum

-- §3 the residual DISCHARGED + the closing-edge-free headline


-- non-vacuity guards


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT44
import ProofsInTheBook.ZinanFFCT45
import ProofsInTheBook.ZinanFFCT43
-/
/- Source module: ProofsInTheBook.ZinanFFCT46 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT34
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT40
open ProofsInTheBook.ZinanFFCT42
open ProofsInTheBook.ZinanFFCT43
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT45

namespace ProofsInTheBook.ZinanFFCT46

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















































end ProofsInTheBook.ZinanFFCT46

-- §1 the margins-free open-hemisphere production (THE keystone mechanism)

-- §2 brick 4

-- §2′ the opened side / joint geometry



-- §3 bricks 5–6


-- §4 brick 8

-- §5 brick 9 + non-vacuity



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT46
-/
/- Source module: ProofsInTheBook.ZinanFFCT47 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT42
open ProofsInTheBook.ZinanFFCT43
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46

namespace ProofsInTheBook.ZinanFFCT47

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























































end ProofsInTheBook.ZinanFFCT47

-- §1 the open-chain collapse kernel (3 ≤ n)

-- §2 the wrap-edge-free open-hemisphere production

-- §3 wrap ShortArc from the hemisphere

-- §4 the residual discharged


-- §5 the wrap-free headline



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT47
import ProofsInTheBook.ZinanFFCT28
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.ZinanFFCT49 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT28
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47

namespace ProofsInTheBook.ZinanFFCT49

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT49

-- §0 the opened arm

-- §2 discharged pieces



-- §4 the bridge

-- §5 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT49
import ProofsInTheBook.ZinanFFCT23
-/
/- Source module: ProofsInTheBook.ZinanFFCT52 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49

namespace ProofsInTheBook.ZinanFFCT52

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































































end ProofsInTheBook.ZinanFFCT52

-- §1 component 2


-- §2 reversal infra




-- §3 orientation normalization

-- §4 interval convexity


-- §5 assembly


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT19
import ProofsInTheBook.ZinanFFCT46
import ProofsInTheBook.ZinanFFCT47
-/
/- Source module: ProofsInTheBook.ZinanFFCT48 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47

namespace ProofsInTheBook.ZinanFFCT48

set_option maxHeartbeats 1600000



























end ProofsInTheBook.ZinanFFCT48




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.ZinanFFCT48
-/
/- Source module: ProofsInTheBook.ZinanFFCT53 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT25

namespace ProofsInTheBook.ZinanFFCT53

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


















































end ProofsInTheBook.ZinanFFCT53

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT52
import ProofsInTheBook.ZinanFFCT53
-/
/- Source module: ProofsInTheBook.ZinanFFCT54 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT52 ProofsInTheBook.ZinanFFCT53

namespace ProofsInTheBook.ZinanFFCT54

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















































































end ProofsInTheBook.ZinanFFCT54

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT54
-/
/- Source module: ProofsInTheBook.ZinanFFCT63 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54

namespace ProofsInTheBook.ZinanFFCT63

set_option maxHeartbeats 1600000




















































end ProofsInTheBook.ZinanFFCT63

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT28
-/
/- Source module: ProofsInTheBook.ZinanFFCT29 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT10 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.ZinanFFCT28

namespace ProofsInTheBook.ZinanFFCT29

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT29

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT29
-/
/- Source module: ProofsInTheBook.ZinanFFCT31 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29

namespace ProofsInTheBook.ZinanFFCT31

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
























































end ProofsInTheBook.ZinanFFCT31

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT31
-/
/- Source module: ProofsInTheBook.ZinanFFCT32 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29
open ProofsInTheBook.ZinanFFCT31

namespace ProofsInTheBook.ZinanFFCT32

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















































end ProofsInTheBook.ZinanFFCT32

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT49
import ProofsInTheBook.ZinanFFCT32
-/
/- Source module: ProofsInTheBook.ZinanFFCT51 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29 ProofsInTheBook.ZinanFFCT31
open ProofsInTheBook.ZinanFFCT32
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49

namespace ProofsInTheBook.ZinanFFCT51

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





























end ProofsInTheBook.ZinanFFCT51

-- §1 the sharp residue

-- §2 the corner sign verification

-- §3 the main near-side line


-- §4 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT51
-/
/- Source module: ProofsInTheBook.ZinanFFCT55 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.ZinanFFCT29
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT51

namespace ProofsInTheBook.ZinanFFCT55

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT55

-- §R1/R2 the constant-binding contradiction at the WBS family


-- §δ*=0 edge

-- §R3 slot normalization

-- §R4 the derivative + the sign finding



-- §R4′ the forced collapse

-- §5 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT21
import ProofsInTheBook.ZinanFFCT55
-/
/- Source module: ProofsInTheBook.ZinanFFCT56 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT55

namespace ProofsInTheBook.ZinanFFCT56

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT56

-- §A the coefficient bricks


-- §B the master mid-fold kill


-- §C the WBS axis-edge elimination

-- §D the honest dispatch + residue

-- §E the consequence wiring

-- §F non-vacuity guards




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT48
import ProofsInTheBook.ZinanFFCT56
-/
/- Source module: ProofsInTheBook.ZinanFFCT57 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT56

namespace ProofsInTheBook.ZinanFFCT57

set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT57









end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
import ProofsInTheBook.SphericalSpliceTransport
import ProofsInTheBook.ZinanFFCT48
import ProofsInTheBook.ZinanFFCT57
-/
/- Source module: ProofsInTheBook.ZinanFFCT58 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT57

namespace ProofsInTheBook.ZinanFFCT58

set_option maxHeartbeats 1600000
set_option linter.unnecessarySeqFocus false























































































end ProofsInTheBook.ZinanFFCT58







end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT58
-/
/- Source module: ProofsInTheBook.ZinanFFCT59 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58

namespace ProofsInTheBook.ZinanFFCT59

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT59









end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT54
import ProofsInTheBook.ZinanFFCT59
-/
/- Source module: ProofsInTheBook.ZinanFFCT60 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59

namespace ProofsInTheBook.ZinanFFCT60

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


























end ProofsInTheBook.ZinanFFCT60

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT60
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.ZinanFFCT61 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT60

namespace ProofsInTheBook.ZinanFFCT61

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































































































end ProofsInTheBook.ZinanFFCT61

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT61
-/
/- Source module: ProofsInTheBook.ZinanFFCT62 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT61

namespace ProofsInTheBook.ZinanFFCT62

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT62

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT62
-/
/- Source module: ProofsInTheBook.ZinanFFCT64 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62

namespace ProofsInTheBook.ZinanFFCT64

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT64

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT63
import ProofsInTheBook.ZinanFFCT64
-/
/- Source module: ProofsInTheBook.ZinanFFCT65 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62
open ProofsInTheBook.ZinanFFCT63
open ProofsInTheBook.ZinanFFCT64

namespace ProofsInTheBook.ZinanFFCT65

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.ZinanFFCT65

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT65
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.ZinanFFCT66 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT63
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65

namespace ProofsInTheBook.ZinanFFCT66

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000












































end ProofsInTheBook.ZinanFFCT66

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT66
-/
/- Source module: ProofsInTheBook.ZinanFFCT67 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66

namespace ProofsInTheBook.ZinanFFCT67

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















end ProofsInTheBook.ZinanFFCT67

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT67
import ProofsInTheBook.ZinanFFCT26
-/
/- Source module: ProofsInTheBook.ZinanFFCT68 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT67

namespace ProofsInTheBook.ZinanFFCT68

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT68

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT68
-/
/- Source module: ProofsInTheBook.ZinanFFCT69 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT67
open ProofsInTheBook.ZinanFFCT68

namespace ProofsInTheBook.ZinanFFCT69

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




































end ProofsInTheBook.ZinanFFCT69

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT69
import ProofsInTheBook.ZinanFFCT32
-/
/- Source module: ProofsInTheBook.ZinanFFCT70 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT31
open ProofsInTheBook.ZinanFFCT32
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69

namespace ProofsInTheBook.ZinanFFCT70

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




























end ProofsInTheBook.ZinanFFCT70

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT70
-/
/- Source module: ProofsInTheBook.ZinanFFCT71 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70

namespace ProofsInTheBook.ZinanFFCT71

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






























end ProofsInTheBook.ZinanFFCT71

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT71
-/
/- Source module: ProofsInTheBook.ZinanFFCT72 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71

namespace ProofsInTheBook.ZinanFFCT72

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000








































end ProofsInTheBook.ZinanFFCT72

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT72
-/
/- Source module: ProofsInTheBook.ZinanFFCT73 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT72

namespace ProofsInTheBook.ZinanFFCT73

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000










































end ProofsInTheBook.ZinanFFCT73

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT73
-/
/- Source module: ProofsInTheBook.ZinanFFCT74 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT73

namespace ProofsInTheBook.ZinanFFCT74

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































end ProofsInTheBook.ZinanFFCT74

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT74
-/
/- Source module: ProofsInTheBook.ZinanFFCT75 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74

namespace ProofsInTheBook.ZinanFFCT75

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






















end ProofsInTheBook.ZinanFFCT75

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT75
import ProofsInTheBook.ZinanFFCT44
-/
/- Source module: ProofsInTheBook.ZinanFFCT76 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75

namespace ProofsInTheBook.ZinanFFCT76

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT76

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT76
-/
/- Source module: ProofsInTheBook.ZinanFFCT77 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76

namespace ProofsInTheBook.ZinanFFCT77

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































































end ProofsInTheBook.ZinanFFCT77

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT77
-/
/- Source module: ProofsInTheBook.ZinanFFCT78 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77

namespace ProofsInTheBook.ZinanFFCT78

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















end ProofsInTheBook.ZinanFFCT78

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT78
-/
/- Source module: ProofsInTheBook.ZinanFFCT79 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78

namespace ProofsInTheBook.ZinanFFCT79

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT79

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT79
-/
/- Source module: ProofsInTheBook.ZinanFFCT80 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79

namespace ProofsInTheBook.ZinanFFCT80

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































end ProofsInTheBook.ZinanFFCT80

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT80
-/
/- Source module: ProofsInTheBook.ZinanFFCT81 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80

namespace ProofsInTheBook.ZinanFFCT81

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000










































end ProofsInTheBook.ZinanFFCT81

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT81
-/
/- Source module: ProofsInTheBook.ZinanFFCT82 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81

namespace ProofsInTheBook.ZinanFFCT82

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































end ProofsInTheBook.ZinanFFCT82

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT82
-/
/- Source module: ProofsInTheBook.ZinanFFCT83 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82

namespace ProofsInTheBook.ZinanFFCT83

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT83

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT83
-/
/- Source module: ProofsInTheBook.ZinanFFCT84 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83

namespace ProofsInTheBook.ZinanFFCT84

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















end ProofsInTheBook.ZinanFFCT84

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT84
-/
/- Source module: ProofsInTheBook.ZinanFFCT85 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84

namespace ProofsInTheBook.ZinanFFCT85

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000









































end ProofsInTheBook.ZinanFFCT85

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT85
-/
/- Source module: ProofsInTheBook.ZinanFFCT86 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84
open ProofsInTheBook.ZinanFFCT85

namespace ProofsInTheBook.ZinanFFCT86

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000








































end ProofsInTheBook.ZinanFFCT86

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT86
-/
/- Source module: ProofsInTheBook.ZinanFFCT100 -/
section
set_option autoImplicit true




open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86

namespace ProofsInTheBook.ZinanFFCT100







end ProofsInTheBook.ZinanFFCT100




end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT100
-/
/- Source module: ProofsInTheBook.ZinanFFCT111 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84
open ProofsInTheBook.ZinanFFCT85
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT100

namespace ProofsInTheBook.ZinanFFCT111

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000













































































end ProofsInTheBook.ZinanFFCT111

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalReachStuck
import ProofsInTheBook.SphericalSZFinal
import ProofsInTheBook.SphericalSZClose
import ProofsInTheBook.ZinanFFCT111
-/
/- Source module: ProofsInTheBook.ZinanFFCT113 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalHinge ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalFinish ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.ZinanFFCT78 ProofsInTheBook.ZinanFFCT111

namespace ProofsInTheBook.ZinanFFCT113

set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT113

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpenedArmCore
import ProofsInTheBook.ZinanFFCT111
import ProofsInTheBook.ZinanFFCT113
-/
/- Source module: ProofsInTheBook.ZinanFFCT112 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ZinanFFCT112

open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalOpenedArmCore












end ProofsInTheBook.ZinanFFCT112




end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.ZinanFFCT112
-/
/- Source module: ProofsInTheBook.Chapter13 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Chapter13

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm



open EdgeSign























namespace StrictTriangleSigns





end StrictTriangleSigns

















namespace CauchyArmOpeningObstruction



end CauchyArmOpeningObstruction



namespace CauchyArmClosingObstruction



end CauchyArmClosingObstruction



namespace CauchyArmFixedChordObstruction



end CauchyArmFixedChordObstruction

















namespace CauchyArmVertex







end CauchyArmVertex



namespace CauchyRigidityCertificate







end CauchyRigidityCertificate











end ProofsInTheBook.Chapter13

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.Chapter13
-/
/- Source module: ProofsInTheBook.Ch13CyclicSigns -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13CyclicSigns

open ProofsInTheBook.Chapter13
open EdgeSign



variable {α : Type*} [DecidableEq α]

























end ProofsInTheBook.Ch13CyclicSigns

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
-/
/- Source module: ProofsInTheBook.Ch13MarkedSphere -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13MarkedSphere

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns

variable {D : Type*} [Fintype D] [DecidableEq D]





























































































end ProofsInTheBook.Ch13MarkedSphere

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
-/
/- Source module: ProofsInTheBook.Ch13MarkedReduction -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13MarkedReduction

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open EdgeSign
open Equiv Equiv.Perm



section ListBridge

variable {α : Type*} [DecidableEq α]







end ListBridge



section OrbitBridge

variable {α : Type*} [DecidableEq α] [Fintype α] {β : Type*} [DecidableEq β]









end OrbitBridge



section StrictBridge

variable {D : Type*} [Fintype D] [DecidableEq D]











end StrictBridge



section ActiveComponent

variable {D : Type*} [Fintype D] [DecidableEq D]













end ActiveComponent



section Obstruction
































end Obstruction

end ProofsInTheBook.Ch13MarkedReduction

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
-/
/- Source module: ProofsInTheBook.Ch13ActiveComponent -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ActiveComponent

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open EdgeSign

variable {D : Type*} [Fintype D] [DecidableEq D]

















open ProofsInTheBook.SubmapPlanar













  -- unreachable on active darts























end ProofsInTheBook.Ch13ActiveComponent

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
import ProofsInTheBook.Ch13ActiveComponent
-/
/- Source module: ProofsInTheBook.Ch13FlipTransport -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13FlipTransport

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open ProofsInTheBook.Ch13ActiveComponent
open ProofsInTheBook.SubmapPlanar
open EdgeSign
open Equiv Equiv.Perm

variable {D : Type*} [Fintype D] [DecidableEq D]



open ProofsInTheBook -- for DeleteSet.firstOutside via Equiv.Perm namespace









































































end ProofsInTheBook.Ch13FlipTransport

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
import ProofsInTheBook.Ch13ActiveComponent
import ProofsInTheBook.Ch13FlipTransport
import ProofsInTheBook.PlanarMapNearTriangulation
-/
/- Source module: ProofsInTheBook.Ch13ComponentClose -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ComponentClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open ProofsInTheBook.Ch13ActiveComponent
open ProofsInTheBook.Ch13FlipTransport
open ProofsInTheBook.SubmapPlanar
open EdgeSign
open Equiv Equiv.Perm

variable {D : Type*} [Fintype D] [DecidableEq D]

















































variable (M : CombMap D) (es : D → EdgeSign)











































end ProofsInTheBook.Ch13ComponentClose

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13ComponentClose
import ProofsInTheBook.ChordFaceCount
import ProofsInTheBook.PlanarMapSimple
-/
/- Source module: ProofsInTheBook.FaceDiagonalSurgery -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap.CombMap

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordSideRecon

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]



namespace FaceDiagonalChoice

variable {M : CombMap D} (c : FaceDiagonalChoice M)



















end FaceDiagonalChoice









namespace FaceDiagonal

variable (M : CombMap D) (c : FaceDiagonalChoice M)



































































end FaceDiagonal





namespace FaceDiagonalInsertion



end FaceDiagonalInsertion

end ProofsInTheBook.PlanarMap.CombMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapChordSplitData
import ProofsInTheBook.PlanarMapCutCap
-/
/- Source module: ProofsInTheBook.ZinanCh35StarRotation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

















variable {M : CombMap D} (hNT : NearTriangulation M)













































end CombMap

end ProofsInTheBook.PlanarMap

-- Axiom audit for the main brick results (expect: propext, Classical.choice, Quot.sound).









end

/- Original source header (imports hoisted):
import ProofsInTheBook.SubmapPlanar
-/
/- Source module: ProofsInTheBook.ChordSideClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSideClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.SubmapPlanar

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



section RawPrimitives

variable (M)

open scoped Classical







end RawPrimitives













section RawConnected

























end RawConnected











end ProofsInTheBook.ChordSideClose







end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideClose
import ProofsInTheBook.ChordSplitNT
-/
/- Source module: ProofsInTheBook.ChordReconClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordReconClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordSideClose

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}





































end ProofsInTheBook.ChordReconClose










end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordReconClose
import ProofsInTheBook.ChordDisk
-/
/- Source module: ProofsInTheBook.ChordSideNT -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSideNT

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ChordReconClose

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

























end ProofsInTheBook.ChordSideNT











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideNT
import ProofsInTheBook.ChordSplitNT
-/
/- Source module: ProofsInTheBook.ChordSplitFinal -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSplitFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordDisk

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}



























end ProofsInTheBook.ChordSplitFinal



namespace ProofsInTheBook.ChordSplitFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT

variable {α : Type u} [DecidableEq α]

/-- **The Thomassen five-list-coloring induction, in the unified chord-recursive framing.**

Given the chord-recursive dichotomy `O` (the single isolated discrete Jordan–Schoenflies
residue: each near-triangulation with the Thomassen lists yields either a chord recursion datum
— two smaller side near-triangulations in the generic `ChordSideReconstruction` shape — or a
chordless oracle datum), every near-triangulation with the Thomassen list hypotheses is
list-colorable.  This is `ChordSplitNT.nearTriangulation_listColorable_chordRecursive`; recorded
here as the headline of the unified framing.  The chord branch now *produces* its colorings by
recursing on the side reconstructions of Section 2 — no colorings consumed, no free-anchor
`sideMap₁` detour. -/
theorem nearTriangulation_listColorable_unified (O : ChordRecursiveDichotomy α)
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
    (cp cq : α) (h : ThomassenLists hNT p q L cp cq) :
    ListColorable M.toSimpleGraph L :=
  nearTriangulation_listColorable_chordRecursive O hNT p q L cp cq h

/-- **Five-colorability of a near-triangulation, unified framing.**

Over any colour type with `5 ≤ Fintype.card α`, every near-triangulation is five-colorable,
given the chord-recursive dichotomy `O` (the isolated Jordan residue).  This mirrors
`ThomassenInduction.nearTriangulation_five_colorable` but in the unified chord-recursive
framing — the chord case recurses on the generic-shape side reconstructions rather than
consuming oracle colorings.  We thread through the `L' ⊆ L` forcing exactly as the upstream
corollary does. -/
theorem nearTriangulation_five_colorable_unified
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    {α : Type u} [Fintype α] [DecidableEq α]
    (hNT : NearTriangulation M) (hα : 5 ≤ Fintype.card α)
    (Ofun : ∀ p q : M.Vertex, ∀ cp cq : α, ChordRecursiveDichotomy α) :
    ListColorable M.toSimpleGraph (fun _ : M.Vertex => (Finset.univ : Finset α)) := by
  classical
  -- the uniform list is constant `Finset.univ`, size ≥ 5.
  have hL : ∀ x : M.Vertex, 5 ≤ ((fun _ : M.Vertex => (Finset.univ : Finset α)) x).card := by
    intro x; rw [Finset.card_univ]; exact hα
  -- pick a precolorable boundary edge (the upstream existence lemma).
  obtain ⟨p, q, hpq, hpb, hqb, hedge, hadj⟩ :=
    ProofsInTheBook.ThomassenInduction.exists_boundary_edge hNT
  set L : M.Vertex → Finset α := fun _ => (Finset.univ : Finset α) with hLdef
  -- choose two distinct precolors.
  have hpne : (L p).Nonempty := Finset.card_pos.mp (by have := hL p; omega)
  obtain ⟨cp, hcp⟩ := hpne
  have hqbig : (L q \ {cp}).Nonempty := by
    rw [← Finset.card_pos]
    have h1 : ((L q) \ {cp}).card ≥ (L q).card - ({cp} : Finset α).card :=
      by have := Finset.le_card_sdiff ({cp} : Finset α) (L q); omega
    have := hL q
    simp only [Finset.card_singleton] at h1
    omega
  obtain ⟨cq, hcq⟩ := hqbig
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hcq
  obtain ⟨hcqL, hcqne⟩ := hcq
  -- the forced lists.
  set L' : M.Vertex → Finset α :=
    fun w => if w = p then {cp} else if w = q then {cq} else L w with hL'
  have hLp : L' p = {cp} := by simp only [hL', if_pos rfl]
  have hLq : L' q = {cq} := by
    have : (q : M.Vertex) ≠ p := Ne.symm hpq
    simp [hL', this]
  have hLo : ∀ w : M.Vertex, w ≠ p → w ≠ q → L' w = L w := by
    intro w hwp hwq; simp only [hL', if_neg hwp, if_neg hwq]
  have hL'sub : ∀ w, L' w ⊆ L w := by
    intro w
    by_cases hwp : w = p
    · subst hwp; rw [hLp]; intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact hcp
    · by_cases hwq : w = q
      · subst hwq; rw [hLq]; intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact hcqL
      · rw [hLo w hwp hwq]
  -- `L'` satisfies the Thomassen list hypotheses.
  have htl : ThomassenLists hNT p q L' cp cq := by
    refine ⟨hpb, hqb, hedge, Ne.symm hcqne, hLp, hLq, ?_, ?_⟩
    · intro w _ hwp hwq; rw [hLo w hwp hwq]; have := hL w; omega
    · intro w hbnd
      by_cases hwp : w = p
      · subst hwp; exact absurd hpb hbnd
      · by_cases hwq : w = q
        · subst hwq; exact absurd hqb hbnd
        · rw [hLo w hwp hwq]; exact hL w
  -- apply the unified theorem with the dichotomy for `L'`, then lift to `L`.
  have hcolor : ListColorable M.toSimpleGraph L' :=
    nearTriangulation_listColorable_unified (Ofun p q cp cq) hNT p q L' cp cq htl
  exact hcolor.mono_lists hL'sub

end ProofsInTheBook.ChordSplitFinal












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideNT
-/
/- Source module: ProofsInTheBook.ChordContiguous -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordContiguous

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSideNT

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



































end ProofsInTheBook.ChordContiguous













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordContiguous
import ProofsInTheBook.ChordFaceCount
-/
/- Source module: ProofsInTheBook.ChordInnerTri -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordInnerTri

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]







section Splice

variable (β ρ : Equiv.Perm K) {a₀ a₁ : K}











end Splice



section Transfer

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)







end Transfer



section MTransfer

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

























end MTransfer

open ProofsInTheBook.ChordContiguous

section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

















end Discharge

end ProofsInTheBook.ChordInnerTri















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordInnerTri
-/
/- Source module: ProofsInTheBook.ChordFaceClass -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceClass

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



































end ProofsInTheBook.ChordFaceClass













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordFaceClass
-/
/- Source module: ProofsInTheBook.ChordBoundaryOrbit -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordBoundaryOrbit

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous
open ProofsInTheBook.ChordFaceClass

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section Trace

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)









end Trace



section Membership

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)







end Membership



















section Untouched

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)



end Untouched



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}





















end Discharge

end ProofsInTheBook.ChordBoundaryOrbit



















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordBoundaryOrbit
-/
/- Source module: ProofsInTheBook.ChordFaceFinal -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section Formula

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)













end Formula



section Consequences

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

include hne







end Consequences



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

































end Discharge

end ProofsInTheBook.ChordFaceFinal

















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordFaceFinal
-/
/- Source module: ProofsInTheBook.ChordAnchor -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordAnchor

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal

universe u



section TwoCycle

variable {K : Type u} [DecidableEq K]



variable [Fintype K]





end TwoCycle



section Card

variable {K : Type u} [Fintype K] [DecidableEq K]



end Card



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}































end Discharge

end ProofsInTheBook.ChordAnchor














end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordAnchor
-/
/- Source module: ProofsInTheBook.ChordAnchorInst -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordAnchorInst

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor

universe u



section Algebra

variable {K : Type u} [Fintype K] [DecidableEq K]





end Algebra



section KeptPhi

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}





end KeptPhi



section Residue

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

















end Residue

end ProofsInTheBook.ChordAnchorInst













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordAnchorInst
-/
/- Source module: ProofsInTheBook.ChordBigonWrap -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace ProofsInTheBook.ChordBigonWrap

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}































end ProofsInTheBook.ChordBigonWrap













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordBigonWrap
-/
/- Source module: ProofsInTheBook.ChordSigmaContig -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace ProofsInTheBook.ChordSigmaContig

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordBigonWrap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}









































end ProofsInTheBook.ChordSigmaContig

















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSigmaContig
-/
/- Source module: ProofsInTheBook.ZinanCh35SideAnchors -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35SideAnchors

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}































end ProofsInTheBook.ZinanCh35SideAnchors













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35SideAnchors
-/
/- Source module: ProofsInTheBook.ZinanCh35Hclass -/
section
set_option autoImplicit true


/-!
# The Chapter 35 chord-side `hclass` gluing bricks (the `ContiguousInterval` master glue)

`ZinanCh35SideAnchors.lean` pinned the **canonical** chord-cap anchors `a₀, a₁` of side 1 and
proved, UNCONDITIONALLY, the post-splice `tracePhi` 2-cycle on the two kept `face₁` darts
(`side₁Anchors_trace12`/`trace21`).  This file assembles those anchor facts, together with the
explicit-trace orbit machinery of `ChordBoundaryOrbit` and the correct-anchor structure of
`ChordAnchor`, into the master **per-face classifier** consumed by
`ChordAnchor.contiguousInterval_of_correctAnchor`:

> for every non-outer side face `g`, EITHER `g` has a splice-untouched, side-`₁`,
> non-`face₁` kept-`inl` representative, OR `g` carries a `CorrectAnchorTwoCycle` datum.

and then feeds it into the final `ContiguousInterval` assembler.

## Bricks (design §8 order)

1.  Notation block (`β ρ a₀ a₁ hne S τ`).
2.  `side₁_trace_beta_a0_to_face₁Dart₁` — `τ (β a₀) = face₁Dart₁ data`
    (`tracePhi_b0` + `sideSigma₁_side₁Anchor₁`).
3.  `side₁_chord0_face_eq_face₁_canonical` — `S.dartFace (inr 0) = S.dartFace (inl face₁Dart₁)`
    (`chordDart_face_eq_b0` + `sideFace_inl_eq_iff_tracePhi` via brick 2).
4.  `Side₁OuterTraceData` — the INPUT bundle (outer face + its boundary cycle, the two chord/face
    incidence facts, and the inner-rep avoidance residue).
5.  `side₁Anchors_oneFresh_canonical` — the one-fresh indicator `= 1`.
6.  `side₁_correctAnchor_face₁_canonical` — the `CorrectAnchorTwoCycle` datum for the touched
    `face₁` side face (`correctAnchorTwoCycle_ofFace₁` + bricks 5 & landed trace12/trace21).
7.  `side1_hclass_canonical` — the MASTER per-face classifier (face₁ branch transports brick 6
    across the face equality; no-hit branch uses `spliceUntouched_of_face_ne_chordOrbits`).
8.  `contiguousInterval_canonical` — feed brick 7 into `contiguousInterval_of_correctAnchor`.

**Input-bundle addition (reported per the design's license).**  The design's
`Side₁OuterTraceData` lists `outerFace, outerCycle, outer_simple, outer_len, chord1_is_outer,
face₁_not_outer`.  The no-hit branch's `M.dartFace k.1 ∈ side₁` (`hside`) obligation is the
genuine geometric residue "the side outer face is exactly the `M`-outer-arc orbit, so every other
face's rep avoids the `M`-outer face" — NOT derivable from the abstract `CombMap`.  Rather than
weaken, we carry it as the repo-native field `inner_reps :
ChordBoundaryOrbit.InnerRepsAvoidBoundary …` (which packages exactly "each non-outer side face has
a kept-`inl` rep with `M`-face `≠ M`-outer and `≠ face₁`"), as the design explicitly permits.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35Hclass

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

































end ProofsInTheBook.ZinanCh35Hclass










end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Hclass
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterTrace -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterTrace

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35Hclass

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u



section PermSplit

variable {D : Type*} [Fintype D] [DecidableEq D]





end PermSplit



section Canonical

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}













end Canonical

end ProofsInTheBook.ZinanCh35OuterTrace









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35OuterTrace
-/
/- Source module: ProofsInTheBook.ZinanCh35Iota -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Iota

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]































end ProofsInTheBook.ZinanCh35Iota









end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapSigma2 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}



                 -- c_i^- ↦ p_i

             -- c_i^- ↦ ℓ_i^- = σ⁻¹ q_i























































end SimplePrimalCycle











end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapF
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapFCore -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount























end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma2
import ProofsInTheBook.PlanarMapCutCapFCore
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap2Counts -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount



































-- Triangle anchor (`PlanarMapCutCapEval.lean`):  V' = 6 = V + k = 3 + 3.























-- Triangle anchor (`PlanarMapCutCapEval.lean`):  F' = 4 = F + 2 = 2 + 2.







end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapEval -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv



section Counters

variable {α : Type*} [DecidableEq α]

















end Counters



namespace TriangleMap

open CombMap



















-- α', σ', φ' cycle counts of the *base* triangle map:
                 -- V = 3 (expected)
                 -- E = 3 (expected)
  -- F = 2 (expected)
-- χ = V - E + F = 3 - 3 + 2 = 2.


-- base-map connectivity: one dartStep component.
        -- c = 1 (connected, expected)

end TriangleMap



namespace TriangleCut

open CombMap TriangleMap




























-- σ' table:  (enc x, enc (σ' x))

-- α' table:

-- φ' = σ' ∘ α' table:




-- E' = number of α'-cycles  (expected 6 = E + k = 3 + 3):

-- V' = number of σ'-cycles  (expected 6 = V + k = 3 + 3):

-- F' = number of φ'-cycles  (φ' = σ' ∘ α'):

-- χ' = V' - E' + F'




-- c = number of dartStep-components of the cut map  (the disputed number):


-- Sanity: cutAlphaC and cutSigmaC are bijections (images have 12 distinct darts).
   -- expect 12
   -- expect 12


  -- F + 2c - 2





              -- c_i^- ↦ p_i

-- corrected σ' table:

-- corrected φ' = σ'₂ ∘ α':


-- CORRECTED verdict numbers:
                              -- E' = 6
                             -- V' = 6
    -- F' = 4  (FIXED)
  -- χ' = 4
               -- c = 2  (FIXED)
-- corrected σ'₂ is a bijection (12 distinct images):
  -- 12

end TriangleCut

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2Counts
import ProofsInTheBook.PlanarMapCutCapEval
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap2F -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount























end SimplePrimalCycle

end CombMap



namespace TriangleCut

open TriangleMap

-- Corrected `φ'₂ = σ'₂ ∘ α'` face-cycle count on the triangle cut:
-- expected `4 = F + 2` (`F = 2`).
   -- 4

-- The explicit `φ'₂`-orbit partition on the triangle (the structural reconnaissance):
-- forward cycle darts `{0,2,4}`, the reverse face `{1,5,3}`, the `+`-caps, the
-- `−`-caps — four orbits, `F' = 4 = F + 2`.


end TriangleCut

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2F
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap2FWalk -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

























end SimplePrimalCycle

end CombMap



namespace TriangleCut

open TriangleMap

-- Corrected `φ'₂ = σ'₂ ∘ α'` face-cycle count on the triangle cut: `4 = F + 2`.
   -- 4

-- `phiLift` reference count `F + 2k = 2 + 6 = 8` (caps as 2k singletons):
   -- 8 = F + 2k

-- The two `faceCorr₂` cap chains (here pure caps `{+0,+2,+1}` and `{−0,−1,−2}`):
-- print the `φ'₂`-orbit reps so the `−(k−1)` per chain is anchored.


end TriangleCut

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2FWalk
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ForcedSplits -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ForcedSplits



variable {X : Type*} [Fintype X] [DecidableEq X]




































end ForcedSplits



namespace ProofsInTheBook.PlanarMap

open ForcedSplits CombMap CombMap.SimplePrimalCycle

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}















end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2FWalk
-/
/- Source module: ProofsInTheBook.PlanarMapSeamChain -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook.PlanarMap

namespace SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]























































namespace SeamChainData

































































end SeamChainData



namespace SeamChainData













end SeamChainData

end SeamChain

end ProofsInTheBook.PlanarMap
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ForcedSplits
import ProofsInTheBook.PlanarMapSeamChain
-/
/- Source module: ProofsInTheBook.FaceCorrWord -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWord

open ForcedSplits SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]

































end FaceCorrWord



namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain

variable {M : CombMap D}











end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWord



end FaceCorrWord



namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWordEval








section
variable {n : ℕ} (alpha sigma : Fin n → Fin n) (dart : Fin 3 → Fin n)






end






















-- The cycle-list word realises `phiLift · faceCorr₂` across genus (all `true`):



-- The cycle-list shapes (genus-dependent; the word is uniform, the splits are not):




end FaceCorrWordEval










end ProofsInTheBook.PlanarMap

end ProofsInTheBook.PlanarMap
end

/- Original source header (imports hoisted):
import ProofsInTheBook.FaceCorrWord
import ProofsInTheBook.RelationComponentCount
-/
/- Source module: ProofsInTheBook.TouchRank -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.TouchRank

open ForcedSplits

variable {X : Type*} [Fintype X] [DecidableEq X]



































variable {p : Equiv.Perm X} {m B : ℕ} {W : Fin m → Swap X}































































namespace TouchCompressionCert

variable {p : Equiv.Perm X} {m B : ℕ} {W : Fin m → Swap X}









































end TouchCompressionCert









end ProofsInTheBook.TouchRank



namespace ProofsInTheBook.PlanarMap

open ForcedSplits CombMap CombMap.SimplePrimalCycle
open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}











end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap








end

/- Original source header (imports hoisted):
import ProofsInTheBook.TouchRank
-/
/- Source module: ProofsInTheBook.TouchCert -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook

namespace TouchCert

open ForcedSplits ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]













end TouchCert



namespace PlanarMap

open ForcedSplits ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.TouchCert

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}









end SimplePrimalCycle

end CombMap

end PlanarMap



namespace TouchCert

open ForcedSplits ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain







end TouchCert

end ProofsInTheBook








end

/- Original source header (imports hoisted):
import ProofsInTheBook.TouchCert
-/
/- Source module: ProofsInTheBook.SeamStructure -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook

namespace SeamStructure

open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]















end SeamStructure



namespace PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount





















open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord









end SimplePrimalCycle

end CombMap

end PlanarMap



namespace SeamStructure

open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain





end SeamStructure

end ProofsInTheBook











end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapF
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapConn -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}





















































end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapConn
-/
/- Source module: ProofsInTheBook.PlanarMapDualPathSep -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}























































end SimplePrimalCycle



namespace SimplePrimalCycle

variable {M : CombMap D}





end SimplePrimalCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2FWalk
import ProofsInTheBook.PlanarMapDualPathSep
-/
/- Source module: ProofsInTheBook.PlanarMapBridge -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}





































































































































end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBridge
import ProofsInTheBook.PlanarMapSeparation
-/
/- Source module: ProofsInTheBook.PlanarMapBridgeWitness -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

























end SimplePrimalCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.SeamStructure
import ProofsInTheBook.PlanarMapBridgeWitness
-/
/- Source module: ProofsInTheBook.SeamApplication -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}













end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}





end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle










end

/- Original source header (imports hoisted):
import ProofsInTheBook.SeamApplication
-/
/- Source module: ProofsInTheBook.SeamIncidence -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function
open ProofsInTheBook.TouchRank

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}



















end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





end NearTriangulation



namespace SimplePrimalCycle

variable {M : CombMap D}

open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.SeamStructure



namespace ArcChordSeam

variable {C : SimplePrimalCycle M}







end ArcChordSeam

end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

open ProofsInTheBook.TouchRank

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}





end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle










end

/- Original source header (imports hoisted):
import ProofsInTheBook.SeamIncidence
-/
/- Source module: ProofsInTheBook.DartArc -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv
open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]





namespace DartArc

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}









end DartArc







namespace SimplePrimalCycle

variable {M : CombMap D}





















open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.SeamStructure



end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}







end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle









end

/- Original source header (imports hoisted):
import ProofsInTheBook.DartArc
import ProofsInTheBook.PlanarMapBridge
import ProofsInTheBook.PlanarMapBridgeWitness
-/
/- Source module: ProofsInTheBook.WitnessFinal -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function
open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.SeamStructure

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}







































end SimplePrimalCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}





end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle











end

/- Original source header (imports hoisted):
import ProofsInTheBook.WitnessFinal
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ChordSeparation -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}















end CombMap.SimplePrimalCycle



namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}



end CombMap.SimplePrimalCycle

namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}





end CombMap.SimplePrimalCycle

namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace CombMap.SimplePrimalCycle



variable {M : CombMap D}







end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSeparation
-/
/- Source module: ProofsInTheBook.ChordGateCompat -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

























































end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap














end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordGateCompat
-/
/- Source module: ProofsInTheBook.ChordSeparationClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

























end CombMap.SimplePrimalCycle



namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}







end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap











end

/- Original source header (imports hoisted):
import ProofsInTheBook.FaceCorrWord
import ProofsInTheBook.ChordSeparationClose
-/
/- Source module: ProofsInTheBook.ZinanCh35CountRoute -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List
open scoped Finset

namespace ForcedSplits

variable {X : Type*} [Fintype X] [DecidableEq X]







end ForcedSplits

namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWord

open ForcedSplits SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]







end FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain

variable {M : CombMap D}












-- If Mathlib renamed this, alternates: `Finset.orderIsoOfFin S`,
-- `Fintype.equivFin {x // x ∈ S}`.

















end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation

end ProofsInTheBook.PlanarMap















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35CountRoute
-/
/- Source module: ProofsInTheBook.ZinanCh35Split -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.PlanarMap

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CutCapCount



section SumCongrTwo

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]



















end SumCongrTwo



end CutCapCount

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain CutCapCount

variable {M : CombMap D}















        -- c_i⁻ ↦ dart i

  -- c_i⁻ ↦ α (dart i)















































































end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation

end ProofsInTheBook.PlanarMap




















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Split
-/
/- Source module: ProofsInTheBook.ZinanCh35Gates -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.PlanarMap

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open CutCapCount

variable {M : CombMap D}





































end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}



end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

















end ProofsInTheBook.PlanarMap
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Iota
import ProofsInTheBook.ZinanCh35Gates
-/
/- Source module: ProofsInTheBook.ZinanCh35Confinement -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Confinement

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ZinanCh35Iota
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]























end ProofsInTheBook.ZinanCh35Confinement









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35Confinement
-/
/- Source module: ProofsInTheBook.ZinanCh35Schoenflies -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Schoenflies

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ZinanCh35Iota
open ProofsInTheBook.ZinanCh35Confinement
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]





































end ProofsInTheBook.ZinanCh35Schoenflies











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Schoenflies
-/
/- Source module: ProofsInTheBook.ZinanCh35EdgeCore -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35EdgeCore

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}































end ProofsInTheBook.ZinanCh35EdgeCore








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35EdgeCore
-/
/- Source module: ProofsInTheBook.ZinanCh35Coverage -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Coverage

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



section Abstract

variable {V : Type*} (r : V → V → Prop)





end Abstract





























end ProofsInTheBook.ZinanCh35Coverage









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35Coverage
-/
/- Source module: ProofsInTheBook.ZinanCh35InnerConn -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35InnerConn

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}





































variable {u v : M.Vertex}









end ProofsInTheBook.ZinanCh35InnerConn












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35InnerConn
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterDual -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterDual

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35InnerConn
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}





































variable {u v : M.Vertex}





end ProofsInTheBook.ZinanCh35OuterDual















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterDual
import ProofsInTheBook.RelationComponentCount
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterCount -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35InnerConn
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35OuterDual

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}



























variable {u v : M.Vertex}







end ProofsInTheBook.ZinanCh35OuterCount













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterCount
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterSlack -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterSlack

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35OuterDual
open ProofsInTheBook.ZinanCh35OuterCount
open ProofsInTheBook.SubmapPlanar

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}




























variable {hNT : NearTriangulation M}







































































end ProofsInTheBook.ZinanCh35OuterSlack













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterSlack
-/
/- Source module: ProofsInTheBook.ZinanCh35BankCount -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35OuterDual
open ProofsInTheBook.ZinanCh35OuterSlack
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}

variable {hNT : NearTriangulation M}



/-- The boundary length `B`. -/
local notation3 "B" => hNT.outerCycle.length







































































































end ProofsInTheBook.ZinanCh35BankCount






end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35EdgeCore
-/
/- Source module: ProofsInTheBook.ZinanCh35StarConn -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35StarConn

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

































































end ProofsInTheBook.ZinanCh35StarConn








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35BankCount
import ProofsInTheBook.ZinanCh35StarConn
-/
/- Source module: ProofsInTheBook.ZinanCh35CycleBank -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35CycleBank

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35OuterSlack
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}



variable (C : SimplePrimalCycle M)































































































































































end ProofsInTheBook.ZinanCh35CycleBank











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35CycleBank
import ProofsInTheBook.ZinanCh35Gates
-/
/- Source module: ProofsInTheBook.ZinanCh35BankLabels -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankLabels

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35CycleBank
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
variable (C : SimplePrimalCycle M)











































end ProofsInTheBook.ZinanCh35BankLabels








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Gates
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordCycle -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}








end BoundaryCycle



namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}





end BoundaryCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle



variable {u v : M.Vertex}









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35EdgeCore
-/
/- Source module: ProofsInTheBook.ZinanCh35Schoenflies2 -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Schoenflies2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

































end ProofsInTheBook.ZinanCh35Schoenflies2












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35BankCount
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35Schoenflies2
-/
/- Source module: ProofsInTheBook.ZinanCh35EdgeCoreFinal -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ZinanCh35EdgeCoreFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35OuterCount
open ProofsInTheBook.ZinanCh35BankCount
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35Schoenflies2

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}







end ProofsInTheBook.ZinanCh35EdgeCoreFinal

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Schoenflies
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
-/
/- Source module: ProofsInTheBook.ZinanCh35Side1Confine -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side1Confine

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}













end ProofsInTheBook.ZinanCh35Side1Confine






end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordCycle
import ProofsInTheBook.ZinanCh35EdgeCore
import ProofsInTheBook.ZinanCh35Side1Confine
-/
/- Source module: ProofsInTheBook.ZinanCh35ArcDartRun -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ArcDartRun

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}





namespace BoundaryPathDartRun

variable {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}





end BoundaryPathDartRun



section DartArcHelpers

variable {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}











end DartArcHelpers





namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}





end NearTriangulation



namespace NearTriangulation

variable (hNT : NearTriangulation M) {u v : M.Vertex}

open ProofsInTheBook.PlanarMap.CombMap.BoundaryCycle





end NearTriangulation



namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}





end NearTriangulation



namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}





end NearTriangulation

end ProofsInTheBook.ZinanCh35ArcDartRun











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ArcDartRun
import ProofsInTheBook.ZinanCh35ChordCycle
-/
/- Source module: ProofsInTheBook.ZinanCh35Contiguity -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Contiguity

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35ArcDartRun

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



























end ProofsInTheBook.ZinanCh35Contiguity












end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter35 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Chapter35

open scoped BigOperators







section KempeChains







end KempeChains

section FiveColorInduction

universe u























end FiveColorInduction









end ProofsInTheBook.Chapter35

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenInduction
import ProofsInTheBook.WitnessFinal
-/
/- Source module: ProofsInTheBook.JordanOracleConstruct -/
section
set_option autoImplicit true




namespace ProofsInTheBook.JordanOracleConstruct

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ListColoring

universe u











variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D}





end ProofsInTheBook.JordanOracleConstruct



namespace ProofsInTheBook.JordanOracleConstruct

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u





end ProofsInTheBook.JordanOracleConstruct








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Schoenflies
-/
/- Source module: ProofsInTheBook.ZinanCh35FinalClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35FinalClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ZinanCh35Iota
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]





























end ProofsInTheBook.ZinanCh35FinalClose










end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.ThomassenInduction
-/
/- Source module: ProofsInTheBook.ChordlessClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordlessClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}























end ProofsInTheBook.ChordlessClose












end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.ChordlessClose
-/
/- Source module: ProofsInTheBook.ChordlessFinal -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordlessFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessClose

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}









































end ProofsInTheBook.ChordlessFinal












end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter35
import ProofsInTheBook.JordanOracleConstruct
import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35FinalClose
import ProofsInTheBook.ChordlessFinal
-/
/- Source module: ProofsInTheBook.ZinanCh35Cert -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Cert

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ListColoring

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]

















/-- The same conversion when the five colors are universe-lifted to match the
dart universe used by the Thomassen machinery. -/
theorem colorable_of_ulift_univ_listColorable {V : Type u} (G : SimpleGraph V)
    (h : ListColorable G (fun _ : V => (Finset.univ : Finset (ULift.{u} (Fin 5))))) :
    G.Colorable 5 := by
  rcases h with ⟨c, hc⟩
  exact ⟨SimpleGraph.Coloring.mk (fun x => (c x).down) (by
    intro a b hab hsame
    exact hc.2 hab (ULift.ext _ _ hsame))⟩

/-- Five-colorability of a near-triangulation from the named remaining planar
input.  This is the sharp current `fiveColor_of_planarInputs` theorem: side-1
can be supplied by `side₁Reconstruction_of_certificateInputs`, but the induction
still needs a uniform two-sided/chordless `ChordRecursiveDichotomy`. -/
theorem fiveColor_of_planarInputs
    (hNT : NearTriangulation M) (input : PlanarInputs (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  colorable_of_ulift_univ_listColorable M.toSimpleGraph
    (nearTriangulation_five_colorable_unified (M := M) (α := ULift.{u} (Fin 5)) hNT
      (by simp)
      (fun _ _ _ _ => input.recursiveDichotomy))









end ProofsInTheBook.ZinanCh35Cert









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Cert
import ProofsInTheBook.ZinanCh35EdgeCore
-/
/- Source module: ProofsInTheBook.ZinanCh35Side2 -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]



















































































end ProofsInTheBook.ZinanCh35Side2














end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Side2
import ProofsInTheBook.ZinanCh35Side1Confine
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35Schoenflies2
-/
/- Source module: ProofsInTheBook.ZinanCh35Side2Confine -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side2Confine

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35Schoenflies2
open ProofsInTheBook.ZinanCh35Side2

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

































end ProofsInTheBook.ZinanCh35Side2Confine











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Side1Confine
import ProofsInTheBook.ZinanCh35Side2Confine
-/
/- Source module: ProofsInTheBook.ZinanCh35BankOrient -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankOrient

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



































end ProofsInTheBook.ZinanCh35BankOrient















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35BankLabels
import ProofsInTheBook.ZinanCh35ChordCycle
import ProofsInTheBook.ZinanCh35Contiguity
import ProofsInTheBook.ZinanCh35BankOrient
import ProofsInTheBook.ZinanCh35InnerConn
-/
/- Source module: ProofsInTheBook.ZinanCh35ArcSide -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ArcSide

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35CycleBank
open ProofsInTheBook.ZinanCh35BankLabels

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}











































































































end ProofsInTheBook.ZinanCh35ArcSide



-- The UNCONDITIONAL bank-side facts (the real new content of R8's chain A–F):








-- The honest assembly over the single isolated orientation input:






end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ArcSide
-/
/- Source module: ProofsInTheBook.ZinanCh35Aligned -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Aligned

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35CycleBank
open ProofsInTheBook.ZinanCh35BankLabels
open ProofsInTheBook.ZinanCh35ArcDartRun

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}











































namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}























































end NearTriangulation







namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}





































-- Both arcs of the normalized arc-split carry genuine internal vertices (the construction fires).


-- `Separates` for the normalized datum is the genuine chord keystone `face₂ ∉ side₁` (not trivial).


-- The datum's chord is the GIVEN chord, so `side₁`/`side₂` are the real chord sides.


-- The two runs have length ≥ 2 (genuinely longer than the chord — the arcs carry interior vertices).


end NearTriangulation

end ProofsInTheBook.ZinanCh35Aligned












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Aligned
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.ZinanCh35BoundaryAssembler -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BoundaryAssembler

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ZinanCh35Aligned

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}



namespace BoundaryCycle

variable {f : M.Face}









end BoundaryCycle




















end ProofsInTheBook.ZinanCh35BoundaryAssembler

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitNT
import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35Cert
-/
/- Source module: ProofsInTheBook.ZinanCh35Dichotomy -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Dichotomy

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordSplitFinal

universe u

variable {α : Type u} [DecidableEq α]





















/-- **Five-colorability of a near-triangulation from the two named branch
suppliers.**  Composing `planarInputs_of_suppliers` with
`ZinanCh35Cert.fiveColor_of_planarInputs`: every near-triangulation is
five-colorable given the chord-branch and chordless-branch suppliers — the entire
Chapter-35 induction surface now reduced to those two isolated planar residues. -/
theorem fiveColor_of_branchSuppliers
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (Sc : ChordBranchSupplier (ULift.{u} (Fin 5)))
    (Sl : ChordlessBranchSupplier (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35Cert.fiveColor_of_planarInputs hNT
    (planarInputs_of_suppliers Sc Sl)

end ProofsInTheBook.ZinanCh35Dichotomy









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Dichotomy
import ProofsInTheBook.ZinanCh35Side2
import ProofsInTheBook.ZinanCh35Aligned
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordBranch -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordBranch

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35Side2
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]



















/-- Abbreviation for the normalized split datum of a chord. -/
local notation3 "ND " h => ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h















/-- **Five-colorability of a near-triangulation from the residual chord-branch supplier and a
chordless supplier.**  The chord half of Chapter 35 is now reduced to the confinement-free
residual bundle. -/
theorem fiveColor_of_residual
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (S : ChordBranchResidualSupplier (ULift.{u} (Fin 5)))
    (Sl : ProofsInTheBook.ZinanCh35Dichotomy.ChordlessBranchSupplier (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35Dichotomy.fiveColor_of_branchSuppliers hNT
    (chordBranchSupplier_of_residual S) Sl



-- The residual genuinely PRODUCES (does not posit) the side-2 confinement: the field type that
-- `Side₂CertificateInputs.confinement` requires is exactly the output of
-- `bothConfinements_normalized`'s second component.


-- The residual data's `side₁`/`side₂` carry NO confinement field (audit: the confinement burden
-- is off the residual — it is the genuine reduction `bothConfinements_normalized` buys).


end ProofsInTheBook.ZinanCh35ChordBranch











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordBranch
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35SideAnchors
import ProofsInTheBook.ChordSigmaContig
import ProofsInTheBook.ChordContiguous
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordResidue -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordResidue

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35ChordBranch
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]





































-- The canonical side-1 anchors genuinely realize the chord endpoints (non-vacuity of `anchors₁`).


-- The produced region glue pins `s₁ = sideRegion₁`, `s₂ = sideRegion₂` definitionally (the
-- `regions_s₁`/`regions_s₂` of the residual data are `rfl`).


end ProofsInTheBook.ZinanCh35ChordResidue












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35Side2Confine
import ProofsInTheBook.ZinanCh35Schoenflies2
import ProofsInTheBook.ZinanCh35ArcSide
-/
/- Source module: ProofsInTheBook.ZinanCh35Regions -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Regions

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ZinanCh35Schoenflies2
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35ArcSide

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



























-- The side-2 region genuinely contains both chord endpoints (non-vacuity of `u_s₂`/`v_s₂`).


end ProofsInTheBook.ZinanCh35Regions










end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterTrace
import ProofsInTheBook.ZinanCh35BoundaryAssembler
import ProofsInTheBook.ZinanCh35Side2
-/
/- Source module: ProofsInTheBook.ZinanCh35Contiguous -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Contiguous

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35OuterTrace

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u



section Itinerary

variable {K : Type u} [Fintype K] [DecidableEq K]
  (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

















end Itinerary



variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



















section Audit

variable {K : Type u} [Fintype K] [DecidableEq K]
  (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)





end Audit

end ProofsInTheBook.ZinanCh35Contiguous












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Contiguous
-/
/- Source module: ProofsInTheBook.ZinanCh35SideOuterSimple -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35SideOuterSimple

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ZinanCh35SideAnchors

universe u



section Bridge

variable {D : Type*} [Fintype D] [DecidableEq D]



end Bridge



section FreshTail

variable {K : Type u} [Fintype K] [DecidableEq K]
  (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)



end FreshTail



section SideTail

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



end SideTail



section Main

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  (hNT : NearTriangulation M) {u v : M.Vertex}

















end Main

end ProofsInTheBook.ZinanCh35SideOuterSimple











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordAnchorInst
import ProofsInTheBook.ChordDisk
-/
/- Source module: ProofsInTheBook.ZinanCh35Side2Anchors -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35Side2Anchors

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u
variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



































end ProofsInTheBook.ZinanCh35Side2Anchors



end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideClose
-/
/- Source module: ProofsInTheBook.ZinanCh35Side2Disk -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSideClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.SubmapPlanar

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



















section RawConnected



























end RawConnected











end ProofsInTheBook.ChordSideClose







end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35SideOuterSimple
import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35ArcDartRun
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35ArcSide
import ProofsInTheBook.ZinanCh35BoundaryAssembler
import ProofsInTheBook.ZinanCh35Side2Anchors
import ProofsInTheBook.ChordDisk
import ProofsInTheBook.ZinanCh35Side2Disk
import ProofsInTheBook.ZinanCh35Regions
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterTraceProof -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterTraceProof

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35SideOuterSimple
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ZinanCh35OuterTrace
open ProofsInTheBook.ZinanCh35Side2Anchors

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}





































variable (hNT : NearTriangulation M) {u v : M.Vertex}
variable {a b : M.Vertex}











































































































































































































































































































variable {α : Type u} [DecidableEq α]









end ProofsInTheBook.ZinanCh35OuterTraceProof
















































end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Side2Confine
import ProofsInTheBook.ZinanCh35Aligned
import ProofsInTheBook.ZinanCh35Regions
import ProofsInTheBook.ZinanCh35Iota
import ProofsInTheBook.ZinanCh35OuterTraceProof
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordSupplier -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordSupplier

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation
open ProofsInTheBook.ZinanCh35Regions
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v p q : M.Vertex}















































































end ProofsInTheBook.ZinanCh35ChordSupplier

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordSupplier
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordSupplier2 -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordSupplier2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation
open ProofsInTheBook.ZinanCh35Regions
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35Side2Anchors
open ProofsInTheBook.ZinanCh35OuterTrace
open ProofsInTheBook.ZinanCh35OuterTraceProof
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35ChordSupplier

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v p q : M.Vertex}









































end ProofsInTheBook.ZinanCh35ChordSupplier2



end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapOuterArc
import ProofsInTheBook.PlanarMapBoundaryArcSplit
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterV0Consecutive -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}





end BoundaryCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M) {v0 : M.Vertex}















end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35InnerConn
-/
/- Source module: ProofsInTheBook.ZinanCh35Chordless -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Chordless

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)


































end ProofsInTheBook.ZinanCh35Chordless
end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.ZinanCh35Chordless
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessFull -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessFull

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)











































end ProofsInTheBook.ZinanCh35ChordlessFull












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordlessFull
import ProofsInTheBook.PlanarMapFanConnectivity
-/
/- Source module: ProofsInTheBook.ZinanCh35FanBackward -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35FanBackward

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}



















variable (hNT)



variable {hNT}







































namespace Conn

variable {v0 : M.Vertex}





























end Conn



















end ProofsInTheBook.ZinanCh35FanBackward

















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35FanBackward
import ProofsInTheBook.ZinanCh35ChordlessFull
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}









end ProofsInTheBook.ZinanCh35ChordlessClose








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterV0Consecutive
import ProofsInTheBook.ZinanCh35ChordlessClose
-/
/- Source module: ProofsInTheBook.ZinanCh35MergedArc -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35MergedArc

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}



















end ProofsInTheBook.ZinanCh35MergedArc












end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapOuterArc
import ProofsInTheBook.ChordlessFinal
import ProofsInTheBook.ZinanCh35ChordlessClose
import ProofsInTheBook.ZinanCh35BoundaryAssembler
-/
/- Source module: ProofsInTheBook.ZinanCh35DeletedBoundary -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35DeletedBoundary

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessClose
open ProofsInTheBook.ChordlessFinal

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}





namespace DeletedSeamData

variable {fan : BoundaryVertexFan hNT v0} {hchord : BoundaryChordless hNT.outerCycle}
  {d0 : D} {htail0 : M.tail d0 = v0}























end DeletedSeamData





















end ProofsInTheBook.ZinanCh35DeletedBoundary

















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35MergedArc
import ProofsInTheBook.ZinanCh35DeletedBoundary
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.ZinanCh35DeletedAssembly -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35DeletedAssembly

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessFinal

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}



































































end ProofsInTheBook.ZinanCh35DeletedAssembly















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35FanBackward
import ProofsInTheBook.ZinanCh35ChordlessClose
import ProofsInTheBook.ZinanCh35Dichotomy
import ProofsInTheBook.ChordlessClose
import ProofsInTheBook.ChordlessFinal
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessOracle -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessOracle

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ZinanCh35Dichotomy

universe u



variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}

























variable {α : Type u} [DecidableEq α]











end ProofsInTheBook.ZinanCh35ChordlessOracle
















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenLists
import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.PlanarMapFanSurgery
import Mathlib.Data.Finset.Basic
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessSite -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessSite

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}

namespace BoundaryCycle

variable {f : M.Face}









end BoundaryCycle

namespace NearTriangulation

variable {v : M.Vertex}







end NearTriangulation

















end ProofsInTheBook.ZinanCh35ChordlessSite

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordlessSite
import ProofsInTheBook.ZinanCh35DeletedAssembly
import ProofsInTheBook.ZinanCh35DeletedBoundary
import ProofsInTheBook.ZinanCh35ChordlessOracle
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessSupplier -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessSupplier

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}











































































end ProofsInTheBook.ZinanCh35ChordlessSupplier

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35Regions
import ProofsInTheBook.ZinanCh35ChordSupplier
import ProofsInTheBook.ZinanCh35ChordSupplier2
import ProofsInTheBook.ZinanCh35MergedArc
import ProofsInTheBook.ZinanCh35DeletedAssembly
import ProofsInTheBook.ZinanCh35ChordlessOracle
import ProofsInTheBook.ZinanCh35ChordlessSupplier
-/
/- Source module: ProofsInTheBook.ZinanCh35Final -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Final

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ZinanCh35Dichotomy
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35ChordlessOracle

universe u

variable {α : Type u} [DecidableEq α]



































/-- The direct canonical Chapter-35 endpoint: the chord branch uses the already
closed canonical chord residual supplier, and the chordless branch uses the
closed Phase-C deletion supplier. -/
theorem fiveColor_planar_canonical
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35ChordBranch.fiveColor_of_residual hNT
    (ProofsInTheBook.ZinanCh35ChordSupplier2.canonicalChordBranchResidualSupplier
      (ULift.{u} (Fin 5)))
    (canonicalChordlessBranchSupplier (ULift.{u} (Fin 5)))



end ProofsInTheBook.ZinanCh35Final














end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlaneSimpleGraph
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.FaceDiagonalSurgery
import ProofsInTheBook.Ch13ActiveComponent
import ProofsInTheBook.ZinanCh35BoundaryAssembler
import ProofsInTheBook.ZinanCh35Final
-/
/- Source module: ProofsInTheBook.PlaneSimpleGraphTriangulate -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace PlaneSimpleGraph

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]































end PlaneSimpleGraph






namespace TriangleWitness

open PlaneSimpleGraph









































end TriangleWitness



universe u v u'

section Extension

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]



/-- Pull a five-colouring of the triangulating near-triangulation back along the embedded
vertex map. -/
theorem colorable_of_triangulationExtension (P : PlaneSimpleGraph V D)
    (E : PlaneTriangulationExtension P) :
    P.G.Colorable 5 := by
  letI := E.fintypeD'
  letI := E.decidableEqD'
  rcases ProofsInTheBook.ZinanCh35Final.fiveColor_planar_canonical E.hNT with ⟨C⟩
  exact ⟨SimpleGraph.Coloring.mk (fun v => C (E.ιV v)) (by
    intro u v huv
    exact C.valid (E.adj_embed huv))⟩

/-- Five-colourability of a plane simple graph from a triangulation-extension certificate.
This is the P5a endpoint; later phases replace the certificate by a producer. -/
theorem fiveColor_planeSimpleGraph_of_extension (P : PlaneSimpleGraph V D)
    (E : PlaneTriangulationExtension P) :
    P.G.Colorable 5 :=
  colorable_of_triangulationExtension P E

end Extension





namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



































































































end CombMap

namespace PlaneSimpleGraph

variable {V : Type v} {D : Type u} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]







end PlaneSimpleGraph

namespace TriangleWitness



















end TriangleWitness



















end ProofsInTheBook.PlanarMap

end


set_option autoImplicit true
set_option linter.unusedSectionVars false
open ProofsInTheBook.PlanarMap
open Equiv
universe u v u'
open ProofsInTheBook.PlanarMap.PlaneSimpleGraph
variable {V : Type v} {D : Type u} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

theorem solution (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v)
    (h3 : P.toCombMap.FaceLengthGe 3)
    [Nonempty D] :
    P.G.Colorable 5 :=
  fiveColor_planeSimpleGraph_of_extension P
    (P.triangulationExtension hsphere hincident h3)
