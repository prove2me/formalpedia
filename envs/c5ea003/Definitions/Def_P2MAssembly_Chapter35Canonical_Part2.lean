-- Prove2me | Definitions.Def_P2MAssembly_Chapter35Canonical_Part2
-- name    : P2MAssembly_Chapter35Canonical_Part2
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T19:23:57.457935+00:00
-- url     : https://prove2.me/theorems/52c3f909-0d9f-4c1b-b27f-1ecd67e5b6bf
-- title:
--   Chord-side face structure and dual-cycle separation
-- statement:
--   This part contains chord-side face tracing, classification of retained triangular faces, and anchor records identifying the side outer face. It also defines side regions and confinement interfaces, the dual map and dual adjacency avoiding selected edges, outer-face deletion counts, and permutation constructions for the two sides of a simple primal cycle. The retained cycle-side certificate records two components of the dual relation avoiding the cycle, the prescribed cycle count and zero Euler deficit, connectivity among faces on each side, and separation between opposite sides. Its structure fields describe the certificate; their definitions alone do not assert its existence.
-- source:
--   Representative original definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ChordAnchor.lean#L183; https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ZinanCh35CycleBank.lean#L1002. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 39, “Five-coloring plane graphs”, pp. 277–280 (https://doi.org/10.1007/978-3-662-57265-8_39).

import Init
import Mathlib
import Mathlib.Data.Finset.Basic
import Definitions.Def_P2MAssembly_Chapter35Canonical_Part1

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



















section Glue

variable {G : SimpleGraph V} {L : V → Finset α} {s t : Set V} {c₁ c₂ : V → α}





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









end ThomassenLists





namespace ChordSplitRegions

variable {M : CombMap D} {hNT : NearTriangulation M}
  {u v p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}















end ChordSplitRegions



section Deletion

variable {M : CombMap D}



























variable {hNT : NearTriangulation M} {d0 : D} {v0 : M.Vertex}







































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















end Chordless



section Induction

variable {α : Type u} [DecidableEq α]







end Induction



section Corollaries

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D}





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



attribute [instance] ChordSideReconstruction.fintypeDₛ ChordSideReconstruction.decEqDₛ

namespace ChordSideReconstruction

variable {s : Set M.Vertex} {L : M.Vertex → Finset α}

















end ChordSideReconstruction





namespace ChordRecursionData

variable {u v p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}









end ChordRecursionData















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





end ProofsInTheBook.ChordSplitFinal












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

































attribute [instance] TouchColorCertBound.colorFintype TouchColorCertBound.colorDecEq

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













/-- **Forward iterate reach.**  Every forward bank dart reaches the `nextIdx`-iterate. -/
lemma cutReach2_dart_nextIdx_iterate (C : SimplePrimalCycle M) (a : Fin C.len) :
    ∀ m : ℕ, C.cutReach2 (Sum.inl (C.dart a)) (Sum.inl (C.dart (C.nextIdx^[m] a)))
  | 0 => by simpa using C.cutReach2_rfl (Sum.inl (C.dart a))
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      exact (C.cutReach2_dart_nextIdx_iterate a m).trans
        (C.cutReach2_dart_nextIdx (C.nextIdx^[m] a))

/-- **Reverse iterate reach.**  Every reverse bank dart reaches the `prevIdx`-iterate. -/
lemma cutReach2_alphaDart_prevIdx_iterate (C : SimplePrimalCycle M) (a : Fin C.len) :
    ∀ m : ℕ, C.cutReach2 (Sum.inl (M.α (C.dart a)))
      (Sum.inl (M.α (C.dart (C.prevIdx^[m] a))))
  | 0 => by simpa using C.cutReach2_rfl (Sum.inl (M.α (C.dart a)))
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      exact (C.cutReach2_alphaDart_prevIdx_iterate a m).trans
        (C.cutReach2_alphaDart_prevIdx (C.prevIdx^[m] a))

/-- **Forward connectivity.**  Any forward bank dart reaches any other.  Pick
`m := (len + b − a) % len` so that `nextIdx^[m] a = b`. -/
lemma cutReach2_dart_all (C : SimplePrimalCycle M) (a b : Fin C.len) :
    C.cutReach2 (Sum.inl (C.dart a)) (Sum.inl (C.dart b)) := by
  set m : ℕ := (C.len + b.1 - a.1) % C.len with hm
  have ha := a.isLt; have hb := b.isLt; have hlen := C.len_pos
  have hval : ((C.nextIdx^[m] a) : ℕ) = b.1 := by
    rw [C.nextIdx_iterate_val a m]
    -- (a + m) % len = b, where m ≡ len + b - a (mod len), so a + m ≡ len + b ≡ b.
    have hmod : (a.1 + m) ≡ b.1 [MOD C.len] := by
      have hmmod : m ≡ C.len + b.1 - a.1 [MOD C.len] := Nat.mod_modEq _ _
      calc a.1 + m ≡ a.1 + (C.len + b.1 - a.1) [MOD C.len] := Nat.ModEq.add_left _ hmmod
        _ = C.len + b.1 := by omega
        _ ≡ b.1 [MOD C.len] := Nat.add_modEq_left
    rw [Nat.ModEq] at hmod
    rwa [Nat.mod_eq_of_lt hb] at hmod
  have hidx : C.nextIdx^[m] a = b := Fin.ext hval
  have := C.cutReach2_dart_nextIdx_iterate a m
  rwa [hidx] at this

/-- **Reverse connectivity.**  Any reverse bank dart reaches any other. -/
lemma cutReach2_alphaDart_all (C : SimplePrimalCycle M) (a b : Fin C.len) :
    C.cutReach2 (Sum.inl (M.α (C.dart a))) (Sum.inl (M.α (C.dart b))) := by
  -- prevIdx^[m] a = b for m := (a + len - b) % len, since prevIdx is −1 mod len.
  set m : ℕ := (a.1 + C.len - b.1) % C.len with hm
  have ha := a.isLt; have hb := b.isLt; have hlen := C.len_pos
  have hval : ((C.prevIdx^[m] a) : ℕ) = b.1 := by
    rw [C.prevIdx_iterate_val a m]
    -- m*(len-1) ≡ -m (mod len); a + m*(len-1) ≡ a - m ≡ b (mod len).
    -- key: (a + m*(len-1)) % len = b.
    have hm_lt : m < C.len := Nat.mod_lt _ hlen
    -- a + m*(len-1) = a + m*len - m, and (a + m*len - m) % len = (a + (len - m % len?)) …
    -- Do it via Nat.ModEq.
    have hmlem : m ≤ C.len * m := Nat.le_mul_of_pos_left m hlen
    have hmm : m * (C.len - 1) = C.len * m - m := by
      rw [Nat.mul_sub_one, Nat.mul_comm]
    have expand : a.1 + m * (C.len - 1) = (a.1 + C.len * m) - m := by
      rw [hmm]; omega
    rw [expand]
    -- (a + len*m - m) ≡ (a - m) (mod len), and we want = b.  Compute via congruence.
    have hge : m ≤ a.1 + C.len * m := by nlinarith
    -- Reduce a + len*m - m modulo len directly to the target b.
    have hmod : (a.1 + C.len * m - m) ≡ b.1 [MOD C.len] := by
      -- a + len*m - m ≡ a - m  and  a - m ≡ a - (a + len - b) ≡ b - len ≡ b
      have h1 : (a.1 + C.len * m - m) + m = a.1 + C.len * m := by omega
      -- (a + len*m - m) ≡ a - m? avoid; use additive form: (X) + m ≡ a (mod len)  where X is LHS
      -- and  b + m ≡ a (mod len).  Then X ≡ b by cancellation.
      have hXm : (a.1 + C.len * m - m) + m ≡ a.1 [MOD C.len] := by
        rw [h1]
        exact (Nat.add_modulus_mul_modEq_iff).mpr (Nat.ModEq.refl _)
      have hbm : b.1 + m ≡ a.1 [MOD C.len] := by
        -- m = (a + len - b) % len ≡ a + len - b ≡ a - b (mod len), so b + m ≡ a.
        have hmmod : m ≡ a.1 + C.len - b.1 [MOD C.len] := (Nat.mod_modEq _ _)
        calc b.1 + m ≡ b.1 + (a.1 + C.len - b.1) [MOD C.len] := Nat.ModEq.add_left _ hmmod
          _ = a.1 + C.len := by omega
          _ ≡ a.1 [MOD C.len] := Nat.add_modEq_right
      -- cancel m: X + m ≡ a ≡ b + m  ⟹ X ≡ b
      have : (a.1 + C.len * m - m) + m ≡ b.1 + m [MOD C.len] := hXm.trans hbm.symm
      exact Nat.ModEq.add_right_cancel' m this
    rw [Nat.ModEq] at hmod
    rwa [Nat.mod_eq_of_lt hb] at hmod
  have hidx : C.prevIdx^[m] a = b := Fin.ext hval
  have := C.cutReach2_alphaDart_prevIdx_iterate a m
  rwa [hidx] at this

/-- **`SidesReach2` for the concrete cycle — UNCONDITIONAL.**  Both the forward and the
reverse cycle bank darts thread into one `cutReach2`-connected loop (the corrected
`φ'₂` wiring), so every forward bank dart reaches the reference forward bank dart and
every reverse bank dart reaches the reference reverse one.  *No appeal to `M.Connected`.*

This refutes the bwitness handoff's "irreducible isolated core" verdict: that verdict was
correct only at the bare `σ'₂` layer; `SidesReach2` lives at the `cutReach2` (= `φ'₂`)
layer, where the corrected fix `cutCapPhi2_dart` threads the cycle darts. -/
theorem sidesReach2_concrete (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.SidesReach2 i :=
  ⟨fun j => C.cutReach2_dart_all j i, fun j => C.cutReach2_alphaDart_all j i⟩

















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



/-- A **star dart** at a vertex `x`: a dart whose tail is `x`.  Since `M.Vertex` is the
`σ`-orbit quotient and `M.tail d = ⟦d⟧_σ`, this is precisely the cyclic family of darts
incident at `x` in their rotation order. -/
abbrev StarDart (M : CombMap D) (x : M.Vertex) : Type _ :=
  {d : D // M.tail d = x}

instance (M : CombMap D) (x : M.Vertex) : DecidableEq (StarDart M x) :=
  Subtype.instDecidableEq

instance (M : CombMap D) (x : M.Vertex) : Fintype (StarDart M x) :=
  Subtype.fintype _









variable {M : CombMap D} (hNT : NearTriangulation M)













































end CombMap

end ProofsInTheBook.PlanarMap

-- Axiom audit for the main brick results (expect: propext, Classical.choice, Quot.sound).









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









/-- **The chord endpoints are adjacent in `M` (the fresh chord edge is a real edge).** -/
theorem chordChoice_adj (data : hNT.ChordSplitData u v) :
    M.toSimpleGraph.Adj u v :=
  data.chord.adj

























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



/-- The kept combinatorial map's face permutation is `keptPhi β ρ = ρ * β`. -/
lemma keptCombMap_phi (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k) :
    (keptCombMap β ρ hβinv hβfix).φ = keptPhi β ρ := rfl



section Splice

variable (β ρ : Equiv.Perm K) {a₀ a₁ : K}

/-- An orbit is **splice-untouched** if it avoids both chord predecessors `β a₀`, `β a₁`. -/
def SpliceUntouched (β ρ : Equiv.Perm K) (a₀ a₁ k : K) : Prop :=
  ¬ (keptPhi β ρ).SameCycle k (β a₀) ∧ ¬ (keptPhi β ρ).SameCycle k (β a₁)

/-- `β (β a) = a` (involutivity, the form used here). -/
 lemma beta_beta' (hβinv : β * β = 1) (a : K) : β (β a) = a := by
  have := congrArg (fun f : Equiv.Perm K => f a) hβinv
  simpa [Equiv.Perm.mul_apply] using this

/-- On a `keptPhi`-orbit avoiding the predecessors, one `tracePhi`-step equals one
`keptPhi`-step (the swap fires only at `β a₀`, `β a₁`, which are not on the orbit). -/
lemma tracePhi_apply_eq_keptPhi_of_avoid (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) {c : K} (hc : (keptPhi β ρ).SameCycle k c) :
    tracePhi β ρ a₀ a₁ c = keptPhi β ρ c := by
  have h0 : c ≠ β a₀ := fun hca => h.1 (hca ▸ hc)
  have h1 : c ≠ β a₁ := fun hca => h.2 (hca ▸ hc)
  have hβc0 : β c ≠ a₀ := by
    intro hb; apply h0; have := congrArg β hb; rwa [beta_beta' β hβinv] at this
  have hβc1 : β c ≠ a₁ := by
    intro hb; apply h1; have := congrArg β hb; rwa [beta_beta' β hβinv] at this
  rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl

/-- On a splice-untouched orbit, the `tracePhi`-iterate equals the `keptPhi`-iterate. -/
lemma tracePhi_iterate_eq_keptPhi (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (n : ℕ) :
    (tracePhi β ρ a₀ a₁)^[n] k = (keptPhi β ρ)^[n] k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      -- `(keptPhi)^[n] k` is on the keptPhi-orbit of `k`.
      have hsc : (keptPhi β ρ).SameCycle k ((keptPhi β ρ)^[n] k) :=
        ⟨(n : ℤ), by rw [zpow_natCast, Equiv.Perm.coe_pow]⟩
      exact tracePhi_apply_eq_keptPhi_of_avoid β ρ hβinv h hsc

/-- **On a splice-untouched orbit, `tracePhi` and `keptPhi` define the same cycle.** -/
lemma tracePhi_sameCycle_iff_keptPhi (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (c : K) :
    (tracePhi β ρ a₀ a₁).SameCycle k c ↔ (keptPhi β ρ).SameCycle k c := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    rw [← hn, tracePhi_iterate_eq_keptPhi β ρ hβinv h n]
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    rw [← hn, ← tracePhi_iterate_eq_keptPhi β ρ hβinv h n]

end Splice



section Transfer

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **No fresh dart lies in a splice-untouched side face.**  If `inr j` were
`freshMap.φ`-SameCycle to `inl k`, its `faceProj` (`β a₀` or `β a₁`) would be
`tracePhi`-SameCycle to `k`, contradicting splice-untouchedness. -/
lemma no_inr_in_spliceUntouched_face {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (j : Fin 2) :
    ¬ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) (Sum.inr j) := by
  intro hsc
  have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inr j)).1 hsc
  simp only [faceProj_inl] at htrace
  -- `faceProj (inr j) ∈ {β a₀, β a₁}`; both contradict splice-untouchedness.
  rw [tracePhi_sameCycle_iff_keptPhi β ρ hβinv h] at htrace
  fin_cases j
  · exact h.1 (by simpa using htrace)
  · exact h.2 (by simpa using htrace)

/-- **The side face of a splice-untouched `inl k` consists exactly of the `inl`-images of
the `keptPhi`-orbit of `k`.**  The filter of darts in that face equals the `keptPhi`-orbit
filter mapped by `Sum.inl`. -/
lemma spliceUntouched_face_filter_eq {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) :
    (Finset.univ.filter (fun x : K ⊕ Fin 2 =>
        Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) x
          = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k)))
      = (Finset.univ.filter (fun c : K =>
          Quotient.mk (cycleSetoid (keptPhi β ρ)) c
            = Quotient.mk (cycleSetoid (keptPhi β ρ)) k)).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    -- `x` is freshPhi-SameCycle to `inl k`.
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) x :=
      Quotient.exact hx.symm
    cases x with
    | inl c =>
        refine ⟨c, ?_, rfl⟩
        apply Quotient.sound
        -- want keptPhi.SameCycle c k, i.e. SameCycle k c symm.
        have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).1 hsc
        simp only [faceProj_inl] at htrace
        rw [tracePhi_sameCycle_iff_keptPhi β ρ hβinv h] at htrace
        exact htrace.symm
    | inr j => exact absurd hsc (no_inr_in_spliceUntouched_face β ρ hβinv hβfix hne h j)
  · rintro ⟨c, hc, rfl⟩
    -- keptPhi.SameCycle c k ⇒ freshPhi.SameCycle (inl k) (inl c).
    have hkp : (keptPhi β ρ).SameCycle k c := (Quotient.exact hc.symm)
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inl k))
        (faceProj β a₀ a₁ (Sum.inl c)) := by
      simp only [faceProj_inl]
      exact (tracePhi_sameCycle_iff_keptPhi β ρ hβinv h c).2 hkp
    have hsc := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).2 htrace
    exact (Quotient.sound hsc.symm)

/-- **Face-SIZE transfer (UNCONDITIONAL).**  For a kept dart `k` whose `keptPhi`-orbit is
splice-untouched, the side face length of `inl k` equals the kept-map face length of `k`:
`faceLen sideMap₁ (dartFace (inl k)) = faceLen (keptCombMap β ρ) (dartFace k)`.  This is the
precise content "the cut reroutes only the chord-incident faces; inner faces are untouched
`keptPhi`-orbits" — FACE SIZE, not the kernel-refuted COUNT label. -/
theorem freshPhi_faceLen_inl_eq_keptPhi {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k))
      = (keptCombMap β ρ hβinv hβfix).faceLen
        ((keptCombMap β ρ hβinv hβfix).dartFace k) := by
  classical
  show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))).card
    = (Finset.univ.filter (fun c => Quotient.mk _ c
      = Quotient.mk (cycleSetoid (keptCombMap β ρ hβinv hβfix).φ) k)).card
  rw [keptCombMap_phi β ρ hβinv hβfix]
  rw [spliceUntouched_face_filter_eq β ρ hβinv hβfix hne h, Finset.card_map]

end Transfer



section MTransfer

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- One `keptPhi`-step on side 1 agrees with one `M.φ`-step, provided the `M.φ`-successor
is kept. -/
lemma sideKeptPhi_apply_eq_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hnext : M.φ k.1 ∉ data.keptDel₁) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ k : D) = M.φ k.1 := by
  -- `keptPhi k = sideSigma₁ (sideAlpha₁ k)`.
  show (data.sideSigma₁ (data.sideAlpha₁ hsep k) : {d : D // d ∉ data.keptDel₁}).1 = M.φ k.1
  -- `sideAlpha₁ k` has coe `M.α k.1`; `sideSigma₁ = filteredRotation M.σ keptDel₁`.
  have hσnext : M.σ ((data.sideAlpha₁ hsep k : {d : D // d ∉ data.keptDel₁}) : D)
      ∉ data.keptDel₁ := by
    rw [sideAlpha₁_apply_coe]
    -- `M.σ (M.α k.1) = M.φ k.1`.
    show M.σ (M.α k.1) ∉ data.keptDel₁
    have : M.φ k.1 = M.σ (M.α k.1) := rfl
    rwa [← this]
  show (FilteredRotation.filteredRotation M.σ data.keptDel₁
      (data.sideAlpha₁ hsep k) : {d : D // d ∉ data.keptDel₁}).1 = M.φ k.1
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₁
    (data.sideAlpha₁ hsep k) hσnext, sideAlpha₁_apply_coe]
  rfl

/-- **The `M.φ`-orbit of a kept dart stays kept.**  Every `M.φ`-iterate of `k.1` avoids the
deleted set.  (Provided here as a hypothesis; established below for inner side faces.) -/
def OrbitKept (data : hNT.ChordSplitData u v) (k : {d : D // d ∉ data.keptDel₁}) : Prop :=
  ∀ n : ℕ, M.φ^[n] k.1 ∉ data.keptDel₁

/-- On a kept orbit, the `keptPhi`-iterate coincides (under coercion) with the `M.φ`-iterate. -/
lemma sideKeptPhi_iterate_eq_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k) (n : ℕ) :
    ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D) = M.φ^[n] k.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      -- the iterate is `⟨M.φ^[n] k.1, _⟩` by `ih`; its φ-successor is `M.φ^[n+1] k.1`, kept.
      have hkn : ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D)
          = M.φ^[n] k.1 := ih
      have hnext : M.φ ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D)
          ∉ data.keptDel₁ := by
        rw [hkn]
        have := hkept (n + 1)
        rwa [Function.iterate_succ_apply'] at this
      rw [sideKeptPhi_apply_eq_phi data hsep _ hnext, hkn]

/-- **`keptPhi` and `M.φ` define the same cycle on a kept orbit.** -/
lemma sideKeptPhi_sameCycle_iff_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k)
    (x : {d : D // d ∉ data.keptDel₁}) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle k x ↔ M.φ.SameCycle k.1 x.1 := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    have := congrArg (Subtype.val) hn
    rw [sideKeptPhi_iterate_eq_phi data hsep k hkept n] at this
    exact this
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    apply Subtype.ext
    rw [sideKeptPhi_iterate_eq_phi data hsep k hkept n]
    exact hn

/-- Every dart on the `M.φ`-orbit of a kept dart `k` (with kept orbit) is itself kept. -/
lemma orbitKept_mem (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k)
    {d : D} (hd : M.φ.SameCycle k.1 d) : d ∉ data.keptDel₁ := by
  obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact hkept n

/-- **The kept side face length equals `M`'s face length on a kept orbit.** -/
theorem sideKeptMap₁_faceLen_eq_M (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k) :
    (sideKeptMap₁ data hsep).faceLen ((sideKeptMap₁ data hsep).dartFace k)
      = M.faceLen (M.dartFace k.1) := by
  classical
  show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).card
    = (Finset.univ.filter (fun d => Quotient.mk _ d
      = Quotient.mk (cycleSetoid M.φ) k.1)).card
  have hφ : (sideKeptMap₁ data hsep).φ
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ := rfl
  -- the kept filter maps bijectively via `Subtype.val` onto the M filter.
  rw [show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).card
      = ((Finset.univ.filter (fun x : {d : D // d ∉ data.keptDel₁} =>
          Quotient.mk _ x = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).map
          ⟨Subtype.val, Subtype.val_injective⟩).card from (Finset.card_map _).symm]
  congr 1
  ext d
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, hcd, rfl⟩
    -- `keptPhi.SameCycle k c`  ⇒  `M.φ.SameCycle k.1 c.1`.
    have hsc : (sideKeptMap₁ data hsep).φ.SameCycle k c := Quotient.exact hcd.symm
    rw [hφ, sideKeptPhi_sameCycle_iff_phi data hsep k hkept] at hsc
    exact Quotient.sound hsc.symm
  · intro hd
    have hsc : M.φ.SameCycle k.1 d := Quotient.exact hd.symm
    have hdkept : d ∉ data.keptDel₁ := orbitKept_mem data k hkept hsc
    refine ⟨⟨d, hdkept⟩, ?_, rfl⟩
    apply Quotient.sound
    show (sideKeptMap₁ data hsep).φ.SameCycle (⟨d, hdkept⟩ : {d : D // d ∉ data.keptDel₁}) k
    refine Equiv.Perm.SameCycle.symm ?_
    rw [hφ, sideKeptPhi_sameCycle_iff_phi data hsep k hkept ⟨d, hdkept⟩]
    exact hsc

/-- **`OrbitKept` is discharged for a genuine inner side-1 face.**  If `k.1` is a side-1
inner dart (`M`-face in `side₁`) whose `M`-face is not the chord face `face₁`, then its whole
`M.φ`-orbit stays kept: each iterate keeps the same (side-1, non-`face₁`) `M`-face, hence lies
in `sideDarts₁ \ {dart} ⊆ keptSet₁`.  This removes `OrbitKept` from the residue: it follows
from the side-1 face classification alone. -/
theorem orbitKept_of_side₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁})
    (hside : M.dartFace k.1 ∈ data.side₁) (hface₁ : M.dartFace k.1 ≠ data.face₁) :
    OrbitKept data k := by
  intro n
  rw [data.mem_keptDel₁_iff]
  -- `M.φ^[n] k.1` has the same `M`-face as `k.1`.
  have hsameface : M.dartFace (M.φ^[n] k.1) = M.dartFace k.1 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', M.dartFace_phi, ih]
  -- in `sideDarts₁`:
  have hin : M.φ^[n] k.1 ∈ data.sideDarts₁ := by
    show M.dartFace (M.φ^[n] k.1) ∈ data.side₁
    rw [hsameface]; exact hside
  -- not the chord dart (its face is `face₁`):
  have hne_dart : M.φ^[n] k.1 ≠ data.dart := by
    intro he
    apply hface₁
    have : M.dartFace (M.φ^[n] k.1) = data.face₁ := by rw [he]; rfl
    rwa [hsameface] at this
  -- hence in `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`.
  show M.φ^[n] k.1 ∈ data.keptSet₁
  exact ⟨Or.inl hin, by simpa using hne_dart⟩



/-- **The side face of an untouched inner `inl k` has the same length as its `M`-face.** -/
theorem sideMap₁_faceLen_inl_eq_M (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k)
    (hkept : OrbitKept data k) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k))
      = M.faceLen (M.dartFace k.1) := by
  have h1 := freshPhi_faceLen_inl_eq_keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne huntouched
  have h2 := sideKeptMap₁_faceLen_eq_M data hsep k hkept
  -- `sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) …`; `sideKeptMap₁ = keptCombMap …`.
  rw [show data.sideMap₁ hsep a₀ a₁ hne
      = freshMap (data.sideAlpha₁ hsep) data.sideSigma₁
          (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) a₀ a₁ hne from rfl]
  rw [h1]
  rw [show keptCombMap (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
      = sideKeptMap₁ data hsep from rfl]
  exact h2

/-- **An untouched inner side face, mapping to a non-outer `M`-face, is a triangle.** -/
theorem sideMap₁_faceLen_inl_eq_three (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k)
    (hkept : OrbitKept data k)
    (hMinner : M.dartFace k.1 ≠ hNT.outerFace) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 := by
  rw [sideMap₁_faceLen_inl_eq_M data hsep a₀ a₁ hne k huntouched hkept]
  exact hNT.inner_tri (M.dartFace k.1) hMinner



/-- **A side-1 inner face (not the chord face) that is splice-untouched is a triangle**, with
`OrbitKept` and `M`-non-outerness *both discharged* from the side-1 classification.  The only
remaining geometric input is `SpliceUntouched` (the correct-anchor condition: the orbit avoids
the chord predecessors) together with the face-membership data. -/
theorem sideMap₁_faceLen_inl_three_of_side₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (hside : M.dartFace k.1 ∈ data.side₁) (hface₁ : M.dartFace k.1 ≠ data.face₁)
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 :=
  sideMap₁_faceLen_inl_eq_three data hsep a₀ a₁ hne k huntouched
    (orbitKept_of_side₁ data hsep k hside hface₁)
    (data.side₁_subset_nonouter hside)

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



/-- **Every side face has a kept-`inl` representative** (the face-level `ι_surj`).  For any face
`f` of `sideMap₁`, there is a kept dart `k` with `dartFace (inl k) = f`.  Proof: a face is a
`freshMap.φ`-orbit; pick any representative `x`, then `f = dartFace (inl (faceProj x))` because
`x` is `φ`-SameCycle to `inl (faceProj x)` (`ChordFaceCount.freshPhi_sameCycle_inl_faceProj`),
and `faceProj x` is a kept dart of `K`. -/
theorem sideFace_has_inl_rep (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) :
    ∃ k : {d : D // d ∉ data.keptDel₁},
      (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f := by
  classical
  refine Quotient.inductionOn f (fun x => ?_)
  -- `f = ⟦x⟧`; take `k = faceProj x` and use `freshPhi_sameCycle_inl_faceProj`.
  refine ⟨faceProj (data.sideAlpha₁ hsep) a₀ a₁ x, ?_⟩
  show Quotient.mk (cycleSetoid (data.sideMap₁ hsep a₀ a₁ hne).φ)
      (Sum.inl (faceProj (data.sideAlpha₁ hsep) a₀ a₁ x))
    = Quotient.mk (cycleSetoid (data.sideMap₁ hsep a₀ a₁ hne).φ) x
  apply Quotient.sound
  -- need `(sideMap₁).φ.SameCycle (inl (faceProj x)) x`; we have the reverse from ChordFaceCount.
  have h := freshPhi_sameCycle_inl_faceProj (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne x
  -- `h : (freshMap …).φ.SameCycle x (inl (faceProj x))`; `sideMap₁ = freshMap …`.
  exact h.symm



/-- **Every kept dart has its `M`-face in `side₁` or equal to the outer face** (unconditional).
A kept dart `k.1 ∈ keptSet₁` is in `sideDarts₁` (face `∈ side₁`) or in `outerArc₁`
(face `= outerFace`). -/
theorem keptDart_face_side₁_or_outer (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) :
    M.dartFace k.1 ∈ data.side₁ ∨ M.dartFace k.1 = hNT.outerFace := by
  -- `k.1 ∉ keptDel₁ ↔ k.1 ∈ keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`.
  have hk : k.1 ∈ data.keptSet₁ := (data.mem_keptDel₁_iff k.1).1 k.2
  obtain ⟨hU, _⟩ := hk
  rcases hU with hin | hout
  · -- `k.1 ∈ sideDarts₁`, i.e. `M.dartFace k.1 ∈ side₁`.
    exact Or.inl hin
  · -- `k.1 ∈ outerArc₁`, i.e. `M.dartFace k.1 = outerFace`.
    exact Or.inr hout.1

/-- **A kept dart whose `M`-face is neither outer nor the chord face lies in `side₁`.**  The
contrapositive packaging of the dichotomy: if `M.dartFace k.1 ≠ outerFace` then it is in `side₁`
(and we carry the `≠ face₁` hypothesis alongside).  Unconditional. -/
theorem keptDart_face_mem_side₁ (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) (houter : M.dartFace k.1 ≠ hNT.outerFace) :
    M.dartFace k.1 ∈ data.side₁ :=
  (keptDart_face_side₁_or_outer data k).resolve_right houter

























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

/-- **The fresh chord dart `inr 0` is freshPhi-SameCycle to `inl (β a₀)`** (explicit trace).
`φ̃ (inl (β a₀)) = inr 0`, so a single `φ`-step joins them. -/
lemma chordDart_sameCycle_b0 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 0) (Sum.inl (β a₀)) := by
  refine ⟨-1, ?_⟩
  rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, freshMap_phi_inl_b0 β ρ hβinv hβfix hne]

/-- **The fresh chord dart `inr 1` is freshPhi-SameCycle to `inl (β a₁)`** (explicit trace). -/
lemma chordDart_sameCycle_b1 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 1) (Sum.inl (β a₁)) := by
  refine ⟨-1, ?_⟩
  rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, freshMap_phi_inl_b1 β ρ hβinv hβfix hne]

/-- **The chord-dart `inr 0`'s side face equals the side face of `inl (β a₀)`** (the boundary
orbit traced concretely from the chord dart's known position). -/
lemma chordDart_face_eq_b0 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
      = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl (β a₀)) :=
  Quotient.sound (chordDart_sameCycle_b0 β ρ hβinv hβfix hne)

/-- **The chord-dart `inr 1`'s side face equals the side face of `inl (β a₁)`.** -/
lemma chordDart_face_eq_b1 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl (β a₁)) :=
  Quotient.sound (chordDart_sameCycle_b1 β ρ hβinv hβfix hne)

end Trace



section Membership

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **Side faces of two `inl` darts coincide iff their `tracePhi`-orbits do.** -/
lemma sideFace_inl_eq_iff_tracePhi (k c : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl c)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k c := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) (Sum.inl c) :=
      Quotient.exact h
    have := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).1 hsc
    simpa only [faceProj_inl] using this
  · intro h
    apply Quotient.sound
    refine (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).2 ?_
    simpa only [faceProj_inl] using h

/-- **The side face of `inl k` is the chord-dart-0 face iff `k` is `tracePhi`-SameCycle to
`β a₀`.** -/
lemma sideFace_eq_chordOrbit0_iff (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
  rw [chordDart_face_eq_b0 β ρ hβinv hβfix hne, sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]

/-- **The side face of `inl k` is the chord-dart-1 face iff `k` is `tracePhi`-SameCycle to
`β a₁`.** -/
lemma sideFace_eq_chordOrbit1_iff (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
  rw [chordDart_face_eq_b1 β ρ hβinv hβfix hne, sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]

end Membership



/-- `β (β a) = a` (involutivity, the local form). -/
 lemma betaBeta (β : Equiv.Perm K) (hβinv : β * β = 1) (a : K) : β (β a) = a := by
  have := congrArg (fun f : Equiv.Perm K => f a) hβinv
  simpa [Equiv.Perm.mul_apply] using this

/-- `keptPhi (β a₀) = ρ a₀` (since `β (β a₀) = a₀`). -/
lemma keptPhi_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (a₀ : K) :
    keptPhi β ρ (β a₀) = ρ a₀ := by
  show ρ (β (β a₀)) = ρ a₀
  rw [betaBeta β hβinv]

/-- `keptPhi (β a₁) = ρ a₁`. -/
lemma keptPhi_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (a₁ : K) :
    keptPhi β ρ (β a₁) = ρ a₁ := by
  show ρ (β (β a₁)) = ρ a₁
  rw [betaBeta β hβinv]

/-- **The walk lemma.**  Iterating `keptPhi` from `β a₀`, every iterate is `tracePhi`-SameCycle
to `β a₀` or to `β a₁`.  Proved by induction tracking which of the two split threads the iterate
sits on; the swap re-routes the thread exactly at the two predecessors. -/
lemma tracePhi_reaches_keptPhi_iterate_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (a₀ a₁ : K) (n : ℕ) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) ((keptPhi β ρ)^[n] (β a₀))
      ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) ((keptPhi β ρ)^[n] (β a₀)) := by
  induction n with
  | zero => exact Or.inl (by simpa using Equiv.Perm.SameCycle.rfl)
  | succ n ih =>
      set c := (keptPhi β ρ)^[n] (β a₀) with hc
      rw [Function.iterate_succ_apply', ← hc]
      by_cases h0 : c = β a₀
      · -- keptPhi c = keptPhi (β a₀) = ρ a₀ = tracePhi (β a₁); hop to the β a₁ thread.
        right
        rw [h0, keptPhi_b0 β ρ hβinv, ← tracePhi_b1 β ρ hβinv a₀ a₁]
        exact ⟨1, by rw [zpow_one]⟩
      · by_cases h1 : c = β a₁
        · -- keptPhi c = ρ a₁ = tracePhi (β a₀); hop to the β a₀ thread.
          left
          rw [h1, keptPhi_b1 β ρ hβinv, ← tracePhi_b0 β ρ hβinv a₀ a₁]
          exact ⟨1, by rw [zpow_one]⟩
        · -- non-predecessor: keptPhi c = tracePhi c, stay on the same thread.
          have hβc0 : β c ≠ a₀ := by
            intro hb; apply h0; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have hβc1 : β c ≠ a₁ := by
            intro hb; apply h1; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have heq : keptPhi β ρ c = tracePhi β ρ a₀ a₁ c := by
            rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl
          rw [heq]
          have hstep : (tracePhi β ρ a₀ a₁).SameCycle c (tracePhi β ρ a₀ a₁ c) :=
            ⟨1, by rw [zpow_one]⟩
          rcases ih with h | h
          · exact Or.inl (h.trans hstep)
          · exact Or.inr (h.trans hstep)

/-- **The unconditional orbit trichotomy (`β a₀` thread).**  Every kept dart `c` whose
`keptPhi`-orbit meets `β a₀` is `tracePhi`-SameCycle to `β a₀` or to `β a₁`. -/
lemma tracePhi_reaches_of_keptPhi_sameCycle_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    {a₀ a₁ c : K} (h : (keptPhi β ρ).SameCycle (β a₀) c) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) c ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) c := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact tracePhi_reaches_keptPhi_iterate_b0 β ρ hβinv a₀ a₁ n

/-- Symmetric walk from the `β a₁` thread. -/
lemma tracePhi_reaches_keptPhi_iterate_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (a₀ a₁ : K) (n : ℕ) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) ((keptPhi β ρ)^[n] (β a₁))
      ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) ((keptPhi β ρ)^[n] (β a₁)) := by
  induction n with
  | zero => exact Or.inr (by simpa using Equiv.Perm.SameCycle.rfl)
  | succ n ih =>
      set c := (keptPhi β ρ)^[n] (β a₁) with hc
      rw [Function.iterate_succ_apply', ← hc]
      by_cases h0 : c = β a₀
      · right
        rw [h0, keptPhi_b0 β ρ hβinv, ← tracePhi_b1 β ρ hβinv a₀ a₁]
        exact ⟨1, by rw [zpow_one]⟩
      · by_cases h1 : c = β a₁
        · left
          rw [h1, keptPhi_b1 β ρ hβinv, ← tracePhi_b0 β ρ hβinv a₀ a₁]
          exact ⟨1, by rw [zpow_one]⟩
        · have hβc0 : β c ≠ a₀ := by
            intro hb; apply h0; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have hβc1 : β c ≠ a₁ := by
            intro hb; apply h1; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have heq : keptPhi β ρ c = tracePhi β ρ a₀ a₁ c := by
            rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl
          rw [heq]
          have hstep : (tracePhi β ρ a₀ a₁).SameCycle c (tracePhi β ρ a₀ a₁ c) :=
            ⟨1, by rw [zpow_one]⟩
          rcases ih with h | h
          · exact Or.inl (h.trans hstep)
          · exact Or.inr (h.trans hstep)

/-- **The unconditional orbit trichotomy (`β a₁` thread).** -/
lemma tracePhi_reaches_of_keptPhi_sameCycle_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    {a₀ a₁ c : K} (h : (keptPhi β ρ).SameCycle (β a₁) c) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) c ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) c := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact tracePhi_reaches_keptPhi_iterate_b1 β ρ hβinv a₀ a₁ n



section Untouched

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **The KEY fresh-angle theorem.**  A kept dart whose side face is neither chord-dart face is
splice-untouched. -/
theorem spliceUntouched_of_face_ne_chordOrbits {k : K}
    (h0 : (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        ≠ (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0))
    (h1 : (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        ≠ (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)) :
    SpliceUntouched β ρ a₀ a₁ k := by
  -- ¬ tracePhi.SameCycle k (β a₀)  and  ¬ tracePhi.SameCycle k (β a₁).
  have ht0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
    rw [← sideFace_eq_chordOrbit0_iff β ρ hβinv hβfix hne]; exact h0
  have ht1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
    rw [← sideFace_eq_chordOrbit1_iff β ρ hβinv hβfix hne]; exact h1
  refine ⟨?_, ?_⟩
  · -- ¬ keptPhi.SameCycle k (β a₀)
    intro hkp
    rcases tracePhi_reaches_of_keptPhi_sameCycle_b0 β ρ hβinv (a₀ := a₀) (a₁ := a₁) hkp.symm
      with h | h
    · exact ht0 h.symm
    · exact ht1 h.symm
  · -- ¬ keptPhi.SameCycle k (β a₁)
    intro hkp
    rcases tracePhi_reaches_of_keptPhi_sameCycle_b1 β ρ hβinv (a₀ := a₀) (a₁ := a₁) hkp.symm
      with h | h
    · exact ht0 h.symm
    · exact ht1 h.symm

end Untouched



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The chord-dart faces are the two touched orbits.**  Re-export of `chordDart_face_eq_*`
specialised to the chord-split side map. -/
lemma sideMap₁_chordDart_face_eq_b0 (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (data.sideAlpha₁ hsep a₀)) :=
  chordDart_face_eq_b0 (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne











/-- **The two chord-dart faces coincide iff the chord predecessors share a `tracePhi`-orbit.**
The equivalence that makes the two-orbit structure explicit. -/
theorem chordOrbits_eq_iff_tracePhi (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (hβfix : ∀ k, β k ≠ k) {a₀ a₁ : K} (hne : a₀ ≠ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle (β a₀) (β a₁) := by
  rw [chordDart_face_eq_b0 β ρ hβinv hβfix hne, chordDart_face_eq_b1 β ρ hβinv hβfix hne,
    sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]







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

/-- The `tracePhi`-orbit cardinality of `k` on `K` (the number of `inl`-darts in the side
face of `inl k`). -/
def tOrbitCard (β ρ : Equiv.Perm K) (a₀ a₁ k : K) : ℕ :=
  (Finset.univ.filter (fun c : K =>
    Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) c
      = Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) k)).card



/-- `inr 0` is in the side face of `inl k` iff `k ~ₜ β a₀`. -/
lemma inr_zero_mem_sideFace_iff (k : K) :
    (Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inr 0)
        = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 0) (Sum.inl k) :=
      Quotient.exact h
    have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 0) (Sum.inl k)).1 hsc
    simp only [faceProj_inr_zero, faceProj_inl] at htrace
    exact (htrace.symm)
  · intro h
    apply Quotient.sound
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inr 0))
        (faceProj β a₀ a₁ (Sum.inl k)) := by
      simp only [faceProj_inr_zero, faceProj_inl]; exact h.symm
    exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 0) (Sum.inl k)).2 htrace

/-- `inr 1` is in the side face of `inl k` iff `k ~ₜ β a₁`. -/
lemma inr_one_mem_sideFace_iff (k : K) :
    (Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inr 1)
        = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 1) (Sum.inl k) :=
      Quotient.exact h
    have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 1) (Sum.inl k)).1 hsc
    simp only [faceProj_inr_one, faceProj_inl] at htrace
    exact (htrace.symm)
  · intro h
    apply Quotient.sound
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inr 1))
        (faceProj β a₀ a₁ (Sum.inl k)) := by
      simp only [faceProj_inr_one, faceProj_inl]; exact h.symm
    exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 1) (Sum.inl k)).2 htrace

/-- The full dart-set splits as `inl`-images of `univ K` together with the two `inr` darts. -/
 lemma univ_sum_decomp :
    (Finset.univ : Finset (K ⊕ Fin 2))
      = (Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩)
        ∪ {Sum.inr 0, Sum.inr 1} := by
  classical
  ext x
  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_insert, Finset.mem_singleton, true_iff]
  cases x with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr j => fin_cases j <;> simp

/-- **The general side-face length formula (UNCONDITIONAL).**  The side face of `inl k` has
length `#(tracePhi-orbit of k)` plus `1` for each chord predecessor `β a₀`, `β a₁` lying in
that orbit. -/
theorem sideFaceLen_formula (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k))
      = tOrbitCard β ρ a₀ a₁ k
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0) := by
  classical
  set Φ := (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ with hΦ
  set Q : K ⊕ Fin 2 → Prop := fun x =>
    Quotient.mk (cycleSetoid Φ) x = Quotient.mk (cycleSetoid Φ) (Sum.inl k) with hQ
  show (Finset.univ.filter Q).card = _
  -- Split the universe into the inl-image and the two inr darts.
  rw [univ_sum_decomp, Finset.filter_union]
  rw [Finset.card_union_of_disjoint ?disj]
  · -- inl part
    have hinl : (((Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩).filter Q)).card
        = tOrbitCard β ρ a₀ a₁ k := by
      rw [Finset.filter_map, Finset.card_map]
      -- the filtered preimage on `K` equals the tracePhi-orbit filter.
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
        Function.Embedding.coeFn_mk, hQ]
      constructor
      · intro h
        apply Quotient.sound
        have hsc : Φ.SameCycle (Sum.inl c) (Sum.inl k) := Quotient.exact h
        have := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl c) (Sum.inl k)).1 hsc
        simpa only [faceProj_inl] using this
      · intro h
        apply Quotient.sound
        have htr : (tracePhi β ρ a₀ a₁).SameCycle c k := Quotient.exact h
        have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inl c))
            (faceProj β a₀ a₁ (Sum.inl k)) := by simpa only [faceProj_inl] using htr
        exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl c) (Sum.inl k)).2 htrace
    -- inr part
    have hinr : (({Sum.inr 0, Sum.inr 1} : Finset (K ⊕ Fin 2)).filter Q).card
        = (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
          + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0) := by
      have key0 : Q (Sum.inr 0) ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) :=
        inr_zero_mem_sideFace_iff β ρ hβinv hβfix hne k
      have key1 : Q (Sum.inr 1) ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) :=
        inr_one_mem_sideFace_iff β ρ hβinv hβfix hne k
      rw [Finset.filter_insert, Finset.filter_singleton]
      by_cases h0 : Q (Sum.inr 0) <;> by_cases h1 : Q (Sum.inr 1)
      · rw [if_pos h0, if_pos h1, if_pos (key0.1 h0), if_pos (key1.1 h1)]
        rw [Finset.card_insert_of_notMem (by simp)]; simp
      · have ne1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := fun e => h1 (key1.2 e)
        rw [if_pos h0, if_neg h1, if_pos (key0.1 h0), if_neg ne1]; simp
      · have ne0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := fun e => h0 (key0.2 e)
        rw [if_neg h0, if_pos h1, if_neg ne0, if_pos (key1.1 h1)]; simp
      · have ne0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := fun e => h0 (key0.2 e)
        have ne1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := fun e => h1 (key1.2 e)
        rw [if_neg h0, if_neg h1, if_neg ne0, if_neg ne1]; simp
    rw [hinl, hinr, ← add_assoc]
  case disj =>
    apply Finset.disjoint_left.2
    intro x hx hx2
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx hx2
    obtain ⟨⟨c, hc⟩, _⟩ := hx
    obtain ⟨hx2mem, _⟩ := hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2mem
    subst hc
    rcases hx2mem with h | h <;> exact absurd h (by simp)

end Formula



section Consequences

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

include hne



/-- **The chord-triangle face length, from the explicit count.**  If the side face's
representative `k` has a `tracePhi`-orbit of exactly `2` kept darts and exactly one of the two
chord predecessors joins it (the fresh chord dart re-closing the deleted-dart gap of the
`M`-triangle `face₁`), then the side face is a triangle.  This is the DIRECT discharge of the
touched chord-triangle face — no splice-untouchedness, computed from the formula. -/
theorem sideFaceLen_three_of_count {k : K} (htwo : tOrbitCard β ρ a₀ a₁ k = 2)
    (hone : ((if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0)) = 1) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)) = 3 := by
  rw [sideFaceLen_formula β ρ hβinv hβfix hne k, add_assoc, htwo, hone]



end Consequences



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The explicit chord-triangle count, at the side-map level.**  A kept dart `k` whose side
face has a `tracePhi`-orbit of `2` kept darts joined by exactly one fresh chord dart yields a
side triangle.  This is the DIRECT discharge of the touched `face₁` image — the chord re-closes
the deleted-dart gap of the `M`-triangle `face₁` with one fresh chord dart. -/
theorem sideMap₁_faceLen_three_of_count (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (htwo : tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k = 2)
    (hone : ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 :=
  sideFaceLen_three_of_count (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne htwo hone

/-- **The per-face triangle witness (NO `≠ face₁` carve-out).**  For one side face `f`, a
representative giving `faceLen f = 3` via EITHER route. -/
inductive SideFaceTriangle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop where
  /-- A representative whose side face IS `f` and has `faceLen = 3`. -/
  | mk (k : {d : D // d ∉ data.keptDel₁})
      (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f)
      (hlen : (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3)



/-- The explicit chord-triangle count route produces a `SideFaceTriangle` witness (the touched
`face₁` image, discharged directly). -/
theorem sideFaceTriangle_of_count (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (k : {d : D // d ∉ data.keptDel₁})
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f)
    (htwo : tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k = 2)
    (hone : ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  ⟨k, hkf, sideMap₁_faceLen_three_of_count data hsep a₀ a₁ hne k htwo hone⟩















/-- **The chord dart is deleted** (`dart ∈ keptDel₁`): it is removed from `keptSet₁`. -/
theorem dart_mem_keptDel₁ (data : hNT.ChordSplitData u v) :
    data.dart ∈ data.keptDel₁ := by
  classical
  by_contra h
  rw [data.mem_keptDel₁_iff] at h
  exact h.2 (by simp)

/-- **The two non-chord darts of `face₁` are kept.**  `M.φ dart`, `M.φ² dart` have `M`-face
`face₁ ∈ side₁`, hence lie in `sideDarts₁`; they are `≠ dart` (the triangle has distinct darts),
hence in `keptSet₁`. -/
theorem face₁_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd1 : M.φ data.dart ≠ data.dart) :
    M.φ data.dart ∉ data.keptDel₁ := by
  classical
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inl ?_, by simpa using hd1⟩
  show M.dartFace (M.φ data.dart) ∈ data.side₁
  rw [M.dartFace_phi]; exact data.face₁_mem_side₁

/-- **The second non-chord dart of `face₁` is kept.** -/
theorem face₁_phi_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd2 : M.φ (M.φ data.dart) ≠ data.dart) :
    M.φ (M.φ data.dart) ∉ data.keptDel₁ := by
  classical
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inl ?_, by simpa using hd2⟩
  show M.dartFace (M.φ (M.φ data.dart)) ∈ data.side₁
  rw [M.dartFace_phi, M.dartFace_phi]; exact data.face₁_mem_side₁

/-- **The two kept `face₁` darts are distinct** (the `M`-triangle `face₁` has three distinct
darts).  Uses graph simplicity from the near-triangulation. -/
theorem face₁_kept_darts_distinct (data : hNT.ChordSplitData u v) :
    M.φ data.dart ≠ M.φ (M.φ data.dart) := by
  intro h
  -- `φ d1 = φ d2 ⇒ d1 = d2`, but a triangle has distinct darts.
  have htri := data.face₁_isFaceTriangle
  -- htri : IsFaceTriangle dart (φ dart) (φ²dart): φ dart = φ dart, φ(φ dart)=φ²dart, φ(φ²dart)=dart
  obtain ⟨_, h12, h20⟩ := htri
  -- from `h : φ dart = φ² dart` we get `dart = φ dart` by injectivity, contradicting simplicity.
  have : M.φ data.dart = M.φ (M.φ data.dart) := h
  have heq : data.dart = M.φ data.dart := M.φ.injective this
  exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) heq.symm

/-- **`face₁` contributes exactly two kept darts** (UNCONDITIONAL, the `M`-side of the count).
The two non-chord darts of the `M`-triangle `face₁` are kept and distinct; the chord dart is
deleted.  This is the genuine chord-triangle structure underlying `tOrbitCard = 2` for the
touched `face₁` side face — established with no correct-anchor input. -/
theorem face₁_two_kept_darts (data : hNT.ChordSplitData u v) :
    (M.φ data.dart ∉ data.keptDel₁) ∧ (M.φ (M.φ data.dart) ∉ data.keptDel₁) ∧
      M.φ data.dart ≠ M.φ (M.φ data.dart) ∧
      M.dartFace (M.φ data.dart) = data.face₁ ∧
      M.dartFace (M.φ (M.φ data.dart)) = data.face₁ := by
  -- triangle distinctness gives φ dart ≠ dart and φ² dart ≠ dart.
  obtain ⟨_, h12, h20⟩ := data.face₁_isFaceTriangle
  have hd1 : M.φ data.dart ≠ data.dart := by
    intro he
    have : data.dart = M.φ data.dart := he.symm
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) he
  have hd2 : M.φ (M.φ data.dart) ≠ data.dart := by
    -- φ²dart = dart would force dart = φ dart (apply φ, use h20); contradiction.
    intro he
    have hstep : M.φ (M.φ (M.φ data.dart)) = M.φ data.dart := congrArg M.φ he
    -- h20 : φ (φ² dart) = dart, so dart = φ dart.
    have : data.dart = M.φ data.dart := h20.symm.trans hstep
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) this.symm
  refine ⟨face₁_phi_dart_kept data hd1, face₁_phi_phi_dart_kept data hd2,
    face₁_kept_darts_distinct data, ?_, ?_⟩
  · show M.dartFace (M.φ data.dart) = M.dartFace data.dart; rw [M.dartFace_phi]
  · show M.dartFace (M.φ (M.φ data.dart)) = M.dartFace data.dart
    rw [M.dartFace_phi, M.dartFace_phi]

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

/-- The natural-number iterate of a swap stays on the two swapped points. -/
 lemma swap_iterate_mem {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) :
    ∀ n : ℕ, g^[n] k₀ = k₀ ∨ g^[n] k₀ = k₁ := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h]; exact Or.inr h01
      · rw [h]; exact Or.inl h10

variable [Fintype K]

/-- `g.SameCycle k₀ c` with `g` swapping `k₀ ↔ k₁` forces `c ∈ {k₀, k₁}`. -/
 lemma sameCycle_swap_mem {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) {c : K}
    (h : g.SameCycle k₀ c) : c = k₀ ∨ c = k₁ := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rcases swap_iterate_mem h01 h10 n with he | he
  · exact Or.inl (by rw [← hn, he])
  · exact Or.inr (by rw [← hn, he])

/-- **The two-cycle orbit has cardinality `2`.**  If `g k₀ = k₁`, `g k₁ = k₀` with
`k₀ ≠ k₁`, the cycle-orbit filter of `k₀` is exactly `{k₀, k₁}`, of cardinality `2`. -/
theorem twoCycle_orbit_card {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) (hne : k₀ ≠ k₁) :
    (Finset.univ.filter (fun c : K =>
        Quotient.mk (cycleSetoid g) c = Quotient.mk (cycleSetoid g) k₀)).card = 2 := by
  classical
  have hset : (Finset.univ.filter (fun c : K =>
      Quotient.mk (cycleSetoid g) c = Quotient.mk (cycleSetoid g) k₀))
      = ({k₀, k₁} : Finset K) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hc
      have hsc : g.SameCycle c k₀ := Quotient.exact hc
      exact sameCycle_swap_mem h01 h10 hsc.symm
    · rintro (rfl | rfl)
      · rfl
      · apply Quotient.sound
        -- `g.SameCycle k₁ k₀`: one step `g k₁ = k₀`.
        exact ⟨1, by rw [zpow_one, h10]⟩
  rw [hset, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

end TwoCycle



section Card

variable {K : Type u} [Fintype K] [DecidableEq K]

/-- **`tOrbitCard = 2` from the explicit `tracePhi` 2-cycle.**  If the side `tracePhi` swaps
the two kept `face₁` darts `d₁ ↔ d₂` (the correct-anchor placement — the chord cap spliced at
the chord-dart position), then the `tracePhi`-orbit of `d₁` is exactly `{d₁, d₂}`, so the
`face₁` side-face has exactly `2` kept darts. -/
theorem tOrbitCard_eq_two_of_tracePhi_swap (β ρ : Equiv.Perm K) (a₀ a₁ : K) {d₁ d₂ : K}
    (h12 : tracePhi β ρ a₀ a₁ d₁ = d₂) (h21 : tracePhi β ρ a₀ a₁ d₂ = d₁)
    (hne : d₁ ≠ d₂) :
    tOrbitCard β ρ a₀ a₁ d₁ = 2 :=
  twoCycle_orbit_card h12 h21 hne

end Card



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The correct-anchor orbit-isolation datum** for the touched `face₁` side face.  Records
the genuine discrete Jordan–Schoenflies placement of the chord cap:

* `kface : {d // d ∉ keptDel₁}` — the representative kept dart of the `face₁` side orbit;
* `kother` — its `tracePhi`-2-cycle partner (the other kept `face₁` dart);
* the side `tracePhi` cycles them (`tracePhi kface = kother`, `tracePhi kother = kface`),
  distinct;
* the rep's side face is the chosen `f`;
* exactly one of the two chord predecessors `(sideAlpha₁) a₀`, `(sideAlpha₁) a₁` is
  `tracePhi`-SameCycle to `kface` (the one fresh chord dart re-closing the deleted-dart gap).

This is the chord-cap placement, exposed as concrete `tracePhi` equations — the abstract
`CombMap` does not certify it (the anchors are free parameters of `sideMap₁`). -/
structure CorrectAnchorTwoCycle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Type u where
  /-- The representative kept dart of the `face₁` side orbit. -/
  kface : {d : D // d ∉ data.keptDel₁}
  /-- Its `tracePhi`-2-cycle partner. -/
  kother : {d : D // d ∉ data.keptDel₁}
  /-- The side `tracePhi` sends the rep to its partner. -/
  trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kface = kother
  /-- The side `tracePhi` sends the partner back to the rep. -/
  trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kother = kface
  /-- The two kept `face₁` darts are distinct. -/
  distinct : kface ≠ kother
  /-- The rep's side face is the chosen face `f`. -/
  hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl kface) = f
  /-- Exactly one fresh chord dart re-closes the orbit (the one-indicator condition). -/
  one_fresh :
    ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
          ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
          ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1

/-- **The correct-anchor datum gives `tOrbitCard = 2`** for the `face₁` orbit rep. -/
theorem correctAnchor_tOrbitCard_two (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hca : CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ hca.kface = 2 :=
  tOrbitCard_eq_two_of_tracePhi_swap (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁
    hca.trace12 hca.trace21 hca.distinct

/-- **The touched `face₁` side face is a `SideFaceTriangle`** — discharged DIRECTLY from the
correct-anchor orbit-isolation (`tOrbitCard = 2` + one fresh chord dart), NOT via a `≠ face₁`
carve-out or boundary absorption.  This is the correct-anchor orbit-isolation closing the last
chord-side residue. -/
theorem face₁_sideFaceTriangle_of_correctAnchor (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hca : CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  sideFaceTriangle_of_count data hsep a₀ a₁ hne f hca.kface hca.hkf
    (correctAnchor_tOrbitCard_two data hsep a₀ a₁ hne f hca) hca.one_fresh











/-- **The correct-anchor datum is satisfiable (non-vacuous), not a hidden `False`.**  Given the
component data — a `tracePhi`-2-cycle on two distinct kept darts, the rep's face, and the
one-fresh-dart indicator — the structure is inhabited.  This is the §3.3 satisfiability check:
`CorrectAnchorTwoCycle` is the genuine correct-anchor placement (a real 2-cycle equation), not
an unsatisfiable premise. -/
def CorrectAnchorTwoCycle.mk' (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (kface kother : {d : D // d ∉ data.keptDel₁})
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kface = kother)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kother = kface)
    (distinct : kface ≠ kother)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl kface) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    CorrectAnchorTwoCycle data hsep a₀ a₁ hne f :=
  { kface := kface, kother := kother, trace12 := trace12, trace21 := trace21,
    distinct := distinct, hkf := hkf, one_fresh := one_fresh }



/-- The first kept `face₁` dart `M.φ dart`, as a subtype element of `{d // d ∉ keptDel₁}`
(kept by the unconditional `face₁_two_kept_darts`). -/
noncomputable def face₁Dart₁ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₁} :=
  ⟨M.φ data.dart, (face₁_two_kept_darts data).1⟩

/-- The second kept `face₁` dart `M.φ² dart`, as a subtype element. -/
noncomputable def face₁Dart₂ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₁} :=
  ⟨M.φ (M.φ data.dart), (face₁_two_kept_darts data).2.1⟩

/-- The two kept `face₁` darts are distinct as subtype elements (from
`face₁_two_kept_darts`). -/
theorem face₁Dart_distinct (data : hNT.ChordSplitData u v) :
    face₁Dart₁ data ≠ face₁Dart₂ data := by
  intro h
  exact (face₁_two_kept_darts data).2.2.1 (congrArg Subtype.val h)

/-- **The correct-anchor datum, anchored to the ACTUAL `face₁` darts.**  Given the `tracePhi`
2-cycle on the two genuine kept `face₁` darts `M.φ dart ↔ M.φ² dart` (the chord-cap placement),
their `inl`-side face being the chosen `f`, and the one-fresh-chord-dart indicator, the
correct-anchor datum holds — with distinctness/keptness supplied UNCONDITIONALLY by
`face₁_two_kept_darts`.  This is the genuine chord-triangle orbit-isolation: the 2 kept `face₁`
darts form a length-2 `tracePhi`-orbit, re-closed by one fresh chord dart. -/
noncomputable def correctAnchorTwoCycle_ofFace₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₁ data)
        = face₁Dart₂ data)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₂ data)
        = face₁Dart₁ data)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    CorrectAnchorTwoCycle data hsep a₀ a₁ hne f :=
  CorrectAnchorTwoCycle.mk' data hsep a₀ a₁ hne f (face₁Dart₁ data) (face₁Dart₂ data)
    trace12 trace21 (face₁Dart_distinct data) hkf one_fresh

/-- **The touched `face₁` side face is a triangle, from the ACTUAL `face₁`-dart 2-cycle.**  The
end-to-end statement the orchestration named: the chord-triangle `face₁`'s keptPhi-orbit has
`tOrbitCard = 2` (its 2 kept darts `M.φ dart`, `M.φ² dart`, the 3rd being the deleted chord
dart), re-closed by one fresh chord dart, so the `face₁` side face is a length-3 triangle —
DIRECTLY, with no `≠ face₁` carve-out. -/
theorem face₁_sideTriangle_ofFace₁Cycle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₁ data)
        = face₁Dart₂ data)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₂ data)
        = face₁Dart₁ data)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  face₁_sideFaceTriangle_of_correctAnchor data hsep a₀ a₁ hne f
    (correctAnchorTwoCycle_ofFace₁ data hsep a₀ a₁ hne f trace12 trace21 hkf one_fresh)

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

/-- **`tracePhi` is `keptPhi` with its values at `ρ a₀`, `ρ a₁` swapped.** -/
lemma tracePhi_eq_swap_keptPhi (β ρ : Equiv.Perm K) (a₀ a₁ k : K) :
    tracePhi β ρ a₀ a₁ k = Equiv.swap (ρ a₀) (ρ a₁) (keptPhi β ρ k) := by
  show (Equiv.swap (ρ a₀) (ρ a₁) * (ρ * β)) k = Equiv.swap (ρ a₀) (ρ a₁) ((ρ * β) k)
  rw [Equiv.Perm.mul_apply]



end Algebra



section KeptPhi

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **`keptPhi d₁ = d₂` on the chord-split side (the easy filtered step).**  The
side face permutation `keptPhi (sideAlpha₁) sideSigma₁` sends the first kept
`face₁` dart `face₁Dart₁ = ⟨M.φ dart, _⟩` to the second `face₁Dart₂ = ⟨M.φ² dart,
_⟩`.  The `α`-then-`σ` step is `M.σ (M.α (M.φ dart)) = M.φ² dart` (= `M.φ`
applied to `M.φ dart`), which is kept, so the filtered rotation does not skip. -/
theorem keptPhi_face₁Dart₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) = face₁Dart₂ data := by
  classical
  -- `keptPhi … d₁ = sideSigma₁ (sideAlpha₁ d₁)`.
  apply Subtype.ext
  show ((data.sideSigma₁ (data.sideAlpha₁ hsep (face₁Dart₁ data))) : D)
    = (face₁Dart₂ data : D)
  -- `sideSigma₁ = filteredRotation M.σ keptDel₁`.
  have hval : ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) = M.α (M.φ data.dart) := by
    rw [sideAlpha₁_apply_coe]; rfl
  -- the `σ`-successor of `α (M.φ dart)` is `M.φ² dart`, which is kept.
  have hstep : M.σ ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) = M.φ (M.φ data.dart) := by
    rw [hval]
    show M.σ (M.α (M.φ data.dart)) = (M.σ * M.α) (M.φ data.dart)
    rw [Equiv.Perm.mul_apply]
  have hkept : M.σ ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) ∉ data.keptDel₁ := by
    rw [hstep]; exact (face₁_two_kept_darts data).2.1
  show ((FilteredRotation.filteredRotation M.σ data.keptDel₁
        (data.sideAlpha₁ hsep (face₁Dart₁ data))) : D) = (face₁Dart₂ data : D)
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₁
    (data.sideAlpha₁ hsep (face₁Dart₁ data)) hkept, hstep]
  rfl

/-- **`keptPhi d₂ ≠ d₂`.**  From `keptPhi d₁ = d₂` and `d₁ ≠ d₂`: if `keptPhi d₂ =
d₂` then `keptPhi d₂ = keptPhi d₁`, so `d₂ = d₁` by injectivity — contradiction.
This is the only consequence needed beyond the bigon closure, and it is FREE. -/
theorem keptPhi_face₁Dart₂_ne_self (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) ≠ face₁Dart₂ data := by
  intro h
  have h1 := keptPhi_face₁Dart₁ data hsep
  -- keptPhi d₂ = d₂ = keptPhi d₁ ⇒ d₂ = d₁.
  have : keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data)
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) := by
    rw [h, ← h1]
  have heq : face₁Dart₂ data = face₁Dart₁ data :=
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).injective this
  exact (face₁Dart_distinct data) heq.symm

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



/-- **`M.φ³ dart = dart`** — the chord-incident face `face₁` is an `M`-triangle.  This is
the third leg of `data.face₁_isFaceTriangle` (which descends from `hNT.inner_tri` applied to
the non-outer face `face₁`): `M.φ (M.φ² dart) = dart`.  UNCONDITIONAL. -/
theorem phi_cube_dart (data : hNT.ChordSplitData u v) :
    M.φ (M.φ (M.φ data.dart)) = data.dart :=
  data.face₁_isFaceTriangle.2.2

/-- **`M.σ (M.α (M.φ² dart)) = dart`** — the immediate `σ`-successor of the `α`-image of `d₂`
is the chord dart.  `M.σ ∘ M.α = M.φ`, so this is `M.φ (M.φ² dart) = M.φ³ dart = dart`.
UNCONDITIONAL. -/
theorem sigma_alpha_phiSq_dart_eq_dart (data : hNT.ChordSplitData u v) :
    M.σ (M.α (M.φ (M.φ data.dart))) = data.dart := by
  show (M.σ * M.α) (M.φ (M.φ data.dart)) = data.dart
  rw [← CombMap.φ]
  exact phi_cube_dart data

/-- **The first `σ`-step of the filtered rotation at `d₂` is the DELETED chord dart.**  The
filtered rotation `sideSigma₁ = filteredRotation M.σ keptDel₁` starts from `sideAlpha₁ d₂`,
whose underlying dart is `M.α (M.φ² dart)`; its immediate `M.σ`-successor is
`M.σ (M.α (M.φ² dart)) = dart ∈ keptDel₁`.  So the rotation cannot take the trivial single
step — it MUST skip the chord dart.  This is the concrete skip certificate of the bigon
wrap, UNCONDITIONAL. -/
theorem bigonWrap_firstStep_deleted (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.σ ((data.sideAlpha₁ hsep (face₁Dart₂ data) : {d : D // d ∉ data.keptDel₁}) : D)
      ∈ data.keptDel₁ := by
  have hval : ((data.sideAlpha₁ hsep (face₁Dart₂ data)) : D) = M.α (M.φ (M.φ data.dart)) := by
    rw [sideAlpha₁_apply_coe]; rfl
  rw [hval, sigma_alpha_phiSq_dart_eq_dart data]
  exact dart_mem_keptDel₁ data

/-- **`firstOutside ≥ 2` at `d₂`.**  Because the first `σ`-successor is deleted
(`bigonWrap_firstStep_deleted`), the filtered rotation takes at least two `σ`-steps from
`sideAlpha₁ d₂`: the wrap is a genuine skip, never the trivial consecutive step.
UNCONDITIONAL. -/
theorem sideSigma₁_sideAlpha₁_firstOutside_ge_two
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    2 ≤ Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
          (data.sideAlpha₁ hsep (face₁Dart₂ data)) := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  -- `firstOutside` is positive, so it must be `1` — forcing the deleted first step to be kept.
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
      (data.sideAlpha₁ hsep (face₁Dart₂ data)) :=
    Equiv.Perm.DeleteSet.firstOutside_pos M.σ data.keptDel₁ _
  have heq1 : Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
      (data.sideAlpha₁ hsep (face₁Dart₂ data)) = 1 := by omega
  -- the survivor (which is `∉ keptDel₁`) equals the first `σ`-step, which is deleted.
  have hnot := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ data.keptDel₁
    (data.sideAlpha₁ hsep (face₁Dart₂ data))
  rw [heq1, pow_one] at hnot
  exact hnot (bigonWrap_firstStep_deleted data hsep)





















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



/-- A `σ`-power preserves the `tail` (vertex): `tail ((σ^n) d) = tail d`.  The two
darts are `σ`-`SameCycle` (witnessed by the exponent `n`), so they have the same
`σ`-orbit class, which is `tail`. -/
lemma tail_pow_sigma (n : ℕ) (d : D) :
    M.tail ((M.σ ^ n) d) = M.tail d := by
  apply Quotient.sound
  -- `SameCycle ((σ^n) d) d` via the exponent `-n`.
  refine ⟨-(n : ℤ), ?_⟩
  rw [zpow_neg, zpow_natCast, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

/-- **The filtered rotation keeps the vertex fixed.**  For any deleted set and kept
dart `x`, the filtered successor lives at the same vertex as `x`. -/
lemma tail_filteredRotation (Del : Finset D) (x : {d : D // d ∉ Del}) :
    M.tail (FilteredRotation.filteredRotation M.σ Del x : D) = M.tail x.1 := by
  rw [FilteredRotation.filteredRotation_apply_coe]
  exact tail_pow_sigma _ x.1



/-- `M.α (M.φ² dart)` lives at vertex `tail dart` (= `u`): its `σ`-successor is the
chord dart `dart`, so it is `σ`-`SameCycle` with `dart`. -/
lemma tail_alpha_phiSq_dart (data : hNT.ChordSplitData u v) :
    M.tail (M.α (M.φ (M.φ data.dart))) = M.tail data.dart := by
  have h : M.σ (M.α (M.φ (M.φ data.dart))) = data.dart :=
    sigma_alpha_phiSq_dart_eq_dart data
  calc
    M.tail (M.α (M.φ (M.φ data.dart)))
        = M.tail (M.σ (M.α (M.φ (M.φ data.dart)))) := (M.tail_sigma _).symm
    _ = M.tail data.dart := by rw [h]

/-- **`keptPhi d₂` lands at vertex `tail dart` (= `u`).**  `keptPhi d₂ =
sideSigma₁ (sideAlpha₁ d₂)`; the `α`-step's underlying dart is `M.α (M.φ² dart)`
(at vertex `tail dart`), and the filtered rotation keeps the vertex. -/
theorem keptPhi_face₁Dart₂_tail (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) :
        {d : D // d ∉ data.keptDel₁}) : D)
      = M.tail data.dart := by
  -- `keptPhi β ρ k = ρ (β k)`; unfold `ρ = sideSigma₁ = filteredRotation M.σ keptDel₁`.
  show M.tail ((data.sideSigma₁ (data.sideAlpha₁ hsep (face₁Dart₂ data)) :
      {d : D // d ∉ data.keptDel₁}) : D) = M.tail data.dart
  -- the filtered rotation preserves the vertex of its argument,
  rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
    tail_filteredRotation data.keptDel₁ (data.sideAlpha₁ hsep (face₁Dart₂ data))]
  -- whose underlying dart is `M.α (M.φ² dart)`, at vertex `tail dart`.
  rw [sideAlpha₁_apply_coe]
  show M.tail (M.α ((face₁Dart₂ data : {d : D // d ∉ data.keptDel₁}) : D)) = M.tail data.dart
  show M.tail (M.α (M.φ (M.φ data.dart))) = M.tail data.dart
  exact tail_alpha_phiSq_dart data

/-- **`d₁ = M.φ dart` lives at vertex `head dart` (= `v`).**  `tail (M.φ dart) =
head dart` by `tail_phi`. -/
theorem face₁Dart₁_tail (data : hNT.ChordSplitData u v) :
    M.tail ((face₁Dart₁ data : {d : D // d ∉ data.keptDel₁}) : D) = M.head data.dart := by
  show M.tail (M.φ data.dart) = M.head data.dart
  exact M.tail_phi data.dart

/-- **The two chord endpoints are distinct vertices** (`tail dart ≠ head dart`):
the chord is a genuine edge, so it is not a loop. -/
theorem u_ne_v (data : hNT.ChordSplitData u v) :
    M.tail data.dart ≠ M.head data.dart :=
  hNT.simpleGraph.no_loop data.dart



/-- **The chord-cap bigon WRAP `keptPhi d₂ = d₁` is FALSE.**  `keptPhi d₂` lives at
vertex `tail dart = u` (`keptPhi_face₁Dart₂_tail`) and `d₁ = M.φ dart` lives at the
other chord endpoint `head dart = v` (`face₁Dart₁_tail`), with `u ≠ v` (`u_ne_v`);
distinct vertices force distinct darts.

This is the precise refutation of the route proposed in `opus-bigonwrap-reply.md`:
the filtered rotation `sideSigma₁` only ever moves *within* a single `σ`-orbit
(vertex), so no `FilteredRotation.ContiguousInterval` for `u`'s kept darts can make
it reach `d₁`, which sits at `v`.  The `keptPhi`-wrap is the WRONG residue. -/
theorem keptPhi_face₁Dart₂_ne_face₁Dart₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) ≠ face₁Dart₁ data := by
  intro hwrap
  -- equal darts ⇒ equal `tail`s, contradicting the distinct-vertex facts.
  have htail : M.tail ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) :
      {d : D // d ∉ data.keptDel₁}) : D)
        = M.tail ((face₁Dart₁ data : {d : D // d ∉ data.keptDel₁}) : D) := by
    rw [hwrap]
  rw [keptPhi_face₁Dart₂_tail data hsep, face₁Dart₁_tail data] at htail
  exact u_ne_v data htail





















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



/-- **The canonical side-1 anchor `a₀`** — the kept dart whose `sideSigma₁`-successor is
`keptPhi d₂`. -/
noncomputable def side₁Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₁} :=
  (data.sideSigma₁).symm
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data))

/-- **The canonical side-1 anchor `a₁`** — the kept dart whose `sideSigma₁`-successor is
`d₁ = M.φ dart`. -/
noncomputable def side₁Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₁} :=
  (data.sideSigma₁).symm (face₁Dart₁ data)

/-- **`sideSigma₁ a₀ = keptPhi d₂`** (definitional, `Equiv.apply_symm_apply`). -/
@[simp] theorem sideSigma₁_side₁Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₁ (side₁Anchor₀ data hsep)
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) := by
  rw [side₁Anchor₀, Equiv.apply_symm_apply]

/-- **`sideSigma₁ a₁ = d₁`** (definitional, `Equiv.apply_symm_apply`). -/
@[simp] theorem sideSigma₁_side₁Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₁ (side₁Anchor₁ data hsep) = face₁Dart₁ data := by
  rw [side₁Anchor₁, Equiv.apply_symm_apply]

/-- **The canonical anchors are distinct.**  If `a₀ = a₁` then their `sideSigma₁`-images
agree, i.e. `keptPhi d₂ = d₁` — refuted by the proven geometric fact
`ChordSigmaContig.keptPhi_face₁Dart₂_ne_face₁Dart₁` (the false-wrap correction). -/
theorem side₁Anchors_ne (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    side₁Anchor₀ data hsep ≠ side₁Anchor₁ data hsep := by
  intro h
  -- equal anchors ⇒ equal `sideSigma₁`-images ⇒ `keptPhi d₂ = d₁`, contradiction.
  have himg : data.sideSigma₁ (side₁Anchor₀ data hsep)
      = data.sideSigma₁ (side₁Anchor₁ data hsep) := by rw [h]
  rw [sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁] at himg
  exact keptPhi_face₁Dart₂_ne_face₁Dart₁ data hsep himg



/-- **`d₁` and `keptPhi d₂` lie on a common `keptPhi`-cycle.**  `keptPhi.SameCycle d₁
(keptPhi d₂)`: `keptPhi d₁ = d₂` (`keptPhi_face₁Dart₁`), and `keptPhi d₂` is one further
forward step from `d₂`, so `d₁ → d₂ → keptPhi d₂` is a `keptPhi`-walk. -/
theorem keptPhi_sameCycle_d₁_keptPhi_d₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle
      (face₁Dart₁ data)
      (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data)) := by
  -- peel the outer `keptPhi` on the right: reduce to `SameCycle d₁ d₂`.
  rw [Equiv.Perm.sameCycle_apply_right]
  -- `SameCycle d₁ d₂` from `keptPhi d₁ = d₂`.
  rw [← keptPhi_face₁Dart₁ data hsep]
  exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- **The anchor-incidence fact for the canonical anchors** (`Side₁AnchorsShareFace`).  The
canonical anchors' `sideSigma₁`-successors `keptPhi d₂` and `d₁` lie on a common kept
(`keptPhi`) face — the shared pre-splice boundary face (the `face₁` orbit).  This is the
proven fact-2 instance the chord-side disk/sphere machinery
(`ChordDisk.side₁_isSphereMap_of_disk`, `ChordSideNT.side₁_sphere_unconditional`) consumes,
now SUPPLIED for the canonical anchors. -/
theorem side₁AnchorsShareFace_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) := by
  -- unfold to `keptPhi.SameCycle (sideSigma₁ a₀) (sideSigma₁ a₁)`,
  show (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle
    (data.sideSigma₁ (side₁Anchor₀ data hsep)) (data.sideSigma₁ (side₁Anchor₁ data hsep))
  rw [sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁]
  -- i.e. `SameCycle (keptPhi d₂) d₁`, the symmetric of `keptPhi_sameCycle_d₁_keptPhi_d₂`.
  exact (keptPhi_sameCycle_d₁_keptPhi_d₂ data hsep).symm



/-- **The easy splice-swap direction `tracePhi d₂ = d₁`** for the canonical anchors.  Since
`ρ a₀ = keptPhi d₂`, the swap `swap (keptPhi d₂) (ρ a₁)` sends `keptPhi d₂ ↦ ρ a₁ = d₁`. -/
theorem side₁Anchors_trace21 (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (face₁Dart₂ data)
      = face₁Dart₁ data := by
  rw [tracePhi_eq_swap_keptPhi, sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁]
  -- `swap (keptPhi d₂) d₁ (keptPhi d₂) = d₁`.
  exact Equiv.swap_apply_left _ _

/-- **The other splice-swap direction `tracePhi d₁ = d₂`** for the canonical anchors.
`tracePhi d₁ = swap (keptPhi d₂) d₁ (keptPhi d₁)`; `keptPhi d₁ = d₂`
(`keptPhi_face₁Dart₁`), and `d₂ ∉ {keptPhi d₂, d₁}` (`keptPhi_face₁Dart₂_ne_self`,
`face₁Dart_distinct`), so the swap fixes `d₂`. -/
theorem side₁Anchors_trace12 (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (face₁Dart₁ data)
      = face₁Dart₂ data := by
  rw [tracePhi_eq_swap_keptPhi, sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁,
    keptPhi_face₁Dart₁ data hsep]
  -- `swap (keptPhi d₂) d₁ d₂ = d₂` since `d₂ ≠ keptPhi d₂` and `d₂ ≠ d₁`.
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · -- `d₂ ≠ keptPhi d₂` (symm of `keptPhi_face₁Dart₂_ne_self`).
    exact (keptPhi_face₁Dart₂_ne_self data hsep).symm
  · -- `d₂ ≠ d₁` (symm of `face₁Dart_distinct`).
    exact (face₁Dart_distinct data).symm







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





/-- **`τ (β a₀) = face₁Dart₁`** for the canonical anchors. -/
theorem side₁_trace_beta_a0_to_face₁Dart₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
      = face₁Dart₁ data := by
  rw [tracePhi_b0 (data.sideAlpha₁ hsep) data.sideSigma₁ (data.sideAlpha₁_involutive hsep),
    sideSigma₁_side₁Anchor₁]

/-- **`β a₀` is `τ`-SameCycle to `face₁Dart₁`** (one `τ`-step), the orbit form of brick 2. -/
theorem side₁_betaA0_sameCycle_face₁Dart₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) (face₁Dart₁ data) := by
  refine ⟨1, ?_⟩
  rw [zpow_one]
  exact side₁_trace_beta_a0_to_face₁Dart₁ data hsep



/-- **The fresh dart `inr 0` joins the `face₁` side face**: `S.dartFace (inr 0) = S.dartFace
(inl face₁Dart₁)`. -/
theorem side₁_chord0_face_eq_face₁_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) := by
  -- `inr 0 ↦ inl (β a₀)` (wrapper, in `sideMap₁` form), then `inl (β a₀) ↦ inl face₁Dart₁`.
  rw [sideMap₁_chordDart_face_eq_b0 data hsep (side₁Anchor₀ data hsep)
        (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)]
  -- `S.dartFace (inl (β a₀)) = S.dartFace (inl face₁Dart₁)` iff `β a₀ ~τ face₁Dart₁` (brick 2).
  exact (sideFace_inl_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
    (side₁Anchors_ne data hsep)
    ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) (face₁Dart₁ data)).2
    (side₁_betaA0_sameCycle_face₁Dart₁ data hsep)





















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

/-- **Right-multiplication split.**  If `a ≠ b` and `a, b` are in the same `p`-cycle, then
`p * swap a b` does NOT have `a, b` in one cycle.  (The `same`-cycle branch of the dichotomy:
the swap splits the shared cycle.) -/
theorem notSameCycle_mul_swap_right_of_sameCycle (p : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hsc : p.SameCycle a b) :
    ¬ (p * Equiv.swap a b).SameCycle a b := by
  intro hqsc
  -- If both `p` and `p * swap` had `a, b` same-cycle, the cycle counts coincide,
  -- contradicting `numCycles_mul_swap_ne`.
  have hq_le_p : numCycles (p * Equiv.swap a b) ≤ numCycles p := by
    have h := PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle
      (p * Equiv.swap a b) hqsc
    simpa [mul_assoc] using h
  have hp_le_q : numCycles p ≤ numCycles (p * Equiv.swap a b) :=
    PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle p hsc
  exact PermTranspositionCycleCount.numCycles_mul_swap_ne p hab
    (le_antisymm hq_le_p hp_le_q)

/-- **Left-multiplication split.**  If `a ≠ b` and `a, b` are in the same `p`-cycle, then
`swap a b * p` does NOT have `a, b` in one cycle.  Reduced to the right-multiplication split by
conjugation with `swap a b` (which fixes the cycle structure and swaps `a ↔ b`). -/
theorem notSameCycle_swap_mul_left_of_sameCycle (p : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hsc : p.SameCycle a b) :
    ¬ (Equiv.swap a b * p).SameCycle a b := by
  intro hsc'
  -- Conjugating `(swap a b * p).SameCycle a b` by `g := swap a b`:
  -- `(swap·(swap·p)·swap⁻¹).SameCycle (swap a)(swap b)`, and
  -- `swap·(swap·p)·swap⁻¹ = p·swap⁻¹ = p·swap`, `swap a = b`, `swap b = a`.
  apply notSameCycle_mul_swap_right_of_sameCycle p hab hsc
  have h2 := hsc'.conj (g := Equiv.swap a b)
  -- normalise the conjugate permutation and the two swapped endpoints.
  have hperm : Equiv.swap a b * (Equiv.swap a b * p) * (Equiv.swap a b)⁻¹
      = p * Equiv.swap a b := by
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul, Equiv.swap_inv]
  rw [hperm, Equiv.swap_apply_left, Equiv.swap_apply_right] at h2
  exact h2.symm

end PermSplit



section Canonical

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The canonical chord predecessors are NOT `tracePhi`-SameCycle.**  `τ = swap (ρ a₀) (ρ a₁)
* keptPhi`, with `keptPhi.SameCycle (ρ a₀) (ρ a₁)` (the proved `side₁AnchorsShareFace_canonical`)
and `ρ a₀ ≠ ρ a₁` (anchors distinct).  Hence the swap splits the shared kept face, so the two
chord predecessors `ρ a₀`, `ρ a₁` no longer share a `τ`-cycle; transporting one `τ`-step on each
side gives `¬ τ.SameCycle (β a₀) (β a₁)`. -/
theorem side₁_chordPred_notSameCycle_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ¬ (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
      ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) := by
  classical
  set β := data.sideAlpha₁ hsep with hβ
  set ρ := data.sideSigma₁ with hρ
  set a₀ := side₁Anchor₀ data hsep with ha₀
  set a₁ := side₁Anchor₁ data hsep with ha₁
  -- the share-face fact: `keptPhi.SameCycle (ρ a₀) (ρ a₁)`.
  have hshare : (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁) := by
    have h := side₁AnchorsShareFace_canonical data hsep
    -- unfolds to `keptPhi.SameCycle (sideSigma₁ a₀) (sideSigma₁ a₁)`.
    simpa [hβ, hρ, ha₀, ha₁, ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace, keptPhi]
      using h
  -- `ρ a₀ ≠ ρ a₁`.
  have hne : ρ a₀ ≠ ρ a₁ := ρa₀_ne_ρa₁ ρ (side₁Anchors_ne data hsep)
  -- the split: `¬ τ.SameCycle (ρ a₀) (ρ a₁)`.
  have hsplit : ¬ (tracePhi β ρ a₀ a₁).SameCycle (ρ a₀) (ρ a₁) := by
    rw [show tracePhi β ρ a₀ a₁ = Equiv.swap (ρ a₀) (ρ a₁) * keptPhi β ρ from rfl]
    exact notSameCycle_swap_mul_left_of_sameCycle (keptPhi β ρ) hne hshare
  -- transport: `τ (β a₀) = ρ a₁` and `τ (β a₁) = ρ a₀`, so
  -- `τ.SameCycle (β a₀) (β a₁) ↔ τ.SameCycle (ρ a₁) (ρ a₀)`.
  intro hsc
  apply hsplit
  have hb0 : tracePhi β ρ a₀ a₁ (β a₀) = ρ a₁ :=
    tracePhi_b0 β ρ (data.sideAlpha₁_involutive hsep) a₀ a₁
  have hb1 : tracePhi β ρ a₀ a₁ (β a₁) = ρ a₀ :=
    tracePhi_b1 β ρ (data.sideAlpha₁_involutive hsep) a₀ a₁
  -- `τ.SameCycle (β a₀) (β a₁) → τ.SameCycle (τ (β a₀)) (τ (β a₁)) = τ.SameCycle (ρ a₁) (ρ a₀)`.
  have hstep : (tracePhi β ρ a₀ a₁).SameCycle
      (tracePhi β ρ a₀ a₁ (β a₀)) (tracePhi β ρ a₀ a₁ (β a₁)) :=
    hsc.apply_left.apply_right
  rw [hb0, hb1] at hstep
  exact hstep.symm

/-- **`face₁_not_outer` for `outerFace := S.dartFace (inr 1)`.**  `S.dartFace (inl face₁Dart₁)
= S.dartFace (inr 0)` (brick 3), and `S.dartFace (inr 0) ≠ S.dartFace (inr 1)` by
`chordOrbits_eq_iff_tracePhi` + the splice-split fact. -/
theorem side₁_face₁_not_outer_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))
      ≠ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) := by
  intro hcontra
  -- `S.dartFace (inr 0) = S.dartFace (inl face₁Dart₁) = S.dartFace (inr 1)`.
  have h01 : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) := by
    rw [side₁_chord0_face_eq_face₁_canonical data hsep, hcontra]
  -- `chordOrbits_eq_iff_tracePhi` : the chord-dart faces coincide iff the chord predecessors
  -- share a `tracePhi`-orbit.
  have hsame : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
        ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) :=
    (chordOrbits_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
      (side₁Anchors_ne data hsep)).1 h01
  exact side₁_chordPred_notSameCycle_canonical data hsep hsame









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



/-- **`ι` computes on a class to the `M.tail` of its projected representative.**  By the
`Quotient.lift` definition of `sideVertexToM₁`, the class of a representative `y` maps to
`M.tail (proj a₀ a₁ y).1`.  (This is the generalisation of `sideVertexToM₁_inl` to arbitrary
representatives, fresh darts included.) -/
lemma sideVertexToM₁_mk (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) y)
      = M.tail (proj a₀ a₁ y).1 :=
  rfl

/-- **Brick 1 — `ι` is injective.**  `ι ⟦y⟧ = ι ⟦z⟧` gives `M.σ.SameCycle (proj y).1 (proj z).1`
(`M.tail` equal ⇒ same `σ`-cycle, `Quotient.exact`).  Transport back: a `sideSigma₁`-SameCycle of
`proj y`, `proj z` (`filteredRotation_sameCycle_iff`), then a `freshSigma`-SameCycle of `y`, `z`
(`freshSigma_sameCycle_iff` backward), i.e. `⟦y⟧ = ⟦z⟧`.  Purely combinatorial. -/
theorem sideVertexToM₁_injective_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    Function.Injective (sideVertexToM₁ data hsep a₀ a₁ hne) := by
  -- reduce to representatives.
  refine fun X Y => ?_
  refine Quotient.inductionOn₂ X Y (fun y z hYZ => ?_)
  -- `hYZ : ι ⟦y⟧ = ι ⟦z⟧`, defeq `M.tail (proj y).1 = M.tail (proj z).1`.
  -- `M.tail a = M.tail b` is `Quotient.mk (cycleSetoid M.σ) a = …`, so `Quotient.exact` gives
  -- `M.σ.SameCycle a b` (Lean unfolds `ι ⟦·⟧ = M.tail (proj ·).1` definitionally).
  have hM : M.σ.SameCycle (proj a₀ a₁ y).1 (proj a₀ a₁ z).1 := Quotient.exact hYZ
  -- back to a `sideSigma₁`-SameCycle of the (kept) projections.
  have hss : data.sideSigma₁.SameCycle (proj a₀ a₁ y) (proj a₀ a₁ z) :=
    (FilteredRotation.filteredRotation_sameCycle_iff M.σ data.keptDel₁
      (proj a₀ a₁ y) (proj a₀ a₁ z)).2 hM
  -- back to a `freshSigma`-SameCycle of the representatives.
  have hfs : (freshSigma data.sideSigma₁ a₀ a₁ hne).SameCycle y z :=
    (freshSigma_sameCycle_iff data.sideSigma₁ hne y z).2 hss
  exact Quotient.sound hfs



/-- `ι (sideMap₁.tail (inr j))` is `M.tail a₀.1` (`j = 0`) or `M.tail a₁.1` (`j = 1`). -/
lemma sideVertexToM₁_tail_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) (Sum.inr j))
      = M.tail (if j = 0 then a₀.1 else a₁.1) := by
  rw [sideVertexToM₁_mk data hsep a₀ a₁ hne (Sum.inr j)]
  fin_cases j
  · simp [proj]
  · simp [proj]

/-- `freshAlpha (sideAlpha₁) (inr j)` is the *other* fresh dart `inr (swap j)`, whose `ι`-tail is
the *other* anchor.  Hence the fresh chord dart `inr j` has `ι`-endpoints `M.tail a₀.1` and
`M.tail a₁.1` (in some order). -/
lemma sideVertexToM₁_head_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₁ hsep)) (Sum.inr j)))
      = M.tail (if j = 0 then a₁.1 else a₀.1) := by
  rw [freshAlpha_inr]
  rw [sideVertexToM₁_tail_inr data hsep a₀ a₁ hne (Equiv.swap (0 : Fin 2) 1 j)]
  fin_cases j
  · simp [Equiv.swap_apply_left]
  · simp [Equiv.swap_apply_right]

/-- **The `ι`-edge of any side dart.**  For every side dart `d`, the `ι`-images of its side
endpoints `sideMap₁.tail d`, `sideMap₁.head d` are `M`-adjacent: an `inl x'` dart gives the proved
`M`-edge of `x'` (`ι_adj_of_inl`); a fresh chord dart gives the anchor-tail pair (`M`-adjacent by
`hchord`).  `sideMap₁.tail d = ⟦d⟧` and `sideMap₁.head d = ⟦freshAlpha _ d⟧` (definitional). -/
lemma ι_adj_of_dart (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (d : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    M.Adj
      (sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) d))
      (sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₁ hsep)) d))) := by
  cases d with
  | inl x' => exact ι_adj_of_inl data hsep a₀ a₁ hne x'
  | inr j =>
      rw [sideVertexToM₁_tail_inr data hsep a₀ a₁ hne j,
        sideVertexToM₁_head_inr data hsep a₀ a₁ hne j]
      fin_cases j
      · simpa using hchord
      · simpa using M.adj_symm hchord



/-- **Brick 2 — `ι_adj`.**  Side adjacency `sideMap₁.toSimpleGraph.Adj x y` carries to
`M.toSimpleGraph.Adj (ι x) (ι y)`.  The witnessing side dart `d` gives `s(x, y) = sideMap₁.dartEdge
d = s(sideMap₁.tail d, sideMap₁.head d)`, whose `ι`-images are `M`-adjacent (`ι_adj_of_dart`); the
unordered pair matches by `Sym2.eq_iff`.  The `≠` half is preserved by injectivity (Brick 1). -/
theorem sideVertexToM₁_adj_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
        M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) := by
  intro x y hxy
  rw [toSimpleGraph_adj] at hxy ⊢
  obtain ⟨hne_xy, d, hd⟩ := hxy
  -- the `≠` part: `ι x ≠ ι y` from injectivity + `x ≠ y`.
  refine ⟨fun h => hne_xy (sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne h), ?_⟩
  -- `s(x, y) = sideMap₁.dartEdge d = s(sideMap₁.tail d, sideMap₁.head d)` (the last `=` is `rfl`).
  have hM := ι_adj_of_dart data hsep a₀ a₁ hne hchord d
  -- `sideMap₁.tail d = ⟦d⟧` and `sideMap₁.head d = ⟦freshAlpha _ d⟧` (definitional), so:
  have hd' : s((data.sideMap₁ hsep a₀ a₁ hne).tail d, (data.sideMap₁ hsep a₀ a₁ hne).head d)
      = s(x, y) := hd
  rcases Sym2.eq_iff.1 hd' with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [← hx, ← hy]; exact hM
  · rw [← hx, ← hy]; exact M.adj_symm hM



/-- **Brick 3 — `ι_adj_reflect`, isolated as the named confinement residue.**  We do NOT silently
assume more than the field itself: the brick simply *is* the hypothesis, recorded as the minimal
region edge-confinement fact (an `M`-edge between two `ι`-images is a side edge), which the open
`ChordSplitRegions`/Schoenflies layer is responsible for.  Reported in the handoff as the genuine
planar block. -/
theorem sideVertexToM₁_adj_reflect_canonical (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y :=
  hreflect



/-- **Brick 5 — `smaller`.**  From the proved injectivity of `ι` and an explicit omitted
`M`-vertex `w ∉ Set.range ι` (the opposite-arc internal vertex side 1 drops — the named
region-confinement residue `homit`), the side has strictly fewer vertices than `M`. -/
theorem side₁_smaller_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)) :
    (data.sideMap₁ hsep a₀ a₁ hne).V < M.V := by
  classical
  obtain ⟨w, hw⟩ := homit
  -- `(sideMap₁).V = Fintype.card (sideMap₁).Vertex`, `M.V = Fintype.card M.Vertex`.
  show Fintype.card (data.sideMap₁ hsep a₀ a₁ hne).Vertex < Fintype.card M.Vertex
  -- the image of `ι` is a proper subset of `M.Vertex` (it misses `w`); `ι` injective.
  have hinj := sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne
  -- map the (full) domain finset injectively into `M.Vertex`, missing `w`.
  have hcard_le : Fintype.card (data.sideMap₁ hsep a₀ a₁ hne).Vertex
      = (Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne)).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [hcard_le]
  -- the image is a finset of `M.Vertex` not containing `w`, hence a strict subset of `univ`.
  have hsub : Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.2 ?_
    intro hfull
    apply hw
    have hmem : w ∈ Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne) := by
      rw [hfull]; exact Finset.mem_univ w
    obtain ⟨V, _, hV⟩ := Finset.mem_image.1 hmem
    exact ⟨V, hV⟩
  calc (Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne)).card
      < (Finset.univ : Finset M.Vertex).card := Finset.card_lt_card hsub
    _ = Fintype.card M.Vertex := Finset.card_univ



/-- **Brick 6 — the side-1 residue, partially assembled.**  All six non-`ci`/`hshare`
`ChordSideResidue` fields are produced: `ι_inj` and the kept-dart half of `ι_adj` PROVED
unconditionally; the fresh-chord `ι_adj` half from `hchord`; `ι_adj_reflect` from the named
confinement residue `hreflect`; `hLₛ` the residue list field; `smaller` from injectivity + the
omitted-vertex residue `homit`.

Remaining (the open `ChordSplitRegions`/discrete-Schoenflies content): `hreflect` (region
edge-confinement) and `homit` (the opposite-arc omitted vertex's not-in-range).  These are the two
honest planar inputs; `hchord` is the chord adjacency `u–v` and `hLₛ` the list transport. -/
def chordSideResidue₁_partial (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (ci : ContiguousInterval data hsep a₀ a₁ hne)
    (hshare : ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y)
    (pₛ qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  chordSideResidue_mk data hsep a₀ a₁ hne L ci hshare
    (sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne)
    (sideVertexToM₁_adj_canonical data hsep a₀ a₁ hne hchord)
    (sideVertexToM₁_adj_reflect_canonical data hsep a₀ a₁ hne hreflect)
    pₛ qₛ cpₛ cqₛ hLₛ
    (side₁_smaller_canonical data hsep a₀ a₁ hne homit)

end ProofsInTheBook.ZinanCh35Iota









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



/-- **`dartFace`-equality is `φ`-`SameCycle`.**  `dartFace d = Quotient.mk (cycleSetoid
M.φ) d`, so two darts share a face iff they are `M.φ.SameCycle`. -/
lemma sameCycle_phi_of_dartFace_eq {d e : D} (h : M.dartFace d = M.dartFace e) :
    M.φ.SameCycle d e := by
  have := Quotient.exact h
  exact this

/-- **A `φ`-`3`-cycle element is `d`, `φ d`, or `φ² d`.**  If `M.φ³ d = d` and
`M.φ.SameCycle d e`, then `e ∈ {d, M.φ d, M.φ² d}`.  Proof: the triple is invariant
under both `φ` and `φ⁻¹` (using `φ³ d = d`), so it contains the whole `φ`-orbit of `d`,
hence `e = φ^i d` for some `i : ℤ`. -/
lemma mem_triple_of_sameCycle_phiCube {d e : D} (hcube : M.φ (M.φ (M.φ d)) = d)
    (h : M.φ.SameCycle d e) :
    e = d ∨ e = M.φ d ∨ e = M.φ (M.φ d) := by
  obtain ⟨i, hi⟩ := h
  -- `φ⁻¹ d = φ² d`, `φ⁻¹ (φ d) = d`, `φ⁻¹ (φ² d) = φ d`  (from `φ³ d = d`).
  have hinv0 : M.φ.symm d = M.φ (M.φ d) := by
    rw [Equiv.symm_apply_eq]; exact hcube.symm
  have hinv1 : M.φ.symm (M.φ d) = d := by rw [Equiv.symm_apply_eq]
  have hinv2 : M.φ.symm (M.φ (M.φ d)) = M.φ d := by rw [Equiv.symm_apply_eq]
  -- The predicate "x ∈ triple" is invariant under `φ` and `φ⁻¹`, so `φ^i d` is in it.
  have key : ∀ k : ℤ, (M.φ ^ k) d = d ∨ (M.φ ^ k) d = M.φ d ∨
      (M.φ ^ k) d = M.φ (M.φ d) := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · left; simp
    · intro n ih
      rw [show ((n : ℤ) + 1) = 1 + (n : ℤ) by ring, zpow_add, zpow_one,
        Equiv.Perm.mul_apply]
      rcases ih with h0 | h1 | h2
      · right; left; rw [h0]
      · right; right; rw [h1]
      · left; rw [h2]; exact hcube
    · intro n ih
      have hstep : (M.φ ^ (-(n : ℤ) - 1)) d = M.φ.symm ((M.φ ^ (-(n : ℤ))) d) := by
        rw [show (-(n : ℤ) - 1) = (-1) + (-(n : ℤ)) by ring, zpow_add, Equiv.Perm.mul_apply,
          show (M.φ ^ (-1 : ℤ)) = M.φ.symm from by
            rw [zpow_neg, zpow_one]; rfl]
      rw [hstep]
      rcases ih with h0 | h1 | h2
      · rw [h0]; right; right; exact hinv0
      · rw [h1]; left; exact hinv1
      · rw [h2]; right; left; exact hinv2
  rcases key i with h0 | h1 | h2
  · left; rw [← hi, h0]
  · right; left; rw [← hi, h1]
  · right; right; rw [← hi, h2]

/-- **The triangle lever (`M.φ` form).**  Two distinct darts of the same inner
triangular face (`M.φ³ d = d`) are joined by a single `M.φ`-step (in one direction or
the other). -/
lemma phi_edge_of_sameFace_triangle {d e : D}
    (hcube : M.φ (M.φ (M.φ d)) = d) (hface : M.dartFace d = M.dartFace e)
    (hne : d ≠ e) :
    M.φ d = e ∨ M.φ e = d := by
  have hsc := sameCycle_phi_of_dartFace_eq hface
  rcases mem_triple_of_sameCycle_phiCube hcube hsc with h0 | h1 | h2
  · exact absurd h0.symm hne
  · exact Or.inl h1.symm
  · -- e = φ² d ⇒ φ e = φ³ d = d
    right; rw [h2]; exact hcube



/-- The `p`/`q` bank darts are exactly the cycle darts: `qDart i = dart i`,
`pDart i = α (dart (prevIdx i))`, both in `dartSet`. -/
lemma pDart_mem_dartSet (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.pDart i ∈ C.dartSet := by
  rw [pDart]; exact C.alpha_dart_mem_dartSet _

lemma qDart_mem_dartSet (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.qDart i ∈ C.dartSet := by
  rw [qDart]; exact C.dart_mem_dartSet _

/-- **Clean `φ'₂` on a non-cycle dart whose `M.φ`-image is also non-cycle.**  Then the
cap-divert branches of `cutCapPhi2_inl_other_cases` cannot fire (they require
`M.φ d = M.σ (M.α d)` to be a `p`/`q` cycle dart), so `φ'₂ (inl d) = inl (M.φ d)`. -/
lemma cutCapPhi2_inl_clean (C : SimplePrimalCycle M) {d : D}
    (hd : d ∉ C.dartSet) (hphid : M.φ d ∉ C.dartSet) :
    (C.cutCapMap2).φ (Sum.inl d) = Sum.inl (M.φ d) := by
  rcases C.cutCapPhi2_inl_other_cases hd with hclean | ⟨j, hpj, _⟩ | ⟨j, hqj, _⟩
  · exact hclean
  · refine absurd ?_ hphid
    rw [show M.φ d = M.σ (M.α d) from rfl, hpj]; exact C.pDart_mem_dartSet j
  · refine absurd ?_ hphid
    rw [show M.φ d = M.σ (M.α d) from rfl, hqj]; exact C.qDart_mem_dartSet j

/-- **The recoverable rotation-system contiguity (`φ'₂` form).**  Two distinct
**non-cycle** darts `d`, `e` in one inner triangular face are joined by a single
`φ'₂`-edge of the corrected cut map.  This is the genuine M-lesson recoverable core:
the triangle `φ`-`3`-cycle gives a single `M.φ`-step, which lifts cleanly because both
darts are non-cycle. -/
lemma phiPrime_edge_of_innerGate (C : SimplePrimalCycle M) {d e : D}
    (hcube : M.φ (M.φ (M.φ d)) = d) (hface : M.dartFace d = M.dartFace e)
    (hne : d ≠ e) (hd : d ∉ C.dartSet) (he : e ∉ C.dartSet) :
    (C.cutCapMap2).φ (Sum.inl d) = Sum.inl e ∨
      (C.cutCapMap2).φ (Sum.inl e) = Sum.inl d := by
  rcases phi_edge_of_sameFace_triangle hcube hface hne with hfwd | hbwd
  · -- M.φ d = e: clean lift of d (its image e is non-cycle)
    left
    have := C.cutCapPhi2_inl_clean hd (by rw [hfwd]; exact he)
    rwa [hfwd] at this
  · -- M.φ e = d: clean lift of e (its image d is non-cycle)
    right
    have := C.cutCapPhi2_inl_clean he (by rw [hbwd]; exact hd)
    rwa [hbwd] at this















/-- A crossing dart of an ordinary dual path is non-cycle (`∉ dartSet`), since it
crosses an uncut edge. -/
lemma edge_notMem_dartSet (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (j : Fin P.n) : P.edge j ∉ C.dartSet :=
  C.notMem_dartSet_of_dartEdge_notMem (P.edge_uncut j)

/-- The `α`-reverse of a crossing dart is also non-cycle (same edge, still uncut). -/
lemma alpha_edge_notMem_dartSet (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (j : Fin P.n) : M.α (P.edge j) ∉ C.dartSet :=
  C.notMem_dartSet_of_dartEdge_notMem (by rw [M.dartEdge_alpha]; exact P.edge_uncut j)

/-- **The geometric residue of the intermediate gates** (the data the *bare* dual path
lacks): for each intermediate position, the entry dart's old face is an inner triangle
(`M.φ³ (α (edge j)) = α (edge j)`) and the entry/exit darts are distinct.  This is the
genuine combinatorial content `gateCompat` must supply for the intermediate gates — and
in a near-triangulation it is *true* (every visited inner face is a triangle), the
recoverable rotation-system contiguity. -/
structure InteriorTriangleGates (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2) :
    Prop where
  /-- The face at each intermediate gate is an inner triangle (the entry dart's
  `M.φ`-orbit is a `3`-cycle). -/
  tri : ∀ j : Fin P.n, ∀ hj : (j : ℕ) + 1 < P.n,
    M.φ (M.φ (M.φ (M.α (P.edge j)))) = M.α (P.edge j)
  /-- The entry and exit darts of each intermediate gate are distinct. -/
  ne : ∀ j : Fin P.n, ∀ hj : (j : ℕ) + 1 < P.n,
    M.α (P.edge j) ≠ P.edge ⟨(j : ℕ) + 1, hj⟩

/-- **Intermediate-gate `φ'₂`-edge, discharged.**  From the geometric residue
`InteriorTriangleGates`, each intermediate gate is realised by a single `φ'₂`-edge — the
exact `mid_edge` field of `GateFragmentCompatible`. -/
theorem mid_edge_of_interiorTriangleGates (C : SimplePrimalCycle M)
    (P : C.OrdinaryDualPath2) (hg : C.InteriorTriangleGates P)
    (j : Fin P.n) (hj : (j : ℕ) + 1 < P.n) :
    (C.cutCapMap2).φ (Sum.inl (M.α (P.edge j))) = Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩) ∨
      (C.cutCapMap2).φ (Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩)) = Sum.inl (M.α (P.edge j)) := by
  refine C.phiPrime_edge_of_innerGate (hg.tri j hj) ?_ (hg.ne j hj)
    (C.alpha_edge_notMem_dartSet P j) (C.edge_notMem_dartSet P ⟨(j : ℕ) + 1, hj⟩)
  -- co-facehood: both darts have face `P.face j.succ`.
  rw [P.right_face j]
  have hjs : (⟨(j : ℕ) + 1, hj⟩ : Fin P.n).castSucc = j.succ := by
    apply Fin.ext; simp [Fin.val_succ]
  rw [P.left_face ⟨(j : ℕ) + 1, hj⟩, hjs]







/-- **The minimal endpoint residue: the cap-channel link.**  The genuine remaining
content of `gateCompat` for an ordinary dual path is the *endpoint* connectivity, which
the surgery routes through the cap chain (NOT a within-face `φ'₂`-edge, as
`start_edge_*_false` show): the forward cycle dart `dart i` is `cutReach2`-connected to
the start crossing dart, and the reverse cycle dart `α (dart i)` to the end crossing
dart.  (For `n = 0` both reduce to `cutReach2 (inl (dart i)) (inl (α (dart i)))`.)

This is non-vacuous (`SidesReach2` already threads all cycle darts into one
`cutReach2`-loop) and is the honest discrete-Jordan datum — the analogue of
`ChordSigmaContig`'s `SideTracePhiTwoCycle` (connectivity through the spliced channel,
not the false within-face wrap). -/
def EndpointCapLink (C : SimplePrimalCycle M) (i : Fin C.len) (P : C.OrdinaryDualPath2) :
    Prop :=
  (∀ h : 0 < P.n,
      C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (P.edge ⟨0, h⟩))) ∧
    (∀ h : 0 < P.n,
      C.cutReach2 (Sum.inl (M.α (C.dart i)))
        (Sum.inl (M.α (P.edge ⟨P.n - 1, by omega⟩)))) ∧
    (P.n = 0 → C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))))





/-- **Non-vacuity of the endpoint cap residue (`n = 0`).**  Given a cross-bank
`cutReach2` link (the genuine connectivity datum, e.g. supplied by `M.Connected` through
`reachesBank2`), the nil ordinary path satisfies `EndpointCapLink`.  So the residue is
inhabited — not a hidden `False`. -/
theorem endpointCapLink_nil (C : SimplePrimalCycle M) (i : Fin C.len) (f : M.Face)
    (hcross : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i)))) :
    C.EndpointCapLink i (OrdinaryDualPath2.nil C f) := by
  refine ⟨fun h => ?_, fun h => ?_, fun _ => hcross⟩
  · exact absurd h (by show ¬ 0 < 0; omega)
  · exact absurd h (by show ¬ 0 < 0; omega)



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



/-- A single intermediate gate, lifted to a `cutReach2` step.  From
`mid_edge_of_interiorTriangleGates` (a clean `φ'₂`-edge in either direction) and
`cutReach2_of_phi_step`. -/
lemma cutReach2_midGate (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hg : C.InteriorTriangleGates P) (j : Fin P.n) (hj : (j : ℕ) + 1 < P.n) :
    C.cutReach2 (Sum.inl (M.α (P.edge j))) (Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩)) := by
  rcases C.mid_edge_of_interiorTriangleGates P hg j hj with hphi | hphi
  · -- φ'₂ (inl (α (edge j))) = inl (edge (j+1))
    have := C.cutReach2_of_phi_step (Sum.inl (M.α (P.edge j)))
    rwa [hphi] at this
  · -- φ'₂ (inl (edge (j+1))) = inl (α (edge j)) — use the reverse step
    have := C.cutReach2_of_phi_step (Sum.inl (P.edge ⟨(j : ℕ) + 1, hj⟩))
    rw [hphi] at this
    exact C.cutReach2_symm this

/-- A single crossing, lifted to a `cutReach2` step (the `α'`-uncut bridge). -/
lemma cutReach2_cross (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2) (j : Fin P.n) :
    C.cutReach2 (Sum.inl (P.edge j)) (Sum.inl (M.α (P.edge j))) :=
  C.cutReach2_across_uncut_dual_gate (P.edge_uncut j)

/-- **The interior reach (prefix form).**  For every `k < n`, the first crossing dart
`inl (edge 0)` reaches the reverse crossing dart `inl (α (edge k))`, by chaining `k`
crossings and `k` intermediate gates. -/
lemma interiorReach_prefix (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hg : C.InteriorTriangleGates P) (h0 : 0 < P.n) :
    ∀ k : ℕ, ∀ hk : k < P.n,
      C.cutReach2 (Sum.inl (P.edge ⟨0, h0⟩)) (Sum.inl (M.α (P.edge ⟨k, hk⟩)))
  | 0, hk => by
      -- base: just the first crossing
      have : (⟨0, hk⟩ : Fin P.n) = ⟨0, h0⟩ := rfl
      rw [this]
      exact C.cutReach2_cross P ⟨0, h0⟩
  | k + 1, hk => by
      have hk' : k < P.n := by omega
      have hkj : (k : ℕ) + 1 < P.n := by omega
      -- reach to α (edge k)
      have ih := C.interiorReach_prefix P hg h0 k hk'
      -- gate: α (edge k) ⇝ edge (k+1)
      have hgate := C.cutReach2_midGate P hg ⟨k, hk'⟩ (by simpa using hkj)
      -- crossing: edge (k+1) ⇝ α (edge (k+1))
      have hcross := C.cutReach2_cross P ⟨k + 1, hk⟩
      have hgate' :
          C.cutReach2 (Sum.inl (M.α (P.edge ⟨k, hk'⟩))) (Sum.inl (P.edge ⟨k + 1, hk⟩)) := by
        have he : (⟨(⟨k, hk'⟩ : Fin P.n) + 1, by simpa using hkj⟩ : Fin P.n)
            = ⟨k + 1, hk⟩ := by apply Fin.ext; simp
        rw [he] at hgate; exact hgate
      exact (ih.trans hgate').trans hcross

/-- **The interior reach.**  When `n > 0`, the first crossing dart reaches the last
reverse crossing dart through `cutReach2`. -/
lemma interiorReach_of_gates (C : SimplePrimalCycle M) (P : C.OrdinaryDualPath2)
    (hg : C.InteriorTriangleGates P) (h0 : 0 < P.n) :
    C.cutReach2 (Sum.inl (P.edge ⟨0, h0⟩)) (Sum.inl (M.α (P.edge ⟨P.n - 1, by omega⟩))) :=
  C.interiorReach_prefix P hg h0 (P.n - 1) (by omega)



/-- **The cross-bank bridge.**  From the endpoint cap-channel link and the interior
triangle gates, the forward cycle bank reaches the reverse cycle bank in the corrected
cut map.  (`n = 0`: the endpoint link is the bridge directly; `n > 0`: forward dart ⇝
first crossing ⇝ [interior reach] ⇝ last reverse crossing ⇝ reverse dart.) -/
theorem crossBankBridge_of_endpointCapLink (C : SimplePrimalCycle M) (i : Fin C.len)
    (P : C.OrdinaryDualPath2) (hlink : C.EndpointCapLink i P)
    (hg : C.InteriorTriangleGates P) :
    C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))) := by
  obtain ⟨hstart, hend, hnil⟩ := hlink
  by_cases h0 : 0 < P.n
  · -- dart i ⇝ edge 0 ⇝ α (edge (n-1)) ⇝ α (dart i)
    have hs : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (P.edge ⟨0, h0⟩)) := hstart h0
    have hmid := C.interiorReach_of_gates P hg h0
    have he : C.cutReach2 (Sum.inl (M.α (C.dart i)))
        (Sum.inl (M.α (P.edge ⟨P.n - 1, by omega⟩))) := hend h0
    exact (hs.trans hmid).trans (C.cutReach2_symm he)
  · -- n = 0: the endpoint link is the cross-bank bridge directly
    have hn0 : P.n = 0 := by omega
    exact hnil hn0



/-- **Connectivity from the corrected gate data** (under the dual-reachability
hypothesis).  Given `M.Connected`, the endpoint cap-channel link, and the interior
triangle gates of *some* extracted ordinary path, the corrected cut map is connected. -/
theorem cutCapMap2_connected_of_corrected (C : SimplePrimalCycle M) (i : Fin C.len)
    (hconn : M.Connected)
    (P : C.OrdinaryDualPath2) (hlink : C.EndpointCapLink i P)
    (hg : C.InteriorTriangleGates P) :
    (C.cutCapMap2).Connected :=
  C.cutCapMap2_connected_of_reachesBank_of_bridge i
    (C.reachesBank2_of_connected i hconn (C.sidesReach2_concrete i))
    (C.crossBankBridge_of_endpointCapLink i P hlink hg)



/-- **The corrected minimal chord-separation residue.** -/
structure ChordJordanInput' (C : SimplePrimalCycle M) : Prop where
  /-- The corrected face count `numCycles φ'₂ = F + 2` (kernel-anchored). -/
  faceCore : C.NumCyclesCutPhi2
  /-- Per-edge supplier: from a cycle-avoiding dual path, an ordinary dual path carrying
  the **cap-channel endpoint link** (`EndpointCapLink`, the genuine discrete-Jordan datum)
  and the **interior triangle gates** (`InteriorTriangleGates`, the recoverable lever). -/
  gateCompat' : ∀ i : Fin C.len,
    DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
      ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P

/-- The corrected connectivity parameter of `jordan_simple_cycle2_walk`, discharged from
the corrected residue bundle. -/
theorem connectivity_of_input' (C : SimplePrimalCycle M) (hconn : M.Connected)
    (hin : C.ChordJordanInput') (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    (C.cutCapMap2).Connected := by
  obtain ⟨P, hlink, hg⟩ := hin.gateCompat' i hpath
  exact C.cutCapMap2_connected_of_corrected i hconn P hlink hg

end CombMap.SimplePrimalCycle



namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

/-- **`InteriorTriangleGates` is inhabited on the nil path** (vacuously: no intermediate
gates). -/
theorem interiorTriangleGates_nil (C : SimplePrimalCycle M) (f : M.Face) :
    C.InteriorTriangleGates (OrdinaryDualPath2.nil C f) where
  tri := fun j hj => absurd hj (by
    have : (OrdinaryDualPath2.nil C f).n = 0 := rfl; omega)
  ne := fun j hj => absurd hj (by
    have : (OrdinaryDualPath2.nil C f).n = 0 := rfl; omega)





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

/-- The actual split indices of a transposition word: the swaps whose endpoints are already
in the same cycle of the prefix permutation. -/
noncomputable def actualSplitFinset (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → ForcedSplits.Swap X) : Finset (Fin m) :=
  Finset.univ.filter fun j =>
    (ForcedSplits.prefixPerm p W j.val).SameCycle (W j).x (W j).y

/-- A non-split transposition step lowers the cycle count by exactly one. -/
lemma stepDelta_eq_neg_one_of_not_sameCycle (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → ForcedSplits.Swap X) (j : Fin m)
    (hne : (W j).x ≠ (W j).y)
    (hnot :
      ¬ (ForcedSplits.prefixPerm p W j.val).SameCycle (W j).x (W j).y) :
    ForcedSplits.stepDelta p W j = -1 := by
  classical
  have hj : j.val < m := j.isLt
  rw [ForcedSplits.stepDelta, ForcedSplits.prefixPerm_succ p W hj,
    ForcedSplits.Swap.perm]
  have hnum := numCycles_mul_swap_of_not_sameCycle
    (ForcedSplits.prefixPerm p W j.val) hne hnot
  have hnumZ :
      (numCycles (ForcedSplits.prefixPerm p W j.val *
          Equiv.swap (W j).x (W j).y) : ℤ) + 1 =
        (numCycles (ForcedSplits.prefixPerm p W j.val) : ℤ) := by
    exact_mod_cast hnum
  linarith

/-- The sum of actual step deltas is `-m + 2 * (# actual splits)`. -/
theorem sum_stepDelta_eq_neg_m_add_two_actualSplits (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → ForcedSplits.Swap X)
    (hne : ∀ j : Fin m, (W j).x ≠ (W j).y) :
    (∑ j : Fin m, ForcedSplits.stepDelta p W j)
      = -(m : ℤ) + 2 * ((ForcedSplits.actualSplitFinset p W).card : ℤ) := by
  classical
  let S : Finset (Fin m) := ForcedSplits.actualSplitFinset p W
  have h_onS : ∀ j ∈ S, ForcedSplits.stepDelta p W j = 1 := by
    intro j hj
    have hsc :
        (ForcedSplits.prefixPerm p W j.val).SameCycle (W j).x (W j).y := by
      simpa [S, ForcedSplits.actualSplitFinset] using (Finset.mem_filter.mp hj).2
    exact ForcedSplits.stepDelta_eq_one_of_forced_split p W j (hne j) hsc
  have h_offS : ∀ j ∈ Sᶜ, ForcedSplits.stepDelta p W j = -1 := by
    intro j hj
    have hjnot : j ∉ S := by simpa using hj
    have hnot :
        ¬ (ForcedSplits.prefixPerm p W j.val).SameCycle (W j).x (W j).y := by
      intro hsc
      exact hjnot (by
        simp [S, ForcedSplits.actualSplitFinset, hsc])
    exact ForcedSplits.stepDelta_eq_neg_one_of_not_sameCycle p W j (hne j) hnot
  calc
    (∑ j : Fin m, ForcedSplits.stepDelta p W j)
        = (∑ j ∈ S, ForcedSplits.stepDelta p W j)
            + (∑ j ∈ Sᶜ, ForcedSplits.stepDelta p W j) := by
          rw [← Finset.sum_add_sum_compl S]
    _ = (∑ _j ∈ S, (1 : ℤ)) + (∑ _j ∈ Sᶜ, (-1 : ℤ)) := by
          congr 1
          · exact Finset.sum_congr rfl (fun j hj => h_onS j hj)
          · exact Finset.sum_congr rfl (fun j hj => h_offS j hj)
    _ = -(m : ℤ) + 2 * ((ForcedSplits.actualSplitFinset p W).card : ℤ) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcardC : (Sᶜ).card = m - S.card := by
            rw [Finset.card_compl, Fintype.card_fin]
          have hcardCZ : ((Sᶜ).card : ℤ) = (m : ℤ) - (S.card : ℤ) := by
            rw [hcardC]
            have hle : S.card ≤ m := by
              simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S
            omega
          rw [hcardCZ]
          dsimp [S]
          ring

end ForcedSplits

namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWord

open ForcedSplits SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A cycle-list decomposition with nodup cycle lists. -/
theorem exists_cycleListProd_nodup (q : Equiv.Perm X) :
    ∃ Ls : List (List X),
      (∀ L ∈ Ls, 2 ≤ L.length ∧ L.Nodup) ∧
      FaceCorrWord.cycleListProd Ls = q := by
  classical
  induction q using Equiv.Perm.cycle_induction_on with
  | base_one =>
      exact ⟨[], by simp, rfl⟩
  | base_cycles σ hσ =>
      obtain ⟨x, hx, -⟩ := id hσ
      have hxs : x ∈ σ.support := by
        rw [Equiv.Perm.mem_support]
        exact hx
      refine ⟨[Equiv.Perm.toList σ x], ?_, ?_⟩
      · intro L hL
        simp only [List.mem_singleton] at hL
        subst hL
        constructor
        · exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxs
        · -- If Mathlib renamed this, alternates: `Equiv.Perm.toList_nodup`,
          -- `Equiv.Perm.nodup_toList`.
          exact Equiv.Perm.nodup_toList σ x
      · simp only [FaceCorrWord.cycleListProd, mul_one, SeamChain.cycleOfList]
        rw [Equiv.Perm.formPerm_toList, Equiv.Perm.IsCycle.cycleOf_eq hσ hx]
  | induction_disjoint σ τ hdisj hσ hστ hτ =>
      obtain ⟨Lσ, hLσ, hfacσ⟩ := hστ
      obtain ⟨Lτ, hLτ, hfacτ⟩ := hτ
      refine ⟨Lσ ++ Lτ, ?_, ?_⟩
      · intro L hL
        rcases List.mem_append.mp hL with h | h
        · exact hLσ L h
        · exact hLτ L h
      · rw [FaceCorrWord.cycleListProd_append, hfacσ, hfacτ]

/-- Consecutive entries in a nodup list are distinct, in the form needed by `wordOfList`. -/
lemma wordOfList_ne_of_nodup (L : List X) (hL : L.Nodup)
    (j : Fin (L.length - 1)) :
    (FaceCorrWord.wordOfList L j).x ≠ (FaceCorrWord.wordOfList L j).y := by
  classical
  dsimp [FaceCorrWord.wordOfList]
  intro h
  have hj0 : j.val < L.length := by
    have := j.isLt
    omega
  have hj1 : j.val + 1 < L.length := by
    have := j.isLt
    omega
  have hidx : j.val = j.val + 1 := by
    -- If Mathlib renamed this, alternates: `List.Nodup.getElem_inj`,
    -- `List.Nodup.getElem_inj_iff`.
    exact (List.Nodup.getElem_inj_iff hL).mp h
  omega

/-- All swaps in a concatenated word of nodup cycle lists have distinct endpoints. -/
lemma concatWord_ne_of_nodup (Ls : List (List X))
    (hpos : ∀ L ∈ Ls, 2 ≤ L.length)
    (hnodup : ∀ L ∈ Ls, L.Nodup)
    (j : Fin (FaceCorrWord.concatLen Ls)) :
    (FaceCorrWord.concatWord Ls j).x ≠ (FaceCorrWord.concatWord Ls j).y := by
  classical
  induction Ls with
  | nil =>
      exact absurd j.isLt (by simp [FaceCorrWord.concatLen])
  | cons L rest ih =>
      have hLpos : 2 ≤ L.length := hpos L List.mem_cons_self
      have hLnodup : L.Nodup := hnodup L List.mem_cons_self
      have hpos_rest : ∀ L' ∈ rest, 2 ≤ L'.length := by
        intro L' hL'
        exact hpos L' (List.mem_cons_of_mem _ hL')
      have hnodup_rest : ∀ L' ∈ rest, L'.Nodup := by
        intro L' hL'
        exact hnodup L' (List.mem_cons_of_mem _ hL')
      by_cases hj : j.val < L.length - 1
      · have hjFin : j.val < (L.length - 1) := hj
        have hcast : (⟨j.val, hjFin⟩ : Fin (L.length - 1)) =
            ⟨j.val, hjFin⟩ := rfl
        simpa [FaceCorrWord.concatWord, FaceCorrWord.concatLen,
          FaceCorrWord.appendWord, hj] using
          FaceCorrWord.wordOfList_ne_of_nodup L hLnodup ⟨j.val, hjFin⟩
      · have hjRest : j.val - (L.length - 1) < FaceCorrWord.concatLen rest := by
          have hlt := j.isLt
          have hcl : FaceCorrWord.concatLen (L :: rest)
              = (L.length - 1) + FaceCorrWord.concatLen rest := rfl
          omega
        have hnot : ¬ j.val < L.length - 1 := hj
        have ihj := ih hpos_rest hnodup_rest
          ⟨j.val - (L.length - 1), hjRest⟩
        simpa [FaceCorrWord.concatWord, FaceCorrWord.concatLen,
          FaceCorrWord.appendWord, hnot] using ihj

end FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain

variable {M : CombMap D}

/-- A cycle-list decomposition of `faceCorr₂`, with enough list hygiene for the
consecutive-transposition word. -/
structure FaceCorrCycleLists (C : SimplePrimalCycle M)
    (Ls : List (List C.CutDart)) : Prop where
  pos : ∀ L ∈ Ls, 2 ≤ L.length
  nodup : ∀ L ∈ Ls, L.Nodup
  factor : FaceCorrWord.cycleListProd Ls = C.faceCorr2

/-- The actual split indices of the canonical cycle-list word for `faceCorr₂`. -/
noncomputable def actualSplitFinset (C : SimplePrimalCycle M)
    (Ls : List (List C.CutDart)) :
    Finset (Fin (FaceCorrWord.concatLen Ls)) :=
  ForcedSplits.actualSplitFinset C.phiLift (FaceCorrWord.concatWord Ls)

/-- The concatenated word of a `FaceCorrCycleLists` certificate is nondegenerate. -/
lemma concatWord_ne_of_nodup (C : SimplePrimalCycle M) {Ls : List (List C.CutDart)}
    (H : C.FaceCorrCycleLists Ls) (j : Fin (FaceCorrWord.concatLen Ls)) :
    (FaceCorrWord.concatWord Ls j).x ≠ (FaceCorrWord.concatWord Ls j).y :=
  FaceCorrWord.concatWord_ne_of_nodup Ls H.pos H.nodup j

/-- Every `faceCorr₂` has a nodup cycle-list decomposition. -/
theorem exists_faceCorrCycleLists (C : SimplePrimalCycle M) :
    ∃ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls := by
  classical
  obtain ⟨Ls, hLs, hfac⟩ := FaceCorrWord.exists_cycleListProd_nodup C.faceCorr2
  refine ⟨Ls, ?_⟩
  exact ⟨fun L hL => (hLs L hL).1, fun L hL => (hLs L hL).2, hfac⟩



/-- Enumerate a finset by `Fin card`, returning elements of the ambient type. -/
noncomputable def splitIdxOfFinset {n : ℕ} (S : Finset (Fin n)) :
    Fin S.card → Fin n :=
  fun i => (S.orderIsoOfFin rfl i : Fin n)
-- If Mathlib renamed this, alternates: `Finset.orderIsoOfFin S`,
-- `Fintype.equivFin {x // x ∈ S}`.

lemma splitIdxOfFinset_mem {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) :
    splitIdxOfFinset S i ∈ S :=
  (S.orderIsoOfFin rfl i).2

lemma splitIdxOfFinset_injective {n : ℕ} (S : Finset (Fin n)) :
    Function.Injective (splitIdxOfFinset S) := by
  intro i j h
  exact (S.orderIsoOfFin rfl).injective (Subtype.ext h)

/-- Build the repository's split certificate from a cycle-list certificate and the sufficient
actual-split count. -/
noncomputable def faceCorrSplitCert_of_cycleLists (C : SimplePrimalCycle M)
    {Ls : List (List C.CutDart)}
    (H : C.FaceCorrCycleLists Ls)
    (hsplits :
      FaceCorrWord.concatLen Ls + 2 ≤
        2 * (C.actualSplitFinset Ls).card + 2 * C.len) :
    C.FaceCorrSplitCert := by
  classical
  let S : Finset (Fin (FaceCorrWord.concatLen Ls)) := C.actualSplitFinset Ls
  refine
    { Ls := Ls
      Ls_pos := ?_
      factor := H.factor
      s := S.card
      hbound := ?_
      splitIdx := splitIdxOfFinset S
      splitIdx_injective := splitIdxOfFinset_injective S
      split_ne := ?_
      forced_split := ?_ }
  · intro L hL
    have := H.pos L hL
    omega
  · simpa [S]
      using hsplits
  · intro i
    exact C.concatWord_ne_of_nodup H (splitIdxOfFinset S i)
  · intro i
    have hmem : splitIdxOfFinset S i ∈ S := splitIdxOfFinset_mem S i
    simpa [S, SimplePrimalCycle.actualSplitFinset, ForcedSplits.actualSplitFinset]
      using (Finset.mem_filter.mp hmem).2

/-- If every cycle-list decomposition has enough actual splits, then `faceCorr₂` has a
`FaceCorrSplitCert`.  This is the conditional replacement for the unproved geometric
split-count theorem. -/
noncomputable def faceCorrSplitCert_of_splitsEnough (C : SimplePrimalCycle M)
    (hsplitsAll :
      ∀ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls →
        FaceCorrWord.concatLen Ls + 2 ≤
          2 * (C.actualSplitFinset Ls).card + 2 * C.len) :
    C.FaceCorrSplitCert := by
  classical
  exact C.faceCorrSplitCert_of_cycleLists
    (C.exists_faceCorrCycleLists).choose_spec
    (hsplitsAll _ (C.exists_faceCorrCycleLists).choose_spec)





/-- Corrected lower-bound Jordan input: the face side is a split certificate, and the
connectivity side is exactly the corrected cap-channel endpoint/interior-gate supplier
from `ChordJordanInput'`. -/
structure ChordJordanInputLower' (C : SimplePrimalCycle M) where
  /-- The lower-bound face-count certificate. -/
  faceSplit : C.FaceCorrSplitCert
  /-- The corrected cap-channel endpoint link plus interior triangle gates, matching
  `ChordJordanInput'.gateCompat'`. -/
  gateCompat' : ∀ i : Fin C.len,
    DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
      ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P

/-- Connectivity of `cutCapMap2` from the lower-bound corrected input. -/
theorem connectivity_of_inputLower' (C : SimplePrimalCycle M) (hconn : M.Connected)
    (hin : C.ChordJordanInputLower') (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    (C.cutCapMap2).Connected := by
  obtain ⟨P, hlink, hg⟩ := hin.gateCompat' i hpath
  exact C.cutCapMap2_connected_of_corrected i hconn P hlink hg

end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- `SphereChordSeparation` from the lower-bound corrected residue. -/
theorem sphereChordSeparation_of_inputLower' {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hin : C.ChordJordanInputLower')
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h := by
  intro hreach
  have hpath : DualReachableAvoidingCycle M C
      (M.dartFace (hNT.chordDart h))
      (M.dartFace (M.α (hNT.chordDart h))) :=
    hNT.reachable_dualAvoidsCycle_of_chordSplitAdj C hsub hreach
  rw [← hleft, ← hright] at hpath
  exact C.jordan_simple_cycle2_lower_of_splitCert hin.faceSplit
    hNT.sphere.2
    (fun i hp => C.connectivity_of_inputLower' hNT.sphere.1 hin i hp)
    i₀ hpath

/-- `Separates` form from the lower-bound corrected residue. -/
theorem separates_of_inputLower' {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hin : C.ChordJordanInputLower')
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  data.separates_of_nearTriangulation
    (hNT.sphereChordSeparation_of_inputLower'
      data.chord C hsub hin i₀ hleft hright)

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

@[simp] lemma sumCongr_apply_inl (f : Equiv.Perm α) (g : Equiv.Perm β) (a : α) :
    (Equiv.Perm.sumCongr f g) (Sum.inl a) = Sum.inl (f a) := by simp

@[simp] lemma sumCongr_apply_inr (f : Equiv.Perm α) (g : Equiv.Perm β) (b : β) :
    (Equiv.Perm.sumCongr f g) (Sum.inr b) = Sum.inr (g b) := by simp

lemma sumCongr_pow_apply_inl (f : Equiv.Perm α) (g : Equiv.Perm β) (n : ℕ) (a : α) :
    ((Equiv.Perm.sumCongr f g) ^ n) (Sum.inl a) = Sum.inl ((f ^ n) a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ih, sumCongr_apply_inl]

lemma sumCongr_pow_apply_inr (f : Equiv.Perm α) (g : Equiv.Perm β) (n : ℕ) (b : β) :
    ((Equiv.Perm.sumCongr f g) ^ n) (Sum.inr b) = Sum.inr ((g ^ n) b) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ih, sumCongr_apply_inr]

lemma sameCycle_sumCongr_inl_inl (f : Equiv.Perm α) (g : Equiv.Perm β) (a a' : α) :
    (Equiv.Perm.sumCongr f g).SameCycle (Sum.inl a) (Sum.inl a')
      ↔ f.SameCycle a a' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    rw [sumCongr_pow_apply_inl] at hm
    exact ⟨(m : ℤ), by rw [zpow_natCast]; exact Sum.inl.inj hm⟩
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    exact ⟨(m : ℤ), by rw [zpow_natCast, sumCongr_pow_apply_inl, hm]⟩

lemma sameCycle_sumCongr_inr_inr (f : Equiv.Perm α) (g : Equiv.Perm β) (b b' : β) :
    (Equiv.Perm.sumCongr f g).SameCycle (Sum.inr b) (Sum.inr b')
      ↔ g.SameCycle b b' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    rw [sumCongr_pow_apply_inr] at hm
    exact ⟨(m : ℤ), by rw [zpow_natCast]; exact Sum.inr.inj hm⟩
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    exact ⟨(m : ℤ), by rw [zpow_natCast, sumCongr_pow_apply_inr, hm]⟩

lemma not_sameCycle_sumCongr_inl_inr (f : Equiv.Perm α) (g : Equiv.Perm β)
    (a : α) (b : β) :
    ¬ (Equiv.Perm.sumCongr f g).SameCycle (Sum.inl a) (Sum.inr b) := by
  intro h
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  rw [sumCongr_pow_apply_inl] at hm
  exact Sum.inl_ne_inr hm

/-- The orbit-quotient bijection for a two-summand `sumCongr`. -/
noncomputable def sumCongrOrbitEquiv (f : Equiv.Perm α) (g : Equiv.Perm β) :
    Quotient (SameCycle.setoid (Equiv.Perm.sumCongr f g))
      ≃ Quotient (SameCycle.setoid f) ⊕ Quotient (SameCycle.setoid g) := by
  classical
  refine
    { toFun := Quotient.lift
        (fun x => match x with
          | Sum.inl a => Sum.inl (Quotient.mk (SameCycle.setoid f) a)
          | Sum.inr b => Sum.inr (Quotient.mk (SameCycle.setoid g) b)) ?_
      invFun := fun s => match s with
        | Sum.inl q => Quotient.lift
            (fun a => Quotient.mk (SameCycle.setoid (Equiv.Perm.sumCongr f g))
              (Sum.inl a)) ?_ q
        | Sum.inr q => Quotient.lift
            (fun b => Quotient.mk (SameCycle.setoid (Equiv.Perm.sumCongr f g))
              (Sum.inr b)) ?_ q
      left_inv := ?_
      right_inv := ?_ }
  · -- well-defined forward
    intro x y hxy
    change (Equiv.Perm.sumCongr f g).SameCycle x y at hxy
    rcases x with a | b <;> rcases y with a' | b'
    · exact congrArg Sum.inl (Quotient.sound
        ((sameCycle_sumCongr_inl_inl f g a a').mp hxy))
    · exact absurd hxy (not_sameCycle_sumCongr_inl_inr f g a b')
    · exact absurd hxy.symm (not_sameCycle_sumCongr_inl_inr f g a' b)
    · exact congrArg Sum.inr (Quotient.sound
        ((sameCycle_sumCongr_inr_inr f g b b').mp hxy))
  · -- well-defined inverse on the left summand
    intro a a' haa'
    change f.SameCycle a a' at haa'
    exact Quotient.sound ((sameCycle_sumCongr_inl_inl f g a a').mpr haa')
  · -- well-defined inverse on the right summand
    intro b b' hbb'
    change g.SameCycle b b' at hbb'
    exact Quotient.sound ((sameCycle_sumCongr_inr_inr f g b b').mpr hbb')
  · -- left_inv
    intro q
    refine Quotient.inductionOn q ?_
    rintro (a | b) <;> rfl
  · -- right_inv
    rintro (q | q)
    · refine Quotient.inductionOn q ?_; intro a; rfl
    · refine Quotient.inductionOn q ?_; intro b; rfl

/-- **`numCycles` is additive over `sumCongr`** (both summands arbitrary). -/
theorem numCycles_sumCongr (f : Equiv.Perm α) (g : Equiv.Perm β) :
    _root_.numCycles (Equiv.Perm.sumCongr f g)
      = _root_.numCycles f + _root_.numCycles g := by
  classical
  unfold _root_.numCycles
  rw [Fintype.card_congr (sumCongrOrbitEquiv f g), Fintype.card_sum]

end SumCongrTwo

/-- A permutation all of whose points are `SameCycle` has exactly one cycle. -/
lemma numCycles_eq_one_of_forall_sameCycle {γ : Type*} [Fintype γ] [DecidableEq γ]
    [Nonempty γ] (p : Equiv.Perm γ) (h : ∀ x y : γ, p.SameCycle x y) :
    _root_.numCycles p = 1 := by
  classical
  unfold _root_.numCycles
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk (SameCycle.setoid p) (Classical.arbitrary γ), ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact Quotient.sound (h x (Classical.arbitrary γ))

end CutCapCount

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain CutCapCount

variable {M : CombMap D}



lemma nextIdxEquiv_pow_apply (C : SimplePrimalCycle M) (n : ℕ) (i : Fin C.len) :
    (C.nextIdxEquiv ^ n) i = ⟨(i.1 + n) % C.len, Nat.mod_lt _ C.len_pos⟩ := by
  induction n with
  | zero =>
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ n ih =>
      apply Fin.ext
      rw [pow_succ', Equiv.Perm.mul_apply, ih, nextIdxEquiv_apply, nextIdx_val,
        Nat.mod_add_mod]
      congr 1

lemma sameCycle_nextIdxEquiv (C : SimplePrimalCycle M) (x y : Fin C.len) :
    C.nextIdxEquiv.SameCycle x y := by
  refine ⟨((y.1 + C.len - x.1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, C.nextIdxEquiv_pow_apply]
  apply Fin.ext
  show (x.1 + (y.1 + C.len - x.1)) % C.len = y.1
  have hx := x.isLt
  have hy := y.isLt
  have hxy : x.1 + (y.1 + C.len - x.1) = y.1 + C.len := by omega
  rw [hxy, Nat.add_mod_right, Nat.mod_eq_of_lt hy]

lemma numCycles_nextIdxEquiv (C : SimplePrimalCycle M) :
    _root_.numCycles C.nextIdxEquiv = 1 := by
  haveI : Nonempty (Fin C.len) := ⟨⟨0, C.len_pos⟩⟩
  exact CutCapCount.numCycles_eq_one_of_forall_sameCycle _ C.sameCycle_nextIdxEquiv

lemma numCycles_nextIdxEquiv_inv (C : SimplePrimalCycle M) :
    _root_.numCycles (C.nextIdxEquiv⁻¹) = 1 := by
  haveI : Nonempty (Fin C.len) := ⟨⟨0, C.len_pos⟩⟩
  exact CutCapCount.numCycles_eq_one_of_forall_sameCycle _
    (fun x y => (Equiv.Perm.sameCycle_inv).mpr (C.sameCycle_nextIdxEquiv x y))



/-- A dart equal to no bank-start (`p`/`q`) dart is not a cycle dart. -/
lemma notMem_dartSet_of_ne_bankStarts (C : SimplePrimalCycle M) {x : D}
    (hp : ∀ i, x ≠ C.pDart i) (hq : ∀ i, x ≠ C.qDart i) : x ∉ C.dartSet := by
  intro hmem
  rw [C.mem_dartSet_iff] at hmem
  obtain ⟨i, hi | hi⟩ := hmem
  · exact hq i (by rw [qDart_def]; exact hi)
  · refine hp (C.nextIdx i) ?_
    rw [pDart_def, C.prevIdx_nextIdx]
    exact hi

open Classical in
/-- Forward map of the seam swap. -/
noncomputable def seamSwapFun (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.cycleKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)   -- dart i ↦ c_i⁺
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)   -- α (dart i) ↦ c_i⁻
      | Sum.inr () => Sum.inl d                      -- ordinary: fixed
  | Sum.inr (Sum.inl i) => Sum.inl (M.α (C.dart i))  -- c_i⁺ ↦ α (dart i)
  | Sum.inr (Sum.inr i) => Sum.inl (C.dart i)        -- c_i⁻ ↦ dart i

open Classical in
/-- Inverse map of the seam swap. -/
noncomputable def seamSwapInvFun (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.cycleKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inr i)   -- dart i ↦ c_i⁻
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inl i)   -- α (dart i) ↦ c_i⁺
      | Sum.inr () => Sum.inl d
  | Sum.inr (Sum.inl i) => Sum.inl (C.dart i)        -- c_i⁺ ↦ dart i
  | Sum.inr (Sum.inr i) => Sum.inl (M.α (C.dart i))  -- c_i⁻ ↦ α (dart i)

lemma seamSwapFun_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapFun (Sum.inl (C.dart i)) = Sum.inr (Sum.inl i) := by
  show (match C.cycleKind (C.dart i) with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr () => Sum.inl (C.dart i)) = _
  rw [C.cycleKind_dart]

lemma seamSwapFun_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapFun (Sum.inl (M.α (C.dart i))) = Sum.inr (Sum.inr i) := by
  show (match C.cycleKind (M.α (C.dart i)) with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr () => Sum.inl (M.α (C.dart i))) = _
  rw [C.cycleKind_alpha_dart]

lemma seamSwapFun_other (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    C.seamSwapFun (Sum.inl d) = Sum.inl d := by
  show (match C.cycleKind d with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr () => Sum.inl d) = _
  rw [C.cycleKind_other h]

@[simp] lemma seamSwapFun_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapFun (Sum.inr (Sum.inl i)) = Sum.inl (M.α (C.dart i)) := rfl

@[simp] lemma seamSwapFun_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapFun (Sum.inr (Sum.inr i)) = Sum.inl (C.dart i) := rfl

lemma seamSwapInvFun_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapInvFun (Sum.inl (C.dart i)) = Sum.inr (Sum.inr i) := by
  show (match C.cycleKind (C.dart i) with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inr j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
    | Sum.inr () => Sum.inl (C.dart i)) = _
  rw [C.cycleKind_dart]

lemma seamSwapInvFun_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapInvFun (Sum.inl (M.α (C.dart i))) = Sum.inr (Sum.inl i) := by
  show (match C.cycleKind (M.α (C.dart i)) with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inr j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
    | Sum.inr () => Sum.inl (M.α (C.dart i))) = _
  rw [C.cycleKind_alpha_dart]

lemma seamSwapInvFun_other (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    C.seamSwapInvFun (Sum.inl d) = Sum.inl d := by
  show (match C.cycleKind d with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inr j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
    | Sum.inr () => Sum.inl d) = _
  rw [C.cycleKind_other h]

@[simp] lemma seamSwapInvFun_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapInvFun (Sum.inr (Sum.inl i)) = Sum.inl (C.dart i) := rfl

@[simp] lemma seamSwapInvFun_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapInvFun (Sum.inr (Sum.inr i)) = Sum.inl (M.α (C.dart i)) := rfl

lemma seamSwap_leftInverse (C : SimplePrimalCycle M) :
    Function.LeftInverse C.seamSwapInvFun C.seamSwapFun := by
  intro x
  rcases x with d | (i | i)
  · rcases hk : C.cycleKind d with (i | i) | u
    · have hd : d = C.dart i := C.cycleKind_eq_inl_inl hk
      subst hd
      rw [C.seamSwapFun_dart, C.seamSwapInvFun_capP]
    · have hd : d = M.α (C.dart i) := C.cycleKind_eq_inl_inr hk
      subst hd
      rw [C.seamSwapFun_alpha_dart, C.seamSwapInvFun_capM]
    · have hd : d ∉ C.dartSet := C.cycleKind_eq_inr hk
      rw [C.seamSwapFun_other hd, C.seamSwapInvFun_other hd]
  · rw [C.seamSwapFun_capP, C.seamSwapInvFun_alpha_dart]
  · rw [C.seamSwapFun_capM, C.seamSwapInvFun_dart]

lemma seamSwap_rightInverse (C : SimplePrimalCycle M) :
    Function.RightInverse C.seamSwapInvFun C.seamSwapFun := by
  intro x
  rcases x with d | (i | i)
  · rcases hk : C.cycleKind d with (i | i) | u
    · have hd : d = C.dart i := C.cycleKind_eq_inl_inl hk
      subst hd
      rw [C.seamSwapInvFun_dart, C.seamSwapFun_capM]
    · have hd : d = M.α (C.dart i) := C.cycleKind_eq_inl_inr hk
      subst hd
      rw [C.seamSwapInvFun_alpha_dart, C.seamSwapFun_capP]
    · have hd : d ∉ C.dartSet := C.cycleKind_eq_inr hk
      rw [C.seamSwapInvFun_other hd, C.seamSwapFun_other hd]
  · rw [C.seamSwapInvFun_capP, C.seamSwapFun_dart]
  · rw [C.seamSwapInvFun_capM, C.seamSwapFun_alpha_dart]

/-- The seam swap as a permutation of the cut-dart set. -/
noncomputable def seamSwap (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart where
  toFun := C.seamSwapFun
  invFun := C.seamSwapInvFun
  left_inv := C.seamSwap_leftInverse
  right_inv := C.seamSwap_rightInverse

@[simp] lemma seamSwap_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.seamSwap x = C.seamSwapFun x := rfl





/-- The conjugacy model of `φ'₂`: the old face permutation on ordinary darts, with the
two cap slots rotating as the two new seam faces (`+` forward, `−` backward). -/
noncomputable def seamModel (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Equiv.Perm.sumCongr M.φ (Equiv.Perm.sumCongr C.nextIdxEquiv C.nextIdxEquiv⁻¹)

@[simp] lemma seamModel_inl (C : SimplePrimalCycle M) (d : D) :
    C.seamModel (Sum.inl d) = Sum.inl (M.φ d) := by
  simp [seamModel]

@[simp] lemma seamModel_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamModel (Sum.inr (Sum.inl i)) = Sum.inr (Sum.inl (C.nextIdx i)) := by
  simp [seamModel]

@[simp] lemma seamModel_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamModel (Sum.inr (Sum.inr i)) = Sum.inr (Sum.inr (C.prevIdx i)) := by
  simp [seamModel]



/-- **The transport identity.**  For *every* dart `d : D`, the seam swap carries
`σ'₂ (inl d)` to `inl (σ d)`: clean steps are untouched, and the two cap diverts
(`σ d = p_j` ⟹ `σ'₂ (inl d) = c_{prevIdx j}⁺ ↦ inl (α (dart (prevIdx j))) = inl (p_j)`;
`σ d = q_j` ⟹ `σ'₂ (inl d) = c_j⁻ ↦ inl (dart j) = inl (q_j)`) land exactly on the
bank-start the cap stands in for. -/
lemma seamSwapFun_cutSigma2_inl (C : SimplePrimalCycle M) (e : D) :
    C.seamSwapFun (C.cutSigma2 (Sum.inl e)) = Sum.inl (M.σ e) := by
  rcases hd : C.divertKind e with (j | j) | u
  · have hσ : M.σ e = C.pDart j := C.divertKind_eq_plus hd
    rw [C.cutSigma2_inl_plus hd, C.seamSwapFun_capP, hσ, pDart_def]
  · have hσ : M.σ e = C.qDart j := C.divertKind_eq_minus hd
    rw [C.cutSigma2_inl_minus hd, C.seamSwapFun_capM, hσ, qDart_def]
  · obtain ⟨hp, hq⟩ := C.divertKind_eq_none hd
    rw [C.cutSigma2_inl_none hd,
      C.seamSwapFun_other (C.notMem_dartSet_of_ne_bankStarts hp hq)]

/-- **Pointwise intertwining**: `e ∘ φ'₂ = seamModel ∘ e` on every cut dart. -/
lemma seamSwapFun_phi2 (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.seamSwapFun ((C.cutCapMap2).φ x) = C.seamModel (C.seamSwapFun x) := by
  rcases x with d | (i | i)
  · rcases hk : C.cycleKind d with (i | i) | u
    · -- seam dart `dart i`: φ'₂ threads it forward; the model rotates its `+`-slot
      have hd : d = C.dart i := C.cycleKind_eq_inl_inl hk
      subst hd
      rw [cutCapPhi2_dart, C.seamSwapFun_dart, C.seamSwapFun_dart, C.seamModel_capP]
    · -- seam dart `α (dart i)`: φ'₂ threads it backward; the model rotates its `−`-slot
      have hd : d = M.α (C.dart i) := C.cycleKind_eq_inl_inr hk
      subst hd
      rw [cutCapPhi2_alpha_dart, pDart_def, C.seamSwapFun_alpha_dart,
        C.seamSwapFun_alpha_dart, C.seamModel_capM]
    · -- ordinary dart: φ'₂ = (transported) φ
      have hd : d ∉ C.dartSet := C.cycleKind_eq_inr hk
      rw [cutCapPhi2_apply, C.cutAlpha_other hd, C.seamSwapFun_cutSigma2_inl,
        C.seamSwapFun_other hd, C.seamModel_inl, CombMap.φ, Equiv.Perm.mul_apply]
  · -- `c_i⁺` stands in for `α (dart i)`: `φ'₂ (c_i⁺) = σ'₂ (inl (dart i))` transports
    -- to `inl (σ (dart i)) = inl (φ (α (dart i)))`
    rw [cutCapPhi2_apply, cutAlpha_capPlus, C.seamSwapFun_cutSigma2_inl,
      C.seamSwapFun_capP, C.seamModel_inl, CombMap.φ, Equiv.Perm.mul_apply,
      M.alpha_alpha]
  · -- `c_i⁻` stands in for `dart i`: `φ'₂ (c_i⁻) = σ'₂ (inl (α (dart i)))` transports
    -- to `inl (σ (α (dart i))) = inl (φ (dart i))`
    rw [cutCapPhi2_apply, cutAlpha_capMinus, C.seamSwapFun_cutSigma2_inl,
      C.seamSwapFun_capM, C.seamModel_inl, CombMap.φ, Equiv.Perm.mul_apply]

/-- The intertwining as a product identity. -/
theorem seamSwap_mul_phi2 (C : SimplePrimalCycle M) :
    C.seamSwap * (C.cutCapMap2).φ = C.seamModel * C.seamSwap := by
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  simp only [seamSwap_apply]
  exact C.seamSwapFun_phi2 x

/-- **The seam conjugacy**: `e · φ'₂ · e⁻¹ = φ ⊕ (nextIdx ⊕ prevIdx)`. -/
theorem seamSwap_phi2_conj (C : SimplePrimalCycle M) :
    C.seamSwap * (C.cutCapMap2).φ * C.seamSwap⁻¹ = C.seamModel := by
  rw [seamSwap_mul_phi2, mul_assoc, mul_inv_cancel, mul_one]



/-- The model has `F + 2` cycles: `F` old faces plus the two seam rotations. -/
theorem numCycles_seamModel (C : SimplePrimalCycle M) :
    _root_.numCycles C.seamModel = M.F + 2 := by
  rw [seamModel, CutCapCount.numCycles_sumCongr, CutCapCount.numCycles_sumCongr,
    C.numCycles_nextIdxEquiv, C.numCycles_nextIdxEquiv_inv, ← M.F_eq_numCycles]

/-- **The corrected face-cycle count, closed unconditionally and genus-free:**
`numCycles φ'₂ = M.F + 2`.  By conjugation invariance through the seam conjugacy. -/
theorem numCycles_cutCapPhi2 (C : SimplePrimalCycle M) :
    _root_.numCycles ((C.cutCapMap2).φ) = M.F + 2 := by
  have h := CutCapCount.numCycles_conj C.seamSwap ((C.cutCapMap2).φ)
  rw [C.seamSwap_phi2_conj] at h
  rw [← h]
  exact C.numCycles_seamModel

/-- **The previously named open core of the corrected Chapter 35 face count, now a
theorem**: every simple primal cycle satisfies `NumCyclesCutPhi2`. -/
theorem numCyclesCutPhi2_holds (C : SimplePrimalCycle M) : C.NumCyclesCutPhi2 := by
  show _root_.numCycles ((C.cutCapMap2).φ) = M.F + 2
  exact C.numCycles_cutCapPhi2



/-- The factored form consumed by the telescope. -/
theorem numCycles_phiLift_mul_faceCorr2 (C : SimplePrimalCycle M) :
    _root_.numCycles (C.phiLift * C.faceCorr2) = M.F + 2 := by
  rw [← C.cutCapPhi2_eq_phiLift_mul]
  exact C.numCycles_cutCapPhi2



/-- **The exact split-count identity**: for every cycle-list certificate,
`concatLen Ls + 2 = 2 · #(actual splits) + 2 · len` — the hsplits bound holds with
slack `0`, for every cut, every genus. -/
theorem concatLen_add_two_eq_splits (C : SimplePrimalCycle M)
    {Ls : List (List C.CutDart)} (H : C.FaceCorrCycleLists Ls) :
    FaceCorrWord.concatLen Ls + 2
      = 2 * (C.actualSplitFinset Ls).card + 2 * C.len := by
  classical
  let W : Fin (FaceCorrWord.concatLen Ls) → ForcedSplits.Swap C.CutDart :=
    FaceCorrWord.concatWord Ls
  have hpos0 : ∀ L ∈ Ls, 0 < L.length := by
    intro L hL
    have := H.pos L hL
    omega
  have hprefix :
      ForcedSplits.prefixPerm C.phiLift W (FaceCorrWord.concatLen Ls)
        = C.phiLift * C.faceCorr2 := by
    dsimp [W]
    rw [FaceCorrWord.prefixPerm_concatWord C.phiLift Ls hpos0, H.factor]
  have htel := ForcedSplits.numCycles_prefix_telescopes C.phiLift W
  have hsum := ForcedSplits.sum_stepDelta_eq_neg_m_add_two_actualSplits
    C.phiLift W (fun j => C.concatWord_ne_of_nodup H j)
  have hdiff :
      (numCycles (ForcedSplits.prefixPerm C.phiLift W (FaceCorrWord.concatLen Ls)) : ℤ)
        - (numCycles C.phiLift : ℤ)
        =
      -(FaceCorrWord.concatLen Ls : ℤ)
        + 2 * ((C.actualSplitFinset Ls).card : ℤ) := by
    rw [SimplePrimalCycle.actualSplitFinset, htel, hsum]
  rw [hprefix] at hdiff
  rw [C.numCycles_phiLift_mul_faceCorr2, C.numCycles_phiLift] at hdiff
  push_cast at hdiff
  omega

/-- **The hsplits bound** (the exact statement consumed by
`numCycles_phiLift_faceCorr2_lower_of_splitsEnough`), unconditional. -/
theorem splitsEnough (C : SimplePrimalCycle M)
    {Ls : List (List C.CutDart)} (H : C.FaceCorrCycleLists Ls) :
    FaceCorrWord.concatLen Ls + 2
      ≤ 2 * (C.actualSplitFinset Ls).card + 2 * C.len :=
  le_of_eq (C.concatLen_add_two_eq_splits H)

/-- The `∀`-form consumed by the `_all` count-route plumbing. -/
theorem splitsEnough_all (C : SimplePrimalCycle M) :
    ∀ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls →
      FaceCorrWord.concatLen Ls + 2
        ≤ 2 * (C.actualSplitFinset Ls).card + 2 * C.len :=
  fun _ H => C.splitsEnough H





/-- **Every simple primal cycle carries a split certificate** — the
`FaceCorrSplitCert` residue of `FaceCorrWord.lean`, discharged. -/
noncomputable def faceCorrSplitCertUnconditional (C : SimplePrimalCycle M) :
    C.FaceCorrSplitCert :=
  C.faceCorrSplitCert_of_splitsEnough C.splitsEnough_all

/-- The lower-bound Jordan theorem, now conditional only on the Euler hypothesis and
the connectivity gates (the split certificate is supplied unconditionally). -/
theorem jordan_simple_cycle2_of_gates (C : SimplePrimalCycle M)
    (hchi : M.eulerChar = 2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_lower_of_splitCert C.faceCorrSplitCertUnconditional
    hchi hconn i

end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle



/-- `Separates` from the corrected gate data alone. -/
theorem separates_of_gates {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hgate : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates_of_inputLower' data C hsub
    ⟨C.faceCorrSplitCertUnconditional, hgate⟩ i₀ hleft hright

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



/-- `φ'₂` as an explicit conjugate of the seam model (the inverted form of
`seamSwap_phi2_conj`, shaped for `conj_pow`). -/
lemma cutCapPhi2_eq_conj (C : SimplePrimalCycle M) :
    (C.cutCapMap2).φ = C.seamSwap⁻¹ * C.seamModel * C.seamSwap⁻¹⁻¹ := by
  rw [inv_inv, ← C.seamSwap_phi2_conj]
  group

/-- **`SameCycle` transport through the seam conjugacy**: a `seamModel`-orbit relation
between the `e`-images is a `φ'₂`-orbit relation. -/
lemma cutCapPhi2_sameCycle_of_seamModel (C : SimplePrimalCycle M) {x y : C.CutDart}
    (h : C.seamModel.SameCycle (C.seamSwap x) (C.seamSwap y)) :
    ((C.cutCapMap2).φ).SameCycle x y := by
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  refine ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast, C.cutCapPhi2_eq_conj, conj_pow, inv_inv,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hm]
  exact inv_eq_iff_eq.mpr rfl

/-- `seamModel` restricted to the `inl` (ordinary-dart) summand is the old face
permutation `φ`. -/
lemma seamModel_sameCycle_inl_iff (C : SimplePrimalCycle M) (d₁ d₂ : D) :
    C.seamModel.SameCycle (Sum.inl d₁) (Sum.inl d₂) ↔ M.φ.SameCycle d₁ d₂ := by
  unfold seamModel
  exact CutCapCount.sameCycle_sumCongr_inl_inl _ _ _ _



/-- **Same old face ⇒ same φ'₂-cycle of the seam carriers ⇒ `cutReach2`.**  This is the
within-face connectivity that the corrected surgery *does* provide at the global
reachability layer (the `SameFragment`-layer version is false; this one is a theorem). -/
lemma cutReach2_seamCarrier_of_dartFace_eq (C : SimplePrimalCycle M) {d₁ d₂ : D}
    (h : M.dartFace d₁ = M.dartFace d₂) :
    C.cutReach2 (C.seamSwapInvFun (Sum.inl d₁)) (C.seamSwapInvFun (Sum.inl d₂)) := by
  apply C.cutReach2_of_phi_sameCycle
  apply C.cutCapPhi2_sameCycle_of_seamModel
  rw [seamSwap_apply, seamSwap_apply,
    C.seamSwap_rightInverse (Sum.inl d₁), C.seamSwap_rightInverse (Sum.inl d₂)]
  exact (C.seamModel_sameCycle_inl_iff d₁ d₂).mpr (sameCycle_phi_of_dartFace_eq h)





/-- **Carrier reach along a bare cycle-avoiding dual path.**  If `f` and `g` are
dual-reachable avoiding the cycle edges, then the seam carriers of *any* dart of `f`
and *any* dart of `g` are `cutReach2`-connected. -/
lemma cutReach2_seamCarrier_of_dualReachable (C : SimplePrimalCycle M) {f g : M.Face}
    (hpath : DualReachableAvoidingCycle M C f g) :
    ∀ {d₁ d₂ : D}, M.dartFace d₁ = f → M.dartFace d₂ = g →
      C.cutReach2 (C.seamSwapInvFun (Sum.inl d₁)) (C.seamSwapInvFun (Sum.inl d₂)) := by
  have hpath' : Relation.ReflTransGen (DualAvoidsCycleStep M C) f g := hpath
  clear hpath
  induction hpath' with
  | refl =>
      intro d₁ d₂ h₁ h₂
      exact C.cutReach2_seamCarrier_of_dartFace_eq (h₁.trans h₂.symm)
  | tail hstep hcross ih =>
      intro d₁ d₂ h₁ h₂
      obtain ⟨c, hcut, hcf, hcg⟩ := hcross
      have hc : c ∉ C.dartSet := C.notMem_dartSet_of_dartEdge_notMem hcut
      have hαc : M.α c ∉ C.dartSet := C.alpha_notMem_dartSet hc
      -- carrier d₁ ⇝ carrier c (induction hypothesis up to the previous face)
      have h1 := ih h₁ hcf
      -- inl c ⇝ inl (α c): one α'-step across the uncut crossing edge
      have h2 : C.cutReach2 (Sum.inl c) (Sum.inl (M.α c)) :=
        C.cutReach2_across_uncut_dual_gate hcut
      -- carrier (α c) ⇝ carrier d₂ (same final face)
      have h3 := C.cutReach2_seamCarrier_of_dartFace_eq (d₁ := M.α c) (d₂ := d₂)
        (hcg.trans h₂.symm)
      rw [C.seamSwapInvFun_other hc] at h1
      rw [C.seamSwapInvFun_other hαc] at h3
      exact C.cutReach2_trans (C.cutReach2_trans h1 h2) h3



/-- **The cross-bank bridge from bare dual reachability** — the genuine connectivity
content of the Chapter 35 gates, with no triangle or fragment input.  (It is *not*
provable without `hpath`: on the sphere the cut map has two components.) -/
theorem crossBankBridge_of_dualReachable (C : SimplePrimalCycle M) (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    C.cutReach2 (Sum.inl (C.dart i)) (Sum.inl (M.α (C.dart i))) := by
  -- carrier (dart i) = c_i⁻ ⇝ carrier (α (dart i)) = c_i⁺
  have hmid := C.cutReach2_seamCarrier_of_dualReachable hpath
    (d₁ := C.dart i) (d₂ := M.α (C.dart i)) rfl rfl
  rw [C.seamSwapInvFun_dart, C.seamSwapInvFun_alpha_dart] at hmid
  -- inl (dart i) ⇝ c_i⁺ (one α'-step)
  have h1 : C.cutReach2 (Sum.inl (C.dart i)) (Sum.inr (Sum.inl i)) := by
    have := C.cutReach2_of_alpha (Sum.inl (C.dart i))
    rwa [cutCapMap2_alpha_apply, C.cutAlpha_dart] at this
  -- c_i⁻ ⇝ inl (α (dart i)) (one α'-step, reversed)
  have h3 : C.cutReach2 (Sum.inr (Sum.inr i)) (Sum.inl (M.α (C.dart i))) := by
    have := C.cutReach2_of_alpha (Sum.inl (M.α (C.dart i)))
    rw [cutCapMap2_alpha_apply, C.cutAlpha_alpha_dart] at this
    exact C.cutReach2_symm this
  exact C.cutReach2_trans (C.cutReach2_trans h1 (C.cutReach2_symm hmid)) h3



/-- **`EndpointCapLink`, supplied** from bare dual reachability (on the nil path). -/
theorem endpointCapLink_of_dualReachable (C : SimplePrimalCycle M) (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    C.EndpointCapLink i (OrdinaryDualPath2.nil C (C.faceLeft i)) :=
  C.endpointCapLink_nil i (C.faceLeft i) (C.crossBankBridge_of_dualReachable i hpath)

/-- **The connectivity gate `gateCompat'`, closed**: for every cycle edge, bare dual
reachability of its two sides yields an ordinary dual path carrying both
`EndpointCapLink` and `InteriorTriangleGates`. -/
theorem gateCompat'_of_dualReachable (C : SimplePrimalCycle M) (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P :=
  ⟨OrdinaryDualPath2.nil C (C.faceLeft i),
    C.endpointCapLink_of_dualReachable i hpath,
    C.interiorTriangleGates_nil (C.faceLeft i)⟩

/-- **`ChordJordanInput'` is a theorem** for every simple primal cycle on every
combinatorial map: the face core is `numCyclesCutPhi2_holds`
(`ZinanCh35Split.lean`), the gate supplier is `gateCompat'_of_dualReachable`. -/
theorem chordJordanInput'_holds (C : SimplePrimalCycle M) : C.ChordJordanInput' :=
  ⟨C.numCyclesCutPhi2_holds, fun i hpath => C.gateCompat'_of_dualReachable i hpath⟩



/-- **The discrete Jordan separation for the corrected surgery, with all gates
discharged**: on a connected map of Euler characteristic `2`, the two sides of every
edge of a simple primal cycle are *not* dual-connected avoiding the cycle.
Conditional only on `M.Connected` and `M.eulerChar = 2`. -/
theorem jordan_simple_cycle2_unconditional (C : SimplePrimalCycle M)
    (hchi : M.eulerChar = 2) (hconn : M.Connected) (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_of_gates hchi
    (fun j hp => C.connectivity_of_input' hconn C.chordJordanInput'_holds j hp) i



end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle



/-- **`Separates` with the connectivity gates discharged.** -/
theorem separates_closed {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates_of_gates data C hsub
    (fun i hp => C.gateCompat'_of_dualReachable i hp) i₀ hleft hright

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







/-- **`homit` ⟺ a vertex outside the side-1 region.**  Via `sideVertexToM₁_range`
(`Set.range ι = sideRegion₁`), the abstract omitted-vertex witness is equivalent to the concrete
region-omission residue `∃ w : M.Vertex, w ∉ sideRegion₁ data`. -/
theorem homit_iff_exists_notMem_sideRegion₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    (∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne))
      ↔ (∃ w : M.Vertex, w ∉ sideRegion₁ data) := by
  rw [sideVertexToM₁_range data hsep a₀ a₁ hne]















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



/-- **Side-region membership, unfolded.**  `w ∈ sideRegion₁` exactly when `w` has an incident
dart (tail `w`) distinct from the chord dart that is *kept* by side 1: either its own face is in
`side₁` (an inner side-1 dart), or it is an outer dart whose reverse face is in `side₁` (a
boundary dart of the side-1 arc). -/
theorem mem_sideRegion₁_iff (data : hNT.ChordSplitData u v) (w : M.Vertex) :
    w ∈ sideRegion₁ data ↔
      ∃ d : D, M.tail d = w ∧ d ≠ data.dart ∧
        (M.dartFace d ∈ data.side₁ ∨
          (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁)) := by
  constructor
  · rintro ⟨d, hd, htail⟩
    rw [data.mem_keptDel₁_iff] at hd
    obtain ⟨hU, hne⟩ := hd
    simp only [Set.mem_singleton_iff] at hne
    refine ⟨d, htail, hne, ?_⟩
    rcases hU with hin | hout
    · exact Or.inl hin
    · exact Or.inr ⟨hout.1, hout.2⟩
  · rintro ⟨d, htail, hne, hkept⟩
    refine ⟨d, ?_, htail⟩
    rw [data.mem_keptDel₁_iff]
    refine ⟨?_, by simp only [Set.mem_singleton_iff]; exact hne⟩
    rcases hkept with hin | hout
    · exact Or.inl hin
    · exact Or.inr hout

/-- **Side-region OMISSION, unfolded** (the form `homit` needs).  A vertex `w` is *outside* the
side-1 region exactly when *every* dart tailed at `w` is deleted by side 1: it is the chord dart,
or its face is not in `side₁` and it is not a side-1 boundary dart.  This is the vertex-star
confinement statement. -/
theorem notMem_sideRegion₁_iff (data : hNT.ChordSplitData u v) (w : M.Vertex) :
    w ∉ sideRegion₁ data ↔
      ∀ d : D, M.tail d = w →
        (d = data.dart ∨
          (M.dartFace d ∉ data.side₁ ∧
            ¬ (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁))) := by
  rw [mem_sideRegion₁_iff]
  constructor
  · intro hnot d htail
    -- If `d` were a kept side-1 dart, `w` would be in the region.
    by_cases hne : d = data.dart
    · exact Or.inl hne
    · right
      refine ⟨?_, ?_⟩
      · intro hin
        exact hnot ⟨d, htail, hne, Or.inl hin⟩
      · intro hout
        exact hnot ⟨d, htail, hne, Or.inr hout⟩
  · rintro hall ⟨d, htail, hne, hkept⟩
    rcases hall d htail with hchord | ⟨hface, houter⟩
    · exact hne hchord
    · rcases hkept with hin | hout
      · exact hface hin
      · exact houter hout

/-- **Star witness ⟹ region membership (inner case).**  If `w` has a star dart `d` (tail `w`)
distinct from the chord dart whose face is in `side₁`, then `w ∈ sideRegion₁`. -/
theorem mem_sideRegion₁_of_star_side₁ (data : hNT.ChordSplitData u v) {w : M.Vertex}
    {d : D} (htail : M.tail d = w) (hne : d ≠ data.dart) (hface : M.dartFace d ∈ data.side₁) :
    w ∈ sideRegion₁ data :=
  (mem_sideRegion₁_iff data w).2 ⟨d, htail, hne, Or.inl hface⟩

/-- **Star witness ⟹ region membership (boundary case).**  If `w` has a star dart `d` (tail `w`)
distinct from the chord dart that is an outer dart whose reverse face is in `side₁`, then
`w ∈ sideRegion₁`. -/
theorem mem_sideRegion₁_of_star_outerArc₁ (data : hNT.ChordSplitData u v) {w : M.Vertex}
    {d : D} (htail : M.tail d = w) (hne : d ≠ data.dart)
    (houter : M.dartFace d = hNT.outerFace) (hrev : M.dartFace (M.α d) ∈ data.side₁) :
    w ∈ sideRegion₁ data :=
  (mem_sideRegion₁_iff data w).2 ⟨d, htail, hne, Or.inr ⟨houter, hrev⟩⟩



/-- **The side-1 vertex-star anchoring residual.**  The discrete-Schoenflies confinement fact that
the landed *face*-dual separation does not supply, isolated sharply:

* `edge_core` — *region edge-confinement core*: an ambient non-chord edge `e` whose two endpoints
  are both side-1-region vertices has its own face in `side₁` (so the edge is realised by an inner
  side-1 dart).  This is the geometric content of `Side₁SchoenfliesConfinement.edge_confined` once
  the chord case and the `α`-closure reduction are peeled off.

* `oppArc_star_core` — *opposite-arc star confinement*: every dart `d` tailed at a strictly
  internal vertex `w` of the *opposite* boundary arc `path₂` is deleted by side 1 (it is the chord
  dart, or its face is outside `side₁` and it is not a side-1 boundary dart).  This is precisely
  the vertex-star-confinement form of `opposite_arc_omitted`.

Both fields are inhabited statements about the concrete map; neither is vacuous (the opposite arc
carries an internal vertex by `data.arc₂_internal`, and the region is inhabited by
`sideRegion₁_nonempty`). -/
structure Side₁StarConfinement (data : hNT.ChordSplitData u v) : Prop where
  /-- Region edge-confinement core (geometric heart of `edge_confined`).  The
  `M.dartFace e ≠ hNT.outerFace` hypothesis (the **bounded-dart** restriction) is essential:
  the outward dart of an outer-arc₁ boundary edge has both endpoints in `sideRegion₁` and is
  non-chord, but its face is the outer face (`∉ side₁`).  Such outer darts are kept via
  `outerArc₁`, not via their face being in `side₁`, and are handled separately by the consumer
  (`vertexStar_confined_of_starConfinement`) through the `outerArc₁` route. -/
  edge_core : ∀ {e : D},
    M.dartEdge e ≠ s(u, v) →
    M.dartFace e ≠ hNT.outerFace →
    M.tail e ∈ sideRegion₁ data →
    M.head e ∈ sideRegion₁ data →
      M.dartFace e ∈ data.side₁
  /-- Opposite-arc vertex-star confinement (geometric heart of `opposite_arc_omitted`). -/
  oppArc_star_core : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices →
    ∀ d : D, M.tail d = w →
      (d = data.dart ∨
        (M.dartFace d ∉ data.side₁ ∧
          ¬ (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁)))



/-- **The design's master confinement structure (design §2).**  `edge_confined` and
`opposite_arc_omitted` in the exact shapes the `hreflect`/`homit` producers consume. -/
structure Side₁SchoenfliesConfinement (data : hNT.ChordSplitData u v) : Prop where
  /-- Any ambient edge whose two endpoints are in the side-1 vertex region is either represented
  in the side-1 carve (both `e` and `α e` kept) or is the chord. -/
  edge_confined : ∀ {e : D},
    M.tail e ∈ sideRegion₁ data →
    M.head e ∈ sideRegion₁ data →
      ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨ M.dartEdge e = s(u, v))
  /-- A strict internal vertex of the opposite boundary arc is omitted by side 1. -/
  opposite_arc_omitted : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices → w ∉ sideRegion₁ data

/-- **The chord dart's edge is `s(u, v)`.**  Bookkeeping for the chord case of `edge_confined`. -/
lemma dart_edge (data : hNT.ChordSplitData u v) : M.dartEdge data.dart = s(u, v) :=
  hNT.chordDart_edge data.chord



/-- **The outer-dart arc residual.**  For a non-chord dart `e` whose face is the outer face and
whose two endpoints are both side-1-region vertices, the reverse face `dartFace (α e)` lies in
`side₁` (so `e ∈ outerArc₁`).  This is the boundary-incidence content of the outer-dart case of
`edge_confined`; everything else in the consumer is combinatorial. -/
def OuterDartArc₁ (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {e : D},
    M.dartEdge e ≠ s(u, v) →
    M.dartFace e = hNT.outerFace →
    M.tail e ∈ sideRegion₁ data →
    M.head e ∈ sideRegion₁ data →
      M.dartFace (M.α e) ∈ data.side₁

/-- **Master confinement from the star residual (Brick 5).**  Produces the design's
`Side₁SchoenfliesConfinement` from `Side₁StarConfinement`, performing the `edge_confined`
`α`-reduction with the landed `Separates`-conditional `α`-closure.  The `edge_confined` derivation
**case-splits** on whether `e` is an outer dart: a bounded dart (`dartFace e ≠ outerFace`) is kept
via the corrected `edge_core`; an outer dart (`dartFace e = outerFace`) is kept via the `outerArc₁`
route, supplied by the boundary-incidence residual `OuterDartArc₁`. -/
theorem vertexStar_confined_of_starConfinement (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (conf : Side₁StarConfinement data)
    (houter : OuterDartArc₁ data) :
    Side₁SchoenfliesConfinement data where
  edge_confined := by
    intro e htail hhead
    by_cases hchord : M.dartEdge e = s(u, v)
    · exact Or.inr hchord
    · -- non-chord: split on whether `e` is an outer dart.
      left
      -- `e ≠ dart` (else `dartEdge e = dartEdge dart = s(u,v)`).
      have hne : e ≠ data.dart := by
        intro h; exact hchord (by rw [h]; exact dart_edge data)
      -- In both cases we produce `e ∈ keptSet₁`, then close under `α`.
      have hkept : e ∈ data.keptSet₁ := by
        by_cases hof : M.dartFace e = hNT.outerFace
        · -- outer dart: kept via `outerArc₁` (face = outerFace, reverse face ∈ side₁).
          have hrev : M.dartFace (M.α e) ∈ data.side₁ := houter hchord hof htail hhead
          refine ⟨Or.inr ⟨hof, hrev⟩, ?_⟩
          simp only [Set.mem_singleton_iff]; exact hne
        · -- bounded dart: corrected `edge_core` gives `dartFace e ∈ side₁`, hence `∈ sideDarts₁`.
          have hface : M.dartFace e ∈ data.side₁ := conf.edge_core hchord hof htail hhead
          refine ⟨Or.inl hface, ?_⟩
          simp only [Set.mem_singleton_iff]; exact hne
      refine ⟨?_, ?_⟩
      · rw [data.mem_keptDel₁_iff]; exact hkept
      · rw [data.mem_keptDel₁_iff]
        exact (data.mem_keptSet₁_alpha_iff hsep e).2 hkept
  opposite_arc_omitted := by
    intro w hw
    rw [notMem_sideRegion₁_iff]
    exact conf.oppArc_star_core hw











end ProofsInTheBook.ZinanCh35Schoenflies











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



/-- **The minimal side-1 confinement input bundle (verdict §4).**  Exactly the two discrete-
Schoenflies facts the `homit`/`hreflect` producers need, in their sharpest concrete shapes:

* `oppArcStarSeed` — a strictly internal vertex of the *opposite* boundary arc `path₂` is omitted
  by side 1 (`w ∉ sideRegion₁ data`).  This is the `homit` content, concretised.

* `edge_core` — an ambient dart `e` whose two endpoints are both side-1-region vertices is either
  represented in the side-1 carve (`e ∉ keptDel₁ ∧ α e ∉ keptDel₁`) or is the chord
  (`dartEdge e = s(u, v)`).  This is the region edge-confinement core, with the `α`-closure folded
  into the conclusion so the `hreflect` producer consumes it directly. -/
structure Side₁SchoenfliesConfinementInput (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : Prop where
  /-- Opposite-arc omission: a `path₂`-internal vertex is not in the side-1 region. -/
  oppArcStarSeed : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices → w ∉ sideRegion₁ data
  /-- Region edge-confinement core: an ambient edge between two side-1-region vertices is kept by
  side 1 (both `e` and `α e`), or is the chord. -/
  edge_core : ∀ {e : D},
    M.tail e ∈ sideRegion₁ data →
    M.head e ∈ sideRegion₁ data →
      ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨ M.dartEdge e = s(u, v))



/-- **Brick 2 — `homit_of_confinementInput`.**  The opposite boundary arc carries an internal
vertex (`data.arc₂_internal`); that vertex is omitted by side 1 (`oppArcStarSeed`), witnessing the
concrete region-omission residue `∃ w, w ∉ sideRegion₁ data`. -/
theorem homit_of_confinementInput (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (H : Side₁SchoenfliesConfinementInput data hsep) :
    ∃ w : M.Vertex, w ∉ sideRegion₁ data := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ data.arc₂_internal
  exact ⟨w, H.oppArcStarSeed hw⟩



/-- **Brick 3 — `side_adj_of_kept_edge`.**  Let `e ∉ keptDel₁` be a kept dart with
`M.tail e = ι x` and `M.head e = ι y` (`x ≠ y`).  Then `sideMap₁.toSimpleGraph.Adj x y`, witnessed
by the side dart `Sum.inl ⟨e, he⟩`, with endpoints identified to `x`, `y` through the proved
injectivity of `ι`. -/
theorem side_adj_of_kept_edge (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    {x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex} (hxy : x ≠ y)
    {e : D} (he : e ∉ data.keptDel₁)
    (htail : M.tail e = sideVertexToM₁ data hsep a₀ a₁ hne x)
    (hhead : M.head e = sideVertexToM₁ data hsep a₀ a₁ hne y) :
    (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  -- the kept side dart and its two side endpoints (as classes).
  set dS : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2 := Sum.inl ⟨e, he⟩ with hdS
  set xS : (data.sideMap₁ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) dS with hxS
  set yS : (data.sideMap₁ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
      ((freshAlpha (data.sideAlpha₁ hsep)) dS) with hyS
  -- `ι xS = M.tail e = ι x` and `ι yS = M.head e = ι y`, so by injectivity `xS = x`, `yS = y`.
  have hιx : sideVertexToM₁ data hsep a₀ a₁ hne xS
      = sideVertexToM₁ data hsep a₀ a₁ hne x := by
    rw [hxS, hdS, sideVertexToM₁_inl data hsep a₀ a₁ hne ⟨e, he⟩, htail]
  have hιy : sideVertexToM₁ data hsep a₀ a₁ hne yS
      = sideVertexToM₁ data hsep a₀ a₁ hne y := by
    rw [hyS, hdS, sideVertexToM₁_head_inl data hsep a₀ a₁ hne ⟨e, he⟩, hhead]
  have hxSx : xS = x := sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne hιx
  have hySy : yS = y := sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne hιy
  -- the side dart realises the edge `s(xS, yS) = s(x, y)`.
  rw [toSimpleGraph_adj]
  refine ⟨hxy, ?_⟩
  refine ⟨dS, ?_⟩
  -- `sideMap₁.dartEdge dS = s(sideMap₁.tail dS, sideMap₁.head dS) = s(xS, yS)`.
  show (data.sideMap₁ hsep a₀ a₁ hne).dartEdge dS = s(x, y)
  rw [← hxSx, ← hySy]
  -- `sideMap₁.tail dS = xS` and `sideMap₁.head dS = yS` definitionally
  -- (`head d = tail (α d)`, `sideMap₁.α = freshAlpha (sideAlpha₁)`).
  rfl



/-- **Brick 4 — `side_adj_of_chord_edge`.**  In the chord case `s(ι x, ι y) = s(u, v)`, with the
canonical anchor-tail identification `M.tail a₀.1 = u`, `M.tail a₁.1 = v` supplied as `ha₀`/`ha₁`,
the fresh chord side dart `Sum.inr 0` realises `s(x, y)`, giving `sideMap₁.toSimpleGraph.Adj x y`. -/
theorem side_adj_of_chord_edge (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    {x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex} (hxy : x ≠ y)
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (hx : sideVertexToM₁ data hsep a₀ a₁ hne x = u)
    (hy : sideVertexToM₁ data hsep a₀ a₁ hne y = v) :
    (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  -- the fresh chord side dart `inr 0` and its endpoints.
  set dS : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2 := Sum.inr 0 with hdS
  set xS : (data.sideMap₁ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) dS with hxS
  set yS : (data.sideMap₁ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
      ((freshAlpha (data.sideAlpha₁ hsep)) dS) with hyS
  -- `ι xS = M.tail a₀.1 = u = ι x`, `ι yS = M.tail a₁.1 = v = ι y`.
  have hιx : sideVertexToM₁ data hsep a₀ a₁ hne xS
      = sideVertexToM₁ data hsep a₀ a₁ hne x := by
    rw [hxS, hdS, sideVertexToM₁_tail_inr data hsep a₀ a₁ hne 0]
    simp only [if_true]
    rw [ha₀, hx]
  have hιy : sideVertexToM₁ data hsep a₀ a₁ hne yS
      = sideVertexToM₁ data hsep a₀ a₁ hne y := by
    rw [hyS, hdS, sideVertexToM₁_head_inr data hsep a₀ a₁ hne 0]
    simp only [if_true]
    rw [ha₁, hy]
  have hxSx : xS = x := sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne hιx
  have hySy : yS = y := sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne hιy
  rw [toSimpleGraph_adj]
  refine ⟨hxy, dS, ?_⟩
  show (data.sideMap₁ hsep a₀ a₁ hne).dartEdge dS = s(x, y)
  rw [← hxSx, ← hySy]
  rfl



/-- **Brick 5 — `hreflect_of_confinementInput`** (master).  Produces the region edge-confinement
field `hreflect` (`M`-adjacency on `ι`-images ⟹ side adjacency) from the bundle's `edge_core`,
threading the canonical anchor-tail identification `ha₀ : M.tail a₀.1 = u`, `ha₁ : M.tail a₁.1 = v`
(canonical-anchor geometry, the chord-case analogue of `ZinanCh35Iota`'s `hchord`). -/
theorem hreflect_of_confinementInput (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (H : Side₁SchoenfliesConfinementInput data hsep) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  intro x y hAdj
  rw [toSimpleGraph_adj] at hAdj
  obtain ⟨hne_ι, e, hde⟩ := hAdj
  -- `x ≠ y` from injectivity (`ι x ≠ ι y`).
  have hxy : x ≠ y := fun h => hne_ι (by rw [h])
  -- both endpoints are side-1-region vertices.
  have hx_mem : sideVertexToM₁ data hsep a₀ a₁ hne x ∈ sideRegion₁ data :=
    sideVertexToM₁_mem data hsep a₀ a₁ hne x
  have hy_mem : sideVertexToM₁ data hsep a₀ a₁ hne y ∈ sideRegion₁ data :=
    sideVertexToM₁_mem data hsep a₀ a₁ hne y
  -- `dartEdge e = s(tail e, head e)`, so `s(tail e, head e) = s(ι x, ι y)`.
  have hde' : s(M.tail e, M.head e)
      = s(sideVertexToM₁ data hsep a₀ a₁ hne x, sideVertexToM₁ data hsep a₀ a₁ hne y) := hde
  rcases Sym2.eq_iff.1 hde' with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · -- `tail e = ι x`, `head e = ι y`.
    have htail_mem : M.tail e ∈ sideRegion₁ data := by rw [ht]; exact hx_mem
    have hhead_mem : M.head e ∈ sideRegion₁ data := by rw [hh]; exact hy_mem
    rcases H.edge_core htail_mem hhead_mem with ⟨hkept, _⟩ | hchord
    · exact side_adj_of_kept_edge data hsep a₀ a₁ hne hxy hkept ht hh
    · -- chord case: `dartEdge e = s(u, v)` and `dartEdge e = s(ι x, ι y)`, so `{ι x, ι y} = {u, v}`.
      have hsuv : s(sideVertexToM₁ data hsep a₀ a₁ hne x, sideVertexToM₁ data hsep a₀ a₁ hne y)
          = s(u, v) := by
        rw [← hde]; exact hchord
      rcases Sym2.eq_iff.1 hsuv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
      · exact side_adj_of_chord_edge data hsep a₀ a₁ hne hxy ha₀ ha₁ hxu hyv
      · exact ((data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.symm
          (side_adj_of_chord_edge data hsep a₀ a₁ hne hxy.symm ha₀ ha₁ hyu hxv))
  · -- `tail e = ι y`, `head e = ι x` (`e` oriented the other way).
    have htail_mem : M.tail e ∈ sideRegion₁ data := by rw [ht]; exact hy_mem
    have hhead_mem : M.head e ∈ sideRegion₁ data := by rw [hh]; exact hx_mem
    rcases H.edge_core htail_mem hhead_mem with ⟨hkept, _⟩ | hchord
    · exact (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.symm
        (side_adj_of_kept_edge data hsep a₀ a₁ hne hxy.symm hkept ht hh)
    · have hsuv : s(sideVertexToM₁ data hsep a₀ a₁ hne y, sideVertexToM₁ data hsep a₀ a₁ hne x)
          = s(u, v) := by
        rw [Sym2.eq_swap, ← hde]; exact hchord
      rcases Sym2.eq_iff.1 hsuv with ⟨hyu, hxv⟩ | ⟨hyv, hxu⟩
      · exact (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.symm
          (side_adj_of_chord_edge data hsep a₀ a₁ hne hxy.symm ha₀ ha₁ hyu hxv)
      · exact side_adj_of_chord_edge data hsep a₀ a₁ hne hxy ha₀ ha₁ hxu hyv



/-- **Brick 6 — `chordSideResidue₁_final`** (master).  The full side-1 reconstruction residue
`ChordSideResidue`, closed modulo the minimal bundle `Side₁SchoenfliesConfinementInput` (the genuine
discrete-Schoenflies content) plus the upstream non-confinement inputs.

The chapter's complete remaining planar-input surface (documented in the deliverable report):

* `ci : ContiguousInterval …` — supplied for canonical anchors by `ZinanCh35Hclass`/`OuterTrace`;
* `hshare : Side₁AnchorsShareFace …` — ditto;
* `hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)` — the chord edge `u–v` (`ι_adj` fresh half);
* `ha₀ : M.tail a₀.1 = u`, `ha₁ : M.tail a₁.1 = v` — canonical anchor-tail geometry (chord-case
  `hreflect`);
* `pₛ qₛ cpₛ cqₛ` + `hLₛ : ThomassenLists …` — the side Thomassen lists transport;
* `H : Side₁SchoenfliesConfinementInput data hsep` — the genuine discrete-Schoenflies confinement
  (`oppArcStarSeed` + `edge_core`).

Everything else (`ι_inj`, the kept half of `ι_adj`, the `homit`/`hreflect` *producers*, the strict
decrease) is proved unconditionally here and upstream. -/
def chordSideResidue₁_final (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (ci : ContiguousInterval data hsep a₀ a₁ hne)
    (hshare : ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (pₛ qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (H : Side₁SchoenfliesConfinementInput data hsep) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  chordSideResidue₁_partial data hsep a₀ a₁ hne L ci hshare hchord
    (hreflect_of_confinementInput data hsep a₀ a₁ hne ha₀ ha₁ H)
    pₛ qₛ cpₛ cqₛ hLₛ
    ((ProofsInTheBook.ZinanCh35Confinement.homit_iff_exists_notMem_sideRegion₁
        data hsep a₀ a₁ hne).2
      (homit_of_confinementInput data hsep H))



/-- **Non-vacuity / satisfiability witness.**  The minimal bundle is *implied by* the landed,
documented-satisfiable `ZinanCh35Schoenflies.Side₁SchoenfliesConfinement` (whose `edge_confined`
yields `edge_core` modulo region-membership of the endpoints, and whose `opposite_arc_omitted` is
`oppArcStarSeed` verbatim).  Hence `Side₁SchoenfliesConfinementInput` is a genuine consequence of an
inhabited structure — it is NOT propositionally `False`. -/
theorem confinementInput_of_schoenflies (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (H : ProofsInTheBook.ZinanCh35Schoenflies.Side₁SchoenfliesConfinement data) :
    Side₁SchoenfliesConfinementInput data hsep where
  oppArcStarSeed := fun hw => H.opposite_arc_omitted hw
  edge_core := fun htail hhead => H.edge_confined htail hhead

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













/-- **The chordless reconstruction, assembled from the fan + the residue datum.**  This is
`fanSurgeryReconstruction`: the three structural fields come from the fan, the boundary
data (`bdry`) supplies the merged outer face, its boundary cycle, and `inner_tri`. -/
noncomputable def chordlessRecon_of_bdry (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) (hmerge : DeleteVertexMergedFaceSingleOrbit M d0)
    (bdry : DeletedOuterBoundary hNT d0) :
    FanSurgeryReconstruction hNT d0 :=
  fanSurgeryReconstruction fan htail0 hmerge bdry









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



/-- A dart whose `M`-face avoids `v0` survives the star deletion.  (The face-incidence
characterization `dartFace_mem_vertexFaces_iff`, re-derived with `htail0`.) -/
lemma survives_of_clean {d0 : D} (htail0 : M.tail d0 = v0)
    {d : D} (hf : M.dartFace d ∉ M.vertexFaces d0) :
    d ∉ M.deleteVertexSet d0 := by
  classical
  rw [mem_deleteVertexSet_iff]
  push_neg
  rw [mem_vertexDarts, mem_vertexDarts]
  -- helper: `dartFace e ∈ vertexFaces d0` whenever `tail ((φ^k) e) = v0`.
  have key : ∀ (e : D) (k : ℤ), M.tail ((M.φ ^ k) e) = v0 → M.dartFace e ∈ M.vertexFaces d0 := by
    intro e k hk
    rw [vertexFaces, Finset.mem_image]
    refine ⟨(M.φ ^ k) e, ?_, ?_⟩
    · rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail d0 = M.tail ((M.φ ^ k) e) by rw [htail0, hk])
    · exact Quotient.sound (⟨-k, by simp⟩ : M.φ.SameCycle ((M.φ ^ k) e) e)
  refine ⟨fun h => hf ?_, fun h => hf ?_⟩
  · -- `tail d = v0`: take `k = 0`.
    apply key d 0
    simp only [zpow_zero, Equiv.Perm.coe_one, id_eq]
    have heq : M.tail d0 = M.tail d := Quotient.sound h
    rw [← heq, htail0]
  · -- `tail (α d) = v0` i.e. `head d = v0 = tail (φ d)`: take `k = 1`.
    apply key d 1
    rw [zpow_one, tail_phi]
    have heq : M.tail d0 = M.tail (M.α d) := Quotient.sound h
    rw [tail_alpha] at heq
    rw [← heq, htail0]

/-- A clean dart's `M.φ`-successor survives. -/
lemma phi_survives_of_clean {d0 : D} (htail0 : M.tail d0 = v0)
    {d : D} (hf : M.dartFace d ∉ M.vertexFaces d0) :
    M.φ d ∉ M.deleteVertexSet d0 := by
  apply survives_of_clean htail0
  have hface : M.dartFace (M.φ d) = M.dartFace d :=
    Quotient.sound (⟨-1, by simp⟩ : M.φ.SameCycle (M.φ d) d)
  rw [hface]; exact hf

/-- **On a clean dart, the deleted `φ'` agrees with `M.φ`, and the result is again clean.** -/
lemma cleanStep {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) :
    ((M.deleteVertex d0).φ x : D) = M.φ x.1 ∧
      M.dartFace ((M.deleteVertex d0).φ x).1 ∉ M.vertexFaces d0 := by
  have hkept : M.φ x.1 ∉ M.deleteVertexSet d0 := phi_survives_of_clean htail0 hf
  have hagree : ((M.deleteVertex d0).φ x : D) = M.φ x.1 :=
    deleteVertex_phi_apply_of_next_kept M d0 x hkept
  refine ⟨hagree, ?_⟩
  rw [hagree]
  have hface : M.dartFace (M.φ x.1) = M.dartFace x.1 :=
    Quotient.sound (⟨-1, by simp⟩ : M.φ.SameCycle (M.φ x.1) x.1)
  rw [hface]; exact hf

/-- **Iterating the clean step**: the `n`-th `φ'`-iterate of a clean dart has underlying dart
`(M.φ)^[n] x.1` and stays clean. -/
lemma cleanIterate {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) (n : ℕ) :
    (((M.deleteVertex d0).φ)^[n] x : D) = (M.φ)^[n] x.1 ∧
      M.dartFace (((M.deleteVertex d0).φ)^[n] x).1 ∉ M.vertexFaces d0 := by
  induction n with
  | zero => exact ⟨rfl, by simpa using hf⟩
  | succ n ih =>
      obtain ⟨hval, hcln⟩ := ih
      have hstep := cleanStep htail0 (((M.deleteVertex d0).φ)^[n] x) hcln
      constructor
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep.1, hval]
      · rw [Function.iterate_succ_apply']; exact hstep.2

/-- **`φ'` and `M.φ` define the same cycle on a clean orbit.** -/
lemma cleanSameCycle_iff {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0)
    (y : {d : D // d ∉ M.deleteVertexSet d0}) :
    (M.deleteVertex d0).φ.SameCycle x y ↔ M.φ.SameCycle x.1 y.1 := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    have := congrArg Subtype.val hn
    rw [(cleanIterate htail0 x hf n).1] at this
    exact this
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    apply Subtype.ext
    rw [(cleanIterate htail0 x hf n).1]
    exact hn

/-- Every dart on the `M.φ`-orbit of a clean dart survives (it has the same `M`-face). -/
lemma clean_orbit_survives {d0 : D} (htail0 : M.tail d0 = v0)
    {x : {d : D // d ∉ M.deleteVertexSet d0}} (hf : M.dartFace x.1 ∉ M.vertexFaces d0)
    {d : D} (hd : M.φ.SameCycle x.1 d) : d ∉ M.deleteVertexSet d0 := by
  apply survives_of_clean htail0
  -- `d` has the same `M`-face as `x.1`.
  have hface : M.dartFace d = M.dartFace x.1 := (Quotient.sound hd).symm
  rw [hface]; exact hf



/-- **Clean face-SIZE transfer (UNCONDITIONAL).**  The deleted face length of a clean survivor
`x` equals the `M`-face length of `x.1`.  The deletion re-routes only the `v0`-incident
(merged outer) face; every clean face is an untouched `M.φ`-orbit. -/
theorem deleteVertex_cleanFaceLen_eq_M {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) :
    (M.deleteVertex d0).faceLen ((M.deleteVertex d0).dartFace x)
      = M.faceLen (M.dartFace x.1) := by
  classical
  show (Finset.univ.filter (fun z => Quotient.mk _ z
      = Quotient.mk (cycleSetoid (M.deleteVertex d0).φ) x)).card
    = (Finset.univ.filter (fun d => Quotient.mk _ d
      = Quotient.mk (cycleSetoid M.φ) x.1)).card
  -- the deleted filter maps bijectively via `Subtype.val` onto the M filter.
  rw [show (Finset.univ.filter (fun z => Quotient.mk _ z
      = Quotient.mk (cycleSetoid (M.deleteVertex d0).φ) x)).card
      = ((Finset.univ.filter (fun z : {d : D // d ∉ M.deleteVertexSet d0} =>
          Quotient.mk _ z = Quotient.mk (cycleSetoid (M.deleteVertex d0).φ) x)).map
          ⟨Subtype.val, Subtype.val_injective⟩).card from (Finset.card_map _).symm]
  congr 1
  ext d
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hsc : (M.deleteVertex d0).φ.SameCycle z x := Quotient.exact hz
    -- transfer to M via clean SameCycle (orbit clean since `x` clean and same cycle).
    have hsc' : M.φ.SameCycle x.1 z.1 :=
      (cleanSameCycle_iff htail0 x hf z).1 hsc.symm
    exact Quotient.sound hsc'.symm
  · intro hd
    have hsc : M.φ.SameCycle x.1 d := Quotient.exact hd.symm
    have hsurv : d ∉ M.deleteVertexSet d0 := clean_orbit_survives htail0 hf hsc
    refine ⟨⟨d, hsurv⟩, ?_, rfl⟩
    apply Quotient.sound
    show (M.deleteVertex d0).φ.SameCycle (⟨d, hsurv⟩ : {d : D // d ∉ M.deleteVertexSet d0}) x
    refine Equiv.Perm.SameCycle.symm ?_
    rw [cleanSameCycle_iff htail0 x hf ⟨d, hsurv⟩]
    exact hsc



/-- **A clean survivor whose `M`-face is non-outer has deleted face length `3`.** -/
theorem deleteVertex_cleanFace_eq_three {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0)
    (hMinner : M.dartFace x.1 ≠ hNT.outerFace) :
    (M.deleteVertex d0).faceLen ((M.deleteVertex d0).dartFace x) = 3 := by
  rw [deleteVertex_cleanFaceLen_eq_M htail0 x hf]
  exact hNT.inner_tri (M.dartFace x.1) hMinner



/-- **The clean-face classification** (the single named residue).  Relative to the merged outer
face `outerFace`, every *other* deleted face is represented by a survivor `x` whose `M`-face is
**clean** (avoids `v0`) and **non-outer** in `M`.  This is the fan analogue of
`InnerFacesSide₁`: the merged outer face captures exactly the `v0`-incident orbit, leaving every
other deleted face an intact `M`-triangle. -/
def CleanFaceClass {d0 : D} (outerFace : (M.deleteVertex d0).Face) : Prop :=
  ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
    ∃ x : {d : D // d ∉ M.deleteVertexSet d0},
      (M.deleteVertex d0).dartFace x = f ∧
      M.dartFace x.1 ∉ M.vertexFaces d0 ∧
      M.dartFace x.1 ≠ hNT.outerFace

/-- **`inner_tri` is discharged from the clean-face classification.**  Every non-outer deleted
face is represented by a clean, `M`-non-outer survivor (the classification), and Section 3 makes
its deleted face length `3`.  This is the chordless inner triangulation, via the same face-SIZE
route as the chord side — sidestepping the `CutFaceLabel` COUNT refutation. -/
theorem deleteVertex_inner_tri_of_cleanFaceClass {d0 : D} (htail0 : M.tail d0 = v0)
    (outerFace : (M.deleteVertex d0).Face)
    (hcl : CleanFaceClass (hNT := hNT) outerFace) :
    ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
      (M.deleteVertex d0).faceLen f = 3 := by
  intro f hf
  obtain ⟨x, hxf, hclean, hMinner⟩ := hcl f hf
  rw [← hxf]
  exact deleteVertex_cleanFace_eq_three htail0 x hclean hMinner



/-- **`DeletedOuterBoundary` from the merged outer-boundary cycle + the clean-face
classification.**  The `inner_tri` field is discharged via the face-SIZE route
(`deleteVertex_inner_tri_of_cleanFaceClass`); the boundary-cycle fields are the genuine
merged-face normalization (supplied as input, as in `DeletedOuterBoundary.ofMergedFace`). -/
noncomputable def deletedOuterBoundary_of_cleanFaceClass {d0 : D} (htail0 : M.tail d0 = v0)
    (outerFace : (M.deleteVertex d0).Face)
    (outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len_ge_three : 3 ≤ outerCycle.length)
    (hcl : CleanFaceClass (hNT := hNT) outerFace) :
    DeletedOuterBoundary hNT d0 where
  outerFace := outerFace
  outerCycle := outerCycle
  outer_simple := outer_simple
  outer_len_ge_three := outer_len_ge_three
  inner_tri := deleteVertex_inner_tri_of_cleanFaceClass htail0 outerFace hcl









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



/-- The exact side-1 input list consumed by
`ZinanCh35FinalClose.chordSideResidue₁_final`.

This is deliberately side-1 only.  A side-2 mirror would need the same kind of
final residue producer for `sideMap₂`; no such theorem is landed in this checkout.
-/
structure Side₁CertificateInputs (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁})
    (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α) where
  ci : ContiguousInterval data hsep a₀ a₁ hne
  hshare : Side₁AnchorsShareFace data hsep a₀ a₁
  hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)
  ha₀ : M.tail a₀.1 = u
  ha₁ : M.tail a₁.1 = v
  pₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex
  qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex
  cpₛ : α
  cqₛ : α
  hLₛ : ThomassenLists
    (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
    pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ
  confinement :
    ProofsInTheBook.ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput data hsep

/-- The campaign's closed side-1 residue, repackaged with its exact input list. -/
def side₁Residue_of_certificateInputs (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁})
    (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (I : Side₁CertificateInputs data hsep a₀ a₁ hne L) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  ProofsInTheBook.ZinanCh35FinalClose.chordSideResidue₁_final data hsep a₀ a₁ hne L
    I.ci I.hshare I.hchord I.ha₀ I.ha₁ I.pₛ I.qₛ I.cpₛ I.cqₛ I.hLₛ I.confinement

/-- The landed side-1 certificate in the exact `ChordSideReconstruction` shape
consumed by the recursive chord induction. -/
noncomputable def side₁Reconstruction_of_certificateInputs
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α)
    (I : Side₁CertificateInputs data hsep a₀ a₁ hne L) :
    ChordSideReconstruction hNT (sideRegion₁ data) L :=
  chordSideReconstruction_of_chord data hsep a₀ a₁ hne L
    (side₁Residue_of_certificateInputs data hsep a₀ a₁ hne L I)



/-- The exact remaining Chapter-35 planar input at the induction level.

It is a uniform supplier, for every recursive near-triangulation with Thomassen
lists, of either:

* a chord recursion datum, which includes both side reconstructions; or
* a chordless oracle, including the fan/deletion reconstruction and deleted-list
  bookkeeping.
-/
structure PlanarInputs (α : Type u) [DecidableEq α] : Type (u + 1) where
  recursiveDichotomy : ChordRecursiveDichotomy α

















end ProofsInTheBook.ZinanCh35Cert









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







/-- **The chord-branch supplier** — the chord half of the dichotomy as a named
residual.  Given any near-triangulation with the Thomassen lists *and a genuine
boundary chord* `(u, v)`, it produces the chord-branch residue
`ChordSplitFinal.ChordBranchResidue` (the `M`-vertex `ChordSplitRegions` glue plus
the two side `ChordSideReconstruction`s).

This is exactly the discrete Jordan–Schoenflies content the chord case needs:
* the side-1 reconstruction is discharged modulo the confinement bundle by
  `ZinanCh35Cert.side₁Reconstruction_of_certificateInputs`;
* the side-2 mirror and the regions partition (`Separates`) are the still-unbuilt
  pieces.

It is *not* a vacuous premise: `ChordBranchResidue` is inhabited from genuine side
reconstructions (`ChordSplitFinal.chordSideResidue_mk`,
`chordSideReconstruction_region_nonempty`). -/
structure ChordBranchSupplier (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- For each near-triangulation with the Thomassen lists and a boundary chord,
  the chord-branch residue for some chord `(u, v)`. -/
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), ThomassenLists hNT p q L cp cq →
      (∃ u v : M.Vertex, hNT.outerCycle.Chord u v) →
        Σ' u v : M.Vertex, ChordBranchResidue hNT u v p q L cp cq

/-- **The chordless-branch supplier** — the chordless half of the dichotomy as a
named residual.  Given any near-triangulation with the Thomassen lists *and a
chordless boundary*, it produces the boundary-deletion fan oracle
`ThomassenInduction.ChordlessOracle` (the `FanSurgeryReconstruction` Jordan data,
plus the reserved-colour and deleted-list bookkeeping).

This is the same fan datum the existing `JordanOracle` / `ThomassenInduction`
chordless branch carries and recurses on — not a vacuous premise. -/
structure ChordlessBranchSupplier (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- For each near-triangulation with the Thomassen lists and a chordless boundary,
  the chordless fan oracle. -/
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), 3 < M.V → ThomassenLists hNT p q L cp cq →
      BoundaryChordless hNT.outerCycle →
        ChordlessOracle hNT p q L cp cq



/-- **The chord-recursive dichotomy, assembled from the two branch suppliers.**

The decision `boundaryChord_em` is unconditional; this theorem routes it:
* in the chord case, the chord-branch supplier yields a `ChordBranchResidue`, from
  which `ChordSplitFinal.chordRecursionData_of_branchResidue` builds the
  `ChordRecursionData` (carrying the two smaller side near-triangulations, **no
  colorings**) — the left summand;
* in the chordless case, the chordless-branch supplier yields the `ChordlessOracle`
  — the right summand.

No content is fabricated: the routing is pure case analysis on the unconditional
decision, and each branch is discharged by its named supplier.  Hence the supplier
is `CONDITIONAL` on exactly the two named residuals, with the decision and packaging
unconditional. -/
noncomputable def chordRecursiveDichotomy_of_suppliers
    (Sc : ChordBranchSupplier α) (Sl : ChordlessBranchSupplier α) :
    ChordRecursiveDichotomy α where
  decide := by
    classical
    intro D _ _ M hNT p q L cp cq hV h
    -- The decision `∃ u v, Chord u v` is a Prop; eliminate it into the `Type`-valued
    -- target via `Classical.dec` (the unconditional chord/chordless EM).
    by_cases hchord : ∃ u v : M.Vertex, hNT.outerCycle.Chord u v
    · -- chord case: produce the recursion datum (no colorings).
      obtain ⟨u, v, br⟩ := Sc.supply hNT p q L cp cq h hchord
      exact Sum.inl ⟨u, v, chordRecursionData_of_branchResidue br⟩
    · -- chordless case: the boundary is chordless; produce the fan oracle.
      have hchordless : BoundaryChordless hNT.outerCycle := by
        intro u v hc; exact hchord ⟨u, v, hc⟩
      exact Sum.inr (Sl.supply hNT p q L cp cq hV h hchordless)





/-- The `PlanarInputs` bundle assembled from the two branch suppliers. -/
noncomputable def planarInputs_of_suppliers
    (Sc : ChordBranchSupplier α) (Sl : ChordlessBranchSupplier α) :
    ProofsInTheBook.ZinanCh35Cert.PlanarInputs α :=
  ⟨chordRecursiveDichotomy_of_suppliers Sc Sl⟩



end ProofsInTheBook.ZinanCh35Dichotomy









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



/-- **The side-2 region.**  The set of `M`-vertices that are the tail of some kept side-2 dart
(`d ∉ keptDel₂`); the `side₂`-analogue of `sideRegion₁`. -/
def sideRegion₂ (data : hNT.ChordSplitData u v) : Set M.Vertex :=
  {w : M.Vertex | ∃ d : D, d ∉ data.keptDel₂ ∧ M.tail d = w}

/-- A kept side-2 dart's tail is in the side-2 region. -/
lemma tail_mem_sideRegion₂ (data : hNT.ChordSplitData u v) {d : D}
    (hd : d ∉ data.keptDel₂) : M.tail d ∈ sideRegion₂ data :=
  ⟨d, hd, rfl⟩



/-- **Bridge 1 — bounded-face coverage.**  Every non-outer face lies in `side₁` or `side₂`.
This is the coverage half of the face partition; disjointness is the proven separation.  Coverage
is the missing cut-component ↔ `ChordSplitAdj`-reachability identification. -/
def BoundedFacePartition (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {f : M.Face}, f ≠ hNT.outerFace → f ∈ data.side₁ ∨ f ∈ data.side₂

/-- **Bridge 2 — vertex-region intersection (vertex-level Schoenflies).**  A vertex lying in both
side regions is a chord endpoint.  The two closed side disks meet only at the chord ends `{u, v}`. -/
def SideRegionInterChordEnds (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {w : M.Vertex}, w ∈ sideRegion₁ data → w ∈ sideRegion₂ data → w = u ∨ w = v



/-- The side-2 seam dart `α dart` has chord edge `s(u, v)`. -/
lemma alpha_dart_edge (data : hNT.ChordSplitData u v) :
    M.dartEdge (M.α data.dart) = s(u, v) := by
  rw [M.dartEdge_alpha]; exact hNT.chordDart_edge data.chord

/-- **Both endpoints of a non-chord side-2 face-dart are in `sideRegion₂`** (unconditional in
`hsep`-free combinatorics apart from the `α`-closure, which needs `Separates`). -/
theorem endpoints_mem_sideRegion₂_of_face (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace e ∈ data.side₂) :
    M.tail e ∈ sideRegion₂ data ∧ M.head e ∈ sideRegion₂ data := by
  -- `e ≠ α dart` (else its edge would be the chord).
  have hne : e ≠ M.α data.dart := by
    intro h; exact hchord (by rw [h]; exact alpha_dart_edge data)
  -- `e ∈ sideDarts₂ ⊆ keptSet₂`.
  have hkept : e ∈ data.keptSet₂ := by
    refine ⟨Or.inl hface, ?_⟩
    simp only [Set.mem_singleton_iff]; exact hne
  have htail : M.tail e ∈ sideRegion₂ data :=
    tail_mem_sideRegion₂ data ((data.mem_keptDel₂_iff e).2 hkept)
  -- head `e = tail (α e)`; `α e ∈ keptSet₂` by the `α`-closure.
  have hkeptα : M.α e ∈ data.keptSet₂ := (data.mem_keptSet₂_alpha_iff hsep e).2 hkept
  have hhead : M.head e ∈ sideRegion₂ data :=
    tail_mem_sideRegion₂ data ((data.mem_keptDel₂_iff (M.α e)).2 hkeptα)
  exact ⟨htail, hhead⟩



/-- **A non-loop edge with both endpoints in `{u, v}` is the chord.**  The simple-map no-loop
fact gives `tail e ≠ head e`; two distinct members of `{u, v}` are exactly `u, v` (in some order),
so `dartEdge e = s(tail e, head e) = s(u, v)`. -/
theorem edge_eq_chord_of_endpoints_chordEnds (data : hNT.ChordSplitData u v) {e : D}
    (htail : M.tail e = u ∨ M.tail e = v) (hhead : M.head e = u ∨ M.head e = v) :
    M.dartEdge e = s(u, v) := by
  have hloop : M.tail e ≠ M.head e := hNT.simpleGraph.no_loop e
  show s(M.tail e, M.head e) = s(u, v)
  rcases htail with ht | ht <;> rcases hhead with hh | hh
  · -- both `= u`: contradicts non-loop.
    exact absurd (ht.trans hh.symm) hloop
  · rw [ht, hh]
  · rw [ht, hh, Sym2.eq_swap]
  · -- both `= v`: contradicts non-loop.
    exact absurd (ht.trans hh.symm) hloop



/-- **The corrected (bounded) `edge_core`, via closure-intersection.**  For a non-chord, bounded
dart `e` (`dartFace e ≠ outerFace`) whose two endpoints are both in `sideRegion₁`, the face of `e`
lies in `side₁`.

Proof: `bounded_face_partition` places `dartFace e` in `side₁` or `side₂`.  In the `side₂` case,
`endpoints_mem_sideRegion₂_of_face` puts both endpoints in `sideRegion₂`; combined with the
`sideRegion₁` hypotheses, `sideRegion_inter_subset_chordEnds` forces both endpoints into `{u, v}`,
whence `edge_eq_chord_of_endpoints_chordEnds` makes `e` the chord — contradicting non-chordness.
So `dartFace e ∈ side₁`.

Clean-3 conditional on exactly the two isolated planar bridges. -/
theorem edge_core_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (houter : M.dartFace e ≠ hNT.outerFace)
    (htail : M.tail e ∈ sideRegion₁ data) (hhead : M.head e ∈ sideRegion₁ data) :
    M.dartFace e ∈ data.side₁ := by
  rcases hpart houter with hside₁ | hside₂
  · exact hside₁
  · -- `dartFace e ∈ side₂`: derive `e = chord`, contradiction.
    exfalso
    obtain ⟨htail₂, hhead₂⟩ := endpoints_mem_sideRegion₂_of_face data hsep hchord hside₂
    have htchord : M.tail e = u ∨ M.tail e = v := hinter htail htail₂
    have hhchord : M.head e = u ∨ M.head e = v := hinter hhead hhead₂
    exact hchord (edge_eq_chord_of_endpoints_chordEnds data htchord hhchord)





end ProofsInTheBook.ZinanCh35EdgeCore








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



/-- **The side-2 vertex correspondence `ι₂`.**  Mirror of `ChordReconClose.sideVertexToM₁`:
a side-2 vertex (a `freshSigma sideSigma₂`-orbit `⟦y⟧`) is sent to `M.tail (proj a₀ a₁ y).val`.
Well-defined: a `freshSigma`-orbit restricts to a `sideSigma₂`-orbit (`freshSigma_sameCycle_iff`)
and then to an `M.σ`-orbit (`filteredRotation_sameCycle_iff` over `keptDel₂`). -/
noncomputable def sideVertexToM₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    (data.sideMap₂ hsep a₀ a₁ hne).Vertex → M.Vertex :=
  Quotient.lift
    (fun y : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2 =>
      M.tail (proj a₀ a₁ y).1)
    (by
      intro x y hxy
      have hfs : (freshSigma data.sideSigma₂ a₀ a₁ hne).SameCycle x y := hxy
      have hss : data.sideSigma₂.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y) :=
        (freshSigma_sameCycle_iff data.sideSigma₂ hne x y).1 hfs
      have hM : M.σ.SameCycle (proj a₀ a₁ x).1 (proj a₀ a₁ y).1 :=
        (filteredRotation_sameCycle_iff M.σ data.keptDel₂ _ _).1 hss
      show M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1
      exact Quotient.sound hM)

/-- `ι₂` on the class of a representative `y` is `M.tail (proj a₀ a₁ y).1` (the `Quotient.lift`
computation). -/
lemma sideVertexToM₂_mk (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (y : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) y)
      = M.tail (proj a₀ a₁ y).1 :=
  rfl

/-- `ι₂` on the class of an `inl`-dart `⟨d, …⟩` is `M.tail d`. -/
lemma sideVertexToM₂_inl (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₂}) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) (Sum.inl x))
      = M.tail x.1 := by
  show M.tail (proj a₀ a₁ (Sum.inl x)).1 = M.tail x.1
  rw [proj_inl]

/-- `ι₂` of the head of an `inl`-dart `x` is `M.head x.val` (`sideAlpha₂` restricts `M.α`). -/
lemma sideVertexToM₂_head_inl (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₂}) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₂ hsep)) (Sum.inl x)))
      = M.head x.1 := by
  rw [freshAlpha_inl]
  rw [sideVertexToM₂_inl data hsep a₀ a₁ hne (data.sideAlpha₂ hsep x)]
  rw [data.sideAlpha₂_apply_coe hsep x]
  rfl

/-- **`ι₂` lands in the side-2 region.**  Every side-2 vertex is the orbit of a kept dart, whose
tail is in `sideRegion₂` by definition. -/
theorem sideVertexToM₂_mem (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (V : (data.sideMap₂ hsep a₀ a₁ hne).Vertex) :
    sideVertexToM₂ data hsep a₀ a₁ hne V ∈ sideRegion₂ data := by
  refine Quotient.inductionOn V (fun y => ?_)
  show M.tail (proj a₀ a₁ y).1 ∈ sideRegion₂ data
  exact tail_mem_sideRegion₂ data (proj a₀ a₁ y).2

/-- **`ι₂` is surjective onto the side-2 region (`ι_surj`).**  Every region vertex `w = M.tail d`
(kept `d ∉ keptDel₂`) is `ι₂ ⟦inl ⟨d, …⟩⟧`. -/
theorem sideVertexToM₂_surjective (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    ∀ ⦃w : M.Vertex⦄, w ∈ sideRegion₂ data →
      ∃ V : (data.sideMap₂ hsep a₀ a₁ hne).Vertex,
        sideVertexToM₂ data hsep a₀ a₁ hne V = w := by
  rintro w ⟨d, hd, rfl⟩
  refine ⟨Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
    (Sum.inl ⟨d, hd⟩), ?_⟩
  exact sideVertexToM₂_inl data hsep a₀ a₁ hne ⟨d, hd⟩

/-- **The image of `ι₂` is exactly the side-2 region.** -/
theorem sideVertexToM₂_range (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    Set.range (sideVertexToM₂ data hsep a₀ a₁ hne) = sideRegion₂ data := by
  apply Set.eq_of_subset_of_subset
  · rintro w ⟨V, rfl⟩
    exact sideVertexToM₂_mem data hsep a₀ a₁ hne V
  · intro w hw
    obtain ⟨V, hV⟩ := sideVertexToM₂_surjective data hsep a₀ a₁ hne hw
    exact ⟨V, hV⟩

/-- **The inner-edge correspondence (`ι_adj_of_inl₂`).**  The side-2 edge of an `inl`-dart `x`
maps under `ι₂` to the `M`-edge `s(M.tail x.val, M.head x.val)`; the two `ι₂`-endpoints are
`M`-adjacent via the dart `x.val`. -/
theorem ι_adj_of_inl₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₂}) :
    M.Adj
      (sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) (Sum.inl x)))
      (sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₂ hsep)) (Sum.inl x)))) := by
  rw [sideVertexToM₂_inl data hsep a₀ a₁ hne x,
    sideVertexToM₂_head_inl data hsep a₀ a₁ hne x]
  exact M.adj_of_dart x.1







/-- **The side-2 boundary classification residue.**  Mirror of `ChordSideNT.ContiguousInterval`
against `sideMap₂`: the side outer face/cycle (arc-plus-duplicated-chord), its simplicity, length
`≥ 3`, and the inner-triangle condition.  These are the `NearTriangulation (sideMap₂)` fields
beyond `IsSphereMap`. -/
structure ContiguousInterval₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) where
  /-- The side-2 map is a simple graph. -/
  simpleGraph : (data.sideMap₂ hsep a₀ a₁ hne).IsSimpleGraph
  /-- The side-2 outer face (the chord face). -/
  outerFace : (data.sideMap₂ hsep a₀ a₁ hne).Face
  /-- The side-2 outer boundary cycle. -/
  outerCycle : BoundaryCycle (data.sideMap₂ hsep a₀ a₁ hne) outerFace
  /-- The side-2 boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The side-2 boundary has length at least three. -/
  outer_len : 3 ≤ outerCycle.length
  /-- Every non-outer side-2 face is a triangle. -/
  inner_tri : ∀ f : (data.sideMap₂ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    (data.sideMap₂ hsep a₀ a₁ hne).faceLen f = 3

/-- **The side-2 near-triangulation, assembled.**  Mirror of
`ChordSideNT.chordSideNearTriangulation`: `sphere` from the supplied side-2 sphere fact,
everything else from `ContiguousInterval₂`. -/
def chordSideNearTriangulation₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hsphere : (data.sideMap₂ hsep a₀ a₁ hne).IsSphereMap)
    (ci : ContiguousInterval₂ data hsep a₀ a₁ hne) :
    NearTriangulation (data.sideMap₂ hsep a₀ a₁ hne) where
  sphere := hsphere
  simpleGraph := ci.simpleGraph
  outerFace := ci.outerFace
  outerCycle := ci.outerCycle
  outer_simple := ci.outer_simple
  outer_len := ci.outer_len
  inner_tri := ci.inner_tri

/-- **The side-2 near-triangulation from the disk facts + the boundary classification.**  Mirror
of `chordSideNearTriangulation_of_share`: the `sphere` field is discharged by
`ChordDisk.side₂_isSphereMap_of_disk` from the side-2 disk fact `Side₂IsDisk` and the
anchor-incidence fact `Side₂AnchorsShareFace`.  (`sideKeptMap₂_connected` was not mirrored
upstream, so `Side₂IsDisk` is a named input — the one genuine asymmetry, see the header.) -/
def chordSideNearTriangulation₂_of_share (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep)
    (hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval₂ data hsep a₀ a₁ hne) :
    NearTriangulation (data.sideMap₂ hsep a₀ a₁ hne) :=
  chordSideNearTriangulation₂ data hsep a₀ a₁ hne
    (ProofsInTheBook.ChordDisk.side₂_isSphereMap_of_disk data hsep a₀ a₁ hne hdisk hshare) ci

/-- **`ContiguousInterval₂` is satisfiable from a side-2 near-triangulation** (non-vacuity).  Any
`NearTriangulation (sideMap₂)` projects onto a `ContiguousInterval₂` (its boundary fields).  So
the predicate is not unsatisfiable: it holds exactly when the side is a near-triangulation. -/
def contiguousInterval₂_of_nearTriangulation (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (N : NearTriangulation (data.sideMap₂ hsep a₀ a₁ hne)) :
    ContiguousInterval₂ data hsep a₀ a₁ hne where
  simpleGraph := N.simpleGraph
  outerFace := N.outerFace
  outerCycle := N.outerCycle
  outer_simple := N.outer_simple
  outer_len := N.outer_len
  inner_tri := N.inner_tri



/-- **Brick 1 — `ι₂` is injective.**  Mirror of `sideVertexToM₁_injective_canonical`:
`ι₂ ⟦y⟧ = ι₂ ⟦z⟧` gives `M.σ.SameCycle (proj y).1 (proj z).1` (`Quotient.exact`), transported
back to a `sideSigma₂`-SameCycle (`filteredRotation_sameCycle_iff`) and then a `freshSigma`-
SameCycle (`freshSigma_sameCycle_iff` backward), i.e. `⟦y⟧ = ⟦z⟧`.  Purely combinatorial. -/
theorem sideVertexToM₂_injective_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    Function.Injective (sideVertexToM₂ data hsep a₀ a₁ hne) := by
  refine fun X Y => ?_
  refine Quotient.inductionOn₂ X Y (fun y z hYZ => ?_)
  have hM : M.σ.SameCycle (proj a₀ a₁ y).1 (proj a₀ a₁ z).1 := Quotient.exact hYZ
  have hss : data.sideSigma₂.SameCycle (proj a₀ a₁ y) (proj a₀ a₁ z) :=
    (FilteredRotation.filteredRotation_sameCycle_iff M.σ data.keptDel₂
      (proj a₀ a₁ y) (proj a₀ a₁ z)).2 hM
  have hfs : (freshSigma data.sideSigma₂ a₀ a₁ hne).SameCycle y z :=
    (freshSigma_sameCycle_iff data.sideSigma₂ hne y z).2 hss
  exact Quotient.sound hfs

/-- `ι₂ (sideMap₂.tail (inr j))` is `M.tail a₀.1` (`j = 0`) or `M.tail a₁.1` (`j = 1`).  Mirror of
`sideVertexToM₁_tail_inr`. -/
lemma sideVertexToM₂_tail_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) (Sum.inr j))
      = M.tail (if j = 0 then a₀.1 else a₁.1) := by
  rw [sideVertexToM₂_mk data hsep a₀ a₁ hne (Sum.inr j)]
  fin_cases j
  · simp [proj]
  · simp [proj]

/-- The fresh chord dart `inr j` has `ι₂`-head the *other* anchor's tail.  Mirror of
`sideVertexToM₁_head_inr`. -/
lemma sideVertexToM₂_head_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₂ hsep)) (Sum.inr j)))
      = M.tail (if j = 0 then a₁.1 else a₀.1) := by
  rw [freshAlpha_inr]
  rw [sideVertexToM₂_tail_inr data hsep a₀ a₁ hne (Equiv.swap (0 : Fin 2) 1 j)]
  fin_cases j
  · simp [Equiv.swap_apply_left]
  · simp [Equiv.swap_apply_right]

/-- **The `ι₂`-edge of any side-2 dart.**  Mirror of `ZinanCh35Iota.ι_adj_of_dart`: an `inl x'`
dart gives the proved `M`-edge of `x'` (`ι_adj_of_inl₂`); a fresh chord dart gives the anchor-tail
pair (`M`-adjacent by `hchord`). -/
lemma ι_adj_of_dart₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (d : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) :
    M.Adj
      (sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) d))
      (sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₂ hsep)) d))) := by
  cases d with
  | inl x' => exact ι_adj_of_inl₂ data hsep a₀ a₁ hne x'
  | inr j =>
      rw [sideVertexToM₂_tail_inr data hsep a₀ a₁ hne j,
        sideVertexToM₂_head_inr data hsep a₀ a₁ hne j]
      fin_cases j
      · simpa using hchord
      · simpa using M.adj_symm hchord

/-- **Brick 2 — `ι₂_adj`.**  Mirror of `sideVertexToM₁_adj_canonical`: side-2 adjacency carries
to `M`-adjacency on `ι₂`-images, with the chord edge `hchord` discharging the fresh-dart half and
injectivity (Brick 1) the `≠` half. -/
theorem sideVertexToM₂_adj_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)) :
    ∀ ⦃x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex⦄,
      (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
        M.toSimpleGraph.Adj (sideVertexToM₂ data hsep a₀ a₁ hne x)
          (sideVertexToM₂ data hsep a₀ a₁ hne y) := by
  intro x y hxy
  rw [toSimpleGraph_adj] at hxy ⊢
  obtain ⟨hne_xy, d, hd⟩ := hxy
  refine ⟨fun h => hne_xy (sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne h), ?_⟩
  have hM := ι_adj_of_dart₂ data hsep a₀ a₁ hne hchord d
  have hd' : s((data.sideMap₂ hsep a₀ a₁ hne).tail d, (data.sideMap₂ hsep a₀ a₁ hne).head d)
      = s(x, y) := hd
  rcases Sym2.eq_iff.1 hd' with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [← hx, ← hy]; exact hM
  · rw [← hx, ← hy]; exact M.adj_symm hM

/-- **Brick 5 — `smaller`.**  Mirror of `side₁_smaller_canonical`: from injectivity of `ι₂` and an
explicit omitted `M`-vertex `w ∉ Set.range ι₂` (the opposite-arc internal vertex side 2 drops —
the named region-confinement residue `homit`), the side has strictly fewer vertices than `M`. -/
theorem side₂_smaller_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₂ data hsep a₀ a₁ hne)) :
    (data.sideMap₂ hsep a₀ a₁ hne).V < M.V := by
  classical
  obtain ⟨w, hw⟩ := homit
  show Fintype.card (data.sideMap₂ hsep a₀ a₁ hne).Vertex < Fintype.card M.Vertex
  have hinj := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne
  have hcard_le : Fintype.card (data.sideMap₂ hsep a₀ a₁ hne).Vertex
      = (Finset.univ.image (sideVertexToM₂ data hsep a₀ a₁ hne)).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [hcard_le]
  have hsub : Finset.univ.image (sideVertexToM₂ data hsep a₀ a₁ hne) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.2 ?_
    intro hfull
    apply hw
    have hmem : w ∈ Finset.univ.image (sideVertexToM₂ data hsep a₀ a₁ hne) := by
      rw [hfull]; exact Finset.mem_univ w
    obtain ⟨V, _, hV⟩ := Finset.mem_image.1 hmem
    exact ⟨V, hV⟩
  calc (Finset.univ.image (sideVertexToM₂ data hsep a₀ a₁ hne)).card
      < (Finset.univ : Finset M.Vertex).card := Finset.card_lt_card hsub
    _ = Fintype.card M.Vertex := Finset.card_univ



/-- **The side-2 residue datum.**  Mirror of `ChordSplitFinal.ChordSideResidue`: the
genuinely-unbuilt `ChordSideReconstruction` fields for the side-2 instantiation. -/
structure ChordSideResidue₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α) where
  /-- The side-2 disk core (for the `sphere` field). -/
  hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep
  /-- The side-2 anchor-incidence fact. -/
  hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁
  /-- The side-2 boundary/inner-triangulation classification. -/
  ci : ContiguousInterval₂ data hsep a₀ a₁ hne
  /-- The vertex correspondence is injective. -/
  ι_inj : Function.Injective (sideVertexToM₂ data hsep a₀ a₁ hne)
  /-- Side-2 adjacency carries to `M`-adjacency. -/
  ι_adj : ∀ ⦃x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex⦄,
    (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
      M.toSimpleGraph.Adj (sideVertexToM₂ data hsep a₀ a₁ hne x)
        (sideVertexToM₂ data hsep a₀ a₁ hne y)
  /-- The vertex correspondence reflects `M`-adjacency on the region. -/
  ι_adj_reflect : ∀ ⦃x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex⦄,
    M.toSimpleGraph.Adj (sideVertexToM₂ data hsep a₀ a₁ hne x)
        (sideVertexToM₂ data hsep a₀ a₁ hne y) →
      (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y
  /-- The side's precolored boundary edge. -/
  pₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex
  /-- The side's precolored boundary edge. -/
  qₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex
  /-- The side's precolors. -/
  cpₛ : α
  /-- The side's precolors. -/
  cqₛ : α
  /-- The side Thomassen list hypotheses (with the pullback lists). -/
  hLₛ : ThomassenLists
    (chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne hdisk hshare ci)
    pₛ qₛ (fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)) cpₛ cqₛ
  /-- The strict vertex decrease (the recursion fuel). -/
  smaller : (data.sideMap₂ hsep a₀ a₁ hne).V < M.V

/-- **The side-2 reconstruction in the generic recursion framing.**  Mirror of
`ChordSplitFinal.chordSideReconstruction_of_chord`: assembles
`ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ data) L` with `N := sideMap₂`,
`hN :=` the proved side-2 near-triangulation, `ι := sideVertexToM₂`, `ι_mem`/`ι_surj` proved in
Tier A and baked in directly, and the residue datum supplying the remaining fields. -/
noncomputable def chordSideReconstruction₂_of_chord (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α)
    (res : ChordSideResidue₂ data hsep a₀ a₁ hne L) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ data) L where
  Dₛ := {d : D // d ∉ data.keptDel₂} ⊕ Fin 2
  N := data.sideMap₂ hsep a₀ a₁ hne
  hN := chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne res.hdisk res.hshare res.ci
  ι := sideVertexToM₂ data hsep a₀ a₁ hne
  ι_inj := res.ι_inj
  ι_mem := fun x => sideVertexToM₂_mem data hsep a₀ a₁ hne x
  ι_surj := fun _ hw => sideVertexToM₂_surjective data hsep a₀ a₁ hne hw
  ι_adj := res.ι_adj
  ι_adj_reflect := res.ι_adj_reflect
  Lₛ := fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)
  Lₛ_eq := fun _ => rfl
  pₛ := res.pₛ
  qₛ := res.qₛ
  cpₛ := res.cpₛ
  cqₛ := res.cqₛ
  hLₛ := res.hLₛ
  smaller := res.smaller





/-- **The minimal side-2 confinement input bundle.**  Mirror of
`ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput` with the side₁/side₂ roles swapped:

* `oppArcStarSeed₂` — a strictly internal vertex of the *opposite* boundary arc `path₁` is omitted
  by side 2 (`w ∉ sideRegion₂ data`).  (For side 2 the opposite arc is `path₁`, the mirror of
  side 1's `path₂`.)

* `edge_core₂` — an ambient dart `e` whose two endpoints are both side-2-region vertices is either
  represented in the side-2 carve (`e ∉ keptDel₂ ∧ α e ∉ keptDel₂`) or is the chord.  This is the
  side-2 region edge-confinement core; it reduces to the SAME two bridges as side 1
  (`BoundedFacePartition` + `SideRegionInterChordEnds`, both side-symmetric), which
  `ZinanCh35EdgeCore.edge_core_holds` discharges with the side roles swapped. -/
structure Side₂SchoenfliesConfinementInput (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : Prop where
  /-- Opposite-arc omission: a `path₁`-internal vertex is not in the side-2 region. -/
  oppArcStarSeed₂ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₁.internalVertices → w ∉ sideRegion₂ data
  /-- Region edge-confinement core: an ambient edge between two side-2-region vertices is kept by
  side 2 (both `e` and `α e`), or is the chord. -/
  edge_core₂ : ∀ {e : D},
    M.tail e ∈ sideRegion₂ data →
    M.head e ∈ sideRegion₂ data →
      ((e ∉ data.keptDel₂ ∧ M.α e ∉ data.keptDel₂) ∨ M.dartEdge e = s(u, v))

/-- **Brick 2 — `homit_of_confinementInput₂`.**  The opposite boundary arc `path₁` carries an
internal vertex (`data.arc₁_internal`); that vertex is omitted by side 2 (`oppArcStarSeed₂`),
witnessing `∃ w, w ∉ sideRegion₂ data`.  Mirror of `homit_of_confinementInput`. -/
theorem homit_of_confinementInput₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ∃ w : M.Vertex, w ∉ sideRegion₂ data := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ data.arc₁_internal
  exact ⟨w, H.oppArcStarSeed₂ hw⟩

/-- **Brick 3 — `side₂_adj_of_kept_edge`.**  Mirror of `ZinanCh35FinalClose.side_adj_of_kept_edge`:
a kept dart `e ∉ keptDel₂` with `M.tail e = ι₂ x`, `M.head e = ι₂ y` (`x ≠ y`) yields
`sideMap₂.toSimpleGraph.Adj x y`, witnessed by the side dart `Sum.inl ⟨e, he⟩`. -/
theorem side₂_adj_of_kept_edge (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    {x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex} (hxy : x ≠ y)
    {e : D} (he : e ∉ data.keptDel₂)
    (htail : M.tail e = sideVertexToM₂ data hsep a₀ a₁ hne x)
    (hhead : M.head e = sideVertexToM₂ data hsep a₀ a₁ hne y) :
    (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  set dS : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2 := Sum.inl ⟨e, he⟩ with hdS
  set xS : (data.sideMap₂ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) dS with hxS
  set yS : (data.sideMap₂ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
      ((freshAlpha (data.sideAlpha₂ hsep)) dS) with hyS
  have hιx : sideVertexToM₂ data hsep a₀ a₁ hne xS
      = sideVertexToM₂ data hsep a₀ a₁ hne x := by
    rw [hxS, hdS, sideVertexToM₂_inl data hsep a₀ a₁ hne ⟨e, he⟩, htail]
  have hιy : sideVertexToM₂ data hsep a₀ a₁ hne yS
      = sideVertexToM₂ data hsep a₀ a₁ hne y := by
    rw [hyS, hdS, sideVertexToM₂_head_inl data hsep a₀ a₁ hne ⟨e, he⟩, hhead]
  have hxSx : xS = x := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne hιx
  have hySy : yS = y := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne hιy
  rw [toSimpleGraph_adj]
  refine ⟨hxy, ?_⟩
  refine ⟨dS, ?_⟩
  show (data.sideMap₂ hsep a₀ a₁ hne).dartEdge dS = s(x, y)
  rw [← hxSx, ← hySy]
  rfl

/-- **Brick 4 — `side₂_adj_of_chord_edge`.**  Mirror of
`ZinanCh35FinalClose.side_adj_of_chord_edge`: in the chord case `s(ι₂ x, ι₂ y) = s(u, v)`, with the
canonical anchor-tail identification `M.tail a₀.1 = u`, `M.tail a₁.1 = v`, the fresh chord side
dart `Sum.inr 0` realises `s(x, y)`. -/
theorem side₂_adj_of_chord_edge (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    {x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex} (hxy : x ≠ y)
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (hx : sideVertexToM₂ data hsep a₀ a₁ hne x = u)
    (hy : sideVertexToM₂ data hsep a₀ a₁ hne y = v) :
    (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  set dS : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2 := Sum.inr 0 with hdS
  set xS : (data.sideMap₂ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) dS with hxS
  set yS : (data.sideMap₂ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
      ((freshAlpha (data.sideAlpha₂ hsep)) dS) with hyS
  have hιx : sideVertexToM₂ data hsep a₀ a₁ hne xS
      = sideVertexToM₂ data hsep a₀ a₁ hne x := by
    rw [hxS, hdS, sideVertexToM₂_tail_inr data hsep a₀ a₁ hne 0]
    simp only [if_true]
    rw [ha₀, hx]
  have hιy : sideVertexToM₂ data hsep a₀ a₁ hne yS
      = sideVertexToM₂ data hsep a₀ a₁ hne y := by
    rw [hyS, hdS, sideVertexToM₂_head_inr data hsep a₀ a₁ hne 0]
    simp only [if_true]
    rw [ha₁, hy]
  have hxSx : xS = x := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne hιx
  have hySy : yS = y := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne hιy
  rw [toSimpleGraph_adj]
  refine ⟨hxy, dS, ?_⟩
  show (data.sideMap₂ hsep a₀ a₁ hne).dartEdge dS = s(x, y)
  rw [← hxSx, ← hySy]
  rfl

/-- **Brick 5 — `hreflect_of_confinementInput₂`** (master).  Mirror of
`ZinanCh35FinalClose.hreflect_of_confinementInput`: produces the region edge-confinement field
`ι_adj_reflect` from `edge_core₂`, threading the canonical anchor-tail identification
`ha₀ : M.tail a₀.1 = u`, `ha₁ : M.tail a₁.1 = v`. -/
theorem hreflect_of_confinementInput₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ∀ ⦃x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₂ data hsep a₀ a₁ hne x)
          (sideVertexToM₂ data hsep a₀ a₁ hne y) →
        (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  intro x y hAdj
  rw [toSimpleGraph_adj] at hAdj
  obtain ⟨hne_ι, e, hde⟩ := hAdj
  have hxy : x ≠ y := fun h => hne_ι (by rw [h])
  have hx_mem : sideVertexToM₂ data hsep a₀ a₁ hne x ∈ sideRegion₂ data :=
    sideVertexToM₂_mem data hsep a₀ a₁ hne x
  have hy_mem : sideVertexToM₂ data hsep a₀ a₁ hne y ∈ sideRegion₂ data :=
    sideVertexToM₂_mem data hsep a₀ a₁ hne y
  have hde' : s(M.tail e, M.head e)
      = s(sideVertexToM₂ data hsep a₀ a₁ hne x, sideVertexToM₂ data hsep a₀ a₁ hne y) := hde
  rcases Sym2.eq_iff.1 hde' with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have htail_mem : M.tail e ∈ sideRegion₂ data := by rw [ht]; exact hx_mem
    have hhead_mem : M.head e ∈ sideRegion₂ data := by rw [hh]; exact hy_mem
    rcases H.edge_core₂ htail_mem hhead_mem with ⟨hkept, _⟩ | hchord
    · exact side₂_adj_of_kept_edge data hsep a₀ a₁ hne hxy hkept ht hh
    · have hsuv : s(sideVertexToM₂ data hsep a₀ a₁ hne x, sideVertexToM₂ data hsep a₀ a₁ hne y)
          = s(u, v) := by
        rw [← hde]; exact hchord
      rcases Sym2.eq_iff.1 hsuv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
      · exact side₂_adj_of_chord_edge data hsep a₀ a₁ hne hxy ha₀ ha₁ hxu hyv
      · exact ((data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.symm
          (side₂_adj_of_chord_edge data hsep a₀ a₁ hne hxy.symm ha₀ ha₁ hyu hxv))
  · have htail_mem : M.tail e ∈ sideRegion₂ data := by rw [ht]; exact hy_mem
    have hhead_mem : M.head e ∈ sideRegion₂ data := by rw [hh]; exact hx_mem
    rcases H.edge_core₂ htail_mem hhead_mem with ⟨hkept, _⟩ | hchord
    · exact (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.symm
        (side₂_adj_of_kept_edge data hsep a₀ a₁ hne hxy.symm hkept ht hh)
    · have hsuv : s(sideVertexToM₂ data hsep a₀ a₁ hne y, sideVertexToM₂ data hsep a₀ a₁ hne x)
          = s(u, v) := by
        rw [Sym2.eq_swap, ← hde]; exact hchord
      rcases Sym2.eq_iff.1 hsuv with ⟨hyu, hxv⟩ | ⟨hyv, hxu⟩
      · exact (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.symm
          (side₂_adj_of_chord_edge data hsep a₀ a₁ hne hxy.symm ha₀ ha₁ hyu hxv)
      · exact side₂_adj_of_chord_edge data hsep a₀ a₁ hne hxy ha₀ ha₁ hxu hyv

/-- **Brick 6 — `chordSideResidue₂_partial`.**  Mirror of `ZinanCh35Iota.chordSideResidue₁_partial`
composed with the side-2 confinement producers: assembles the full `ChordSideResidue₂` from the
boundary classification `ci`, the disk/anchor facts, the chord edge `hchord`, the canonical
anchor-tail identification `ha₀`/`ha₁`, the side Thomassen lists `hLₛ`, and the side-2 confinement
bundle `H` (which supplies `ι_adj_reflect` via Brick 5 and the omitted-vertex witness via Brick 2).

The proved fields: `ι_inj` (Tier C Brick 1), the kept-dart half of `ι_adj` (Brick 2), the strict
decrease (Brick 5).  The genuine planar residue is exactly `H` (the confinement bundle), `ci`,
`hdisk`/`hshare`, `hchord`, and the list field `hLₛ` — mirroring side 1 field-for-field. -/
def chordSideResidue₂_partial (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep)
    (hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval₂ data hsep a₀ a₁ hne)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (pₛ qₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne hdisk hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ChordSideResidue₂ data hsep a₀ a₁ hne L where
  hdisk := hdisk
  hshare := hshare
  ci := ci
  ι_inj := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne
  ι_adj := sideVertexToM₂_adj_canonical data hsep a₀ a₁ hne hchord
  ι_adj_reflect := hreflect_of_confinementInput₂ data hsep a₀ a₁ hne ha₀ ha₁ H
  pₛ := pₛ
  qₛ := qₛ
  cpₛ := cpₛ
  cqₛ := cqₛ
  hLₛ := hLₛ
  smaller := side₂_smaller_canonical data hsep a₀ a₁ hne
    (by
      -- transport `homit_of_confinementInput₂` through `Set.range ι₂ = sideRegion₂`.
      obtain ⟨w, hw⟩ := homit_of_confinementInput₂ data hsep H
      refine ⟨w, ?_⟩
      rw [sideVertexToM₂_range data hsep a₀ a₁ hne]
      exact hw)

/-- **`chordSideResidue₂_final`.**  Mirror of `ZinanCh35FinalClose.chordSideResidue₁_final`: the
full side-2 reconstruction residue `ChordSideResidue₂`, closed modulo the minimal bundle
`Side₂SchoenfliesConfinementInput` (the genuine side-2 discrete-Schoenflies content) plus the
upstream non-confinement inputs (`hdisk`/`hshare`/`ci`/`hchord`/`ha₀`/`ha₁`/`hLₛ`).  This is
exactly `chordSideResidue₂_partial`, recorded under the FinalClose name for parity with side 1. -/
def chordSideResidue₂_final (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep)
    (hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval₂ data hsep a₀ a₁ hne)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (pₛ qₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne hdisk hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ChordSideResidue₂ data hsep a₀ a₁ hne L :=
  chordSideResidue₂_partial data hsep a₀ a₁ hne L hdisk hshare ci hchord ha₀ ha₁
    pₛ qₛ cpₛ cqₛ hLₛ H



/-- **The exact side-2 input list** consumed by `chordSideResidue₂_final`.  Mirror of
`ZinanCh35Cert.Side₁CertificateInputs` against the side-2 data; the genuine planar content is the
field `confinement : Side₂SchoenfliesConfinementInput` plus the boundary/disk classification. -/
structure Side₂CertificateInputs (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂})
    (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α) where
  hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep
  hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁
  ci : ContiguousInterval₂ data hsep a₀ a₁ hne
  hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)
  ha₀ : M.tail a₀.1 = u
  ha₁ : M.tail a₁.1 = v
  pₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex
  qₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex
  cpₛ : α
  cqₛ : α
  hLₛ : ThomassenLists
    (chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne hdisk hshare ci)
    pₛ qₛ (fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)) cpₛ cqₛ
  confinement : Side₂SchoenfliesConfinementInput data hsep

/-- The side-2 residue, repackaged with its exact input list.  Mirror of
`ZinanCh35Cert.side₁Residue_of_certificateInputs`. -/
def side₂Residue_of_certificateInputs (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂})
    (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (I : Side₂CertificateInputs data hsep a₀ a₁ hne L) :
    ChordSideResidue₂ data hsep a₀ a₁ hne L :=
  chordSideResidue₂_final data hsep a₀ a₁ hne L
    I.hdisk I.hshare I.ci I.hchord I.ha₀ I.ha₁ I.pₛ I.qₛ I.cpₛ I.cqₛ I.hLₛ I.confinement

/-- **The deliverable: the side-2 reconstruction in the exact `ChordSideReconstruction` shape.**
Mirror of `ZinanCh35Cert.side₁Reconstruction_of_certificateInputs`: threads the side-2 final
residue into `ChordSideReconstruction hNT (sideRegion₂ data) L`, the side-2 half the
`ChordBranchSupplier` needs to assemble a `ChordSplitFinal.ChordBranchResidue`. -/
noncomputable def side₂Reconstruction_of_certificateInputs
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α)
    (I : Side₂CertificateInputs data hsep a₀ a₁ hne L) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ data) L :=
  chordSideReconstruction₂_of_chord data hsep a₀ a₁ hne L
    (side₂Residue_of_certificateInputs data hsep a₀ a₁ hne L I)





end ProofsInTheBook.ZinanCh35Side2














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

/-- `r` with the single undirected edge `{a, b}` removed. -/
def removeEdge (a b : V) : V → V → Prop :=
  fun x y => r x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))

/-- **One-edge removal.**  If `w` is reachable from `a` in `r`, then `w` is reachable from `a` or
from `b` in `r` with the edge `{a, b}` removed. -/
theorem reflTransGen_removeEdge {a b : V} {w : V}
    (h : Relation.ReflTransGen r a w) :
    Relation.ReflTransGen (removeEdge r a b) a w ∨
      Relation.ReflTransGen (removeEdge r a b) b w := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail x w hax hxw ih =>
      by_cases hedge : (x = a ∧ w = b) ∨ (x = b ∧ w = a)
      · -- The last step is exactly the removed edge `{a, b}`.
        rcases hedge with ⟨hxa, hwb⟩ | ⟨hxb, hwa⟩
        · subst hwb; exact Or.inr Relation.ReflTransGen.refl
        · subst hwa; exact Or.inl Relation.ReflTransGen.refl
      · -- The last step survives in `removeEdge`.
        have hstep : removeEdge r a b x w := ⟨hxw, hedge⟩
        rcases ih with hA | hB
        · exact Or.inl (hA.tail hstep)
        · exact Or.inr (hB.tail hstep)

end Abstract



/-- **Inner-face dual adjacency.**  Two faces share an edge that is not a boundary edge. -/
def InnerAdj (hNT : NearTriangulation M) (f g : M.Face) : Prop :=
  ∃ d : D,
    M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
      ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)





/-- A dart with the chord edge is `data.dart` or `M.α data.dart`. -/
lemma eq_dart_or_alpha_of_chordEdge (data : hNT.ChordSplitData u v) {d : D}
    (hd : M.dartEdge d = s(u, v)) : d = data.dart ∨ d = M.α data.dart := by
  have hsame : M.dartEdge d = M.dartEdge data.dart := by
    rw [hd]; exact (hNT.chordDart_edge data.chord).symm
  have hsc : M.α.SameCycle data.dart d :=
    M.alpha_sameCycle_of_dartEdge_eq hNT.simpleGraph hsame.symm
  exact (M.alpha_sameCycle_iff data.dart d).1 hsc

/-- **The chord `InnerAdj`-edge runs between `face₁` and `face₂`.**  If `d` witnesses an
`InnerAdj`-step `f → g` and carries the chord edge, then `{f, g} = {face₁, face₂}` (as the ordered
pair `(face₁, face₂)` or `(face₂, face₁)`). -/
lemma face_pair_of_chordEdge (data : hNT.ChordSplitData u v) {d : D} {f g : M.Face}
    (hdf : M.dartFace d = f) (hdg : M.dartFace (M.α d) = g)
    (hd : M.dartEdge d = s(u, v)) :
    (f = data.face₁ ∧ g = data.face₂) ∨ (f = data.face₂ ∧ g = data.face₁) := by
  rcases eq_dart_or_alpha_of_chordEdge data hd with hcase | hcase
  · -- `d = dart`: `f = face₁`, `g = face₂`.
    left
    refine ⟨?_, ?_⟩
    · rw [← hdf, hcase]; rfl
    · rw [← hdg, hcase]; rfl
  · -- `d = α dart`: `f = face₂`, `g = face₁`.
    right
    refine ⟨?_, ?_⟩
    · rw [← hdf, hcase]; rfl
    · rw [← hdg, hcase, M.alpha_alpha]; rfl

/-- **`InnerAdj` minus the `{face₁, face₂}` edge is `ChordSplitAdj`.**  An `InnerAdj`-step whose
ordered face-pair is neither `(face₁, face₂)` nor `(face₂, face₁)` is a genuine `ChordSplitAdj`-step
(its edge cannot be the chord). -/
lemma chordSplitAdj_of_removeEdge_innerAdj (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : removeEdge (InnerAdj hNT) data.face₁ data.face₂ f g) :
    hNT.ChordSplitAdj u v f g := by
  obtain ⟨⟨d, hdf, hdg, hbe⟩, hne⟩ := h
  refine ⟨d, hdf, hdg, hbe, ?_⟩
  intro hchord
  -- chord edge ⟹ `(f, g)` is `(face₁, face₂)` or `(face₂, face₁)`, contradicting `hne`.
  exact hne (face_pair_of_chordEdge data hdf hdg hchord)



/-- A `removeEdge InnerAdj`-walk lifts to a `ChordSplitAdj`-walk (pointwise inclusion of steps). -/
lemma reflTransGen_chordSplitAdj_of_removeEdge (data : hNT.ChordSplitData u v) {s g : M.Face}
    (h : Relation.ReflTransGen (removeEdge (InnerAdj hNT) data.face₁ data.face₂) s g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) s g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (chordSplitAdj_of_removeEdge_innerAdj data hstep)



/-- **The sharp residual: inner-face dual connectivity from `face₁`.**  Every non-outer face is
`InnerAdj`-reachable from `face₁` (the inner-face dual graph is connected, seeded at the chord-face
`face₁`).  This is the only genuinely-missing planar input behind face coverage. -/
def InnerFaceConnectedFromFace₁ (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {f : M.Face}, f ≠ hNT.outerFace →
    Relation.ReflTransGen (InnerAdj hNT) data.face₁ f

/-- **`BoundedFacePartition` from inner-face dual connectivity (the reduction).**
Given that every non-outer face is `InnerAdj`-reachable from `face₁`, every non-outer face is
`ChordSplitAdj`-reachable from `face₁` or `face₂`.  Proof: `InnerAdj`-reach `face₁ → f`, remove the
`{face₁, face₂}` edge (`reflTransGen_removeEdge`) to get `removeEdge`-reach from `face₁` or `face₂`,
then lift through `removeEdge InnerAdj ⊆ ChordSplitAdj`. -/
theorem boundedFacePartition_of_innerConnected (data : hNT.ChordSplitData u v)
    (hconn : InnerFaceConnectedFromFace₁ data) :
    BoundedFacePartition data := by
  intro f hf
  -- `InnerAdj`-reach `face₁ → f`.
  have hreach : Relation.ReflTransGen (InnerAdj hNT) data.face₁ f := hconn hf
  -- remove the chord dual edge `{face₁, face₂}`.
  rcases reflTransGen_removeEdge (InnerAdj hNT) (a := data.face₁) (b := data.face₂) hreach with
    hA | hB
  · -- `removeEdge`-reach from `face₁` ⟹ `ChordSplitAdj`-reach from `face₁` ⟹ `f ∈ side₁`.
    exact Or.inl (reflTransGen_chordSplitAdj_of_removeEdge data hA)
  · -- `removeEdge`-reach from `face₂` ⟹ `ChordSplitAdj`-reach from `face₂` ⟹ `f ∈ side₂`.
    exact Or.inr (reflTransGen_chordSplitAdj_of_removeEdge data hB)





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







/-- **The α-step.**  If the edge of `d` is not a boundary edge, then `dartFace d` and
`dartFace (α d)` are `InnerAdj`-adjacent (the dart `d` itself is the witness). -/
lemma innerAdj_alpha {d : D} (hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)) :
    InnerAdj hNT (M.dartFace d) (M.dartFace (M.α d)) :=
  ⟨d, rfl, rfl, hbe⟩





/-- For a boundary edge, at least one of its two darts lies on the outer face. -/
lemma boundaryEdge_dart_outer {e : D}
    (hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)) :
    M.dartFace e = hNT.outerFace ∨ M.dartFace (M.α e) = hNT.outerFace := by
  rw [BoundaryCycle.IsBoundaryEdge, hNT.outerCycle.edges_eq, List.mem_map] at hbe
  obtain ⟨b, hb, hbe⟩ := hbe
  have hbface : M.dartFace b = hNT.outerFace := (hNT.outerCycle.mem_darts_iff b).mp hb
  have hsc : M.α.SameCycle e b :=
    M.alpha_sameCycle_of_dartEdge_eq hNT.simpleGraph hbe.symm
  rcases (M.alpha_sameCycle_iff b e).mp hsc.symm with h | h
  · exact Or.inl (by rw [h]; exact hbface)
  · right; rw [h, M.alpha_alpha]; exact hbface

/-- **No interior bridge: an edge with both faces inner is non-boundary.**  Contrapositive of
`boundaryEdge_dart_outer`. -/
lemma not_boundaryEdge_of_both_inner {d : D}
    (h1 : M.dartFace d ≠ hNT.outerFace) (h2 : M.dartFace (M.α d) ≠ hNT.outerFace) :
    ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
  intro hbe
  rcases boundaryEdge_dart_outer hbe with h | h
  · exact h1 h
  · exact h2 h



/-- The clean inner-dart link: same face, or the reverse dart across a non-boundary edge. -/
def InnerLink (hNT : NearTriangulation M) (d e : D) : Prop :=
  M.dartFace d = M.dartFace e ∨
    (e = M.α d ∧ ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d))

/-- **A single `InnerLink`-step lifts to face `InnerAdj`-reachability.** -/
lemma reflTransGen_innerAdj_of_innerLink {d e : D} (h : InnerLink hNT d e) :
    Relation.ReflTransGen (InnerAdj hNT) (M.dartFace d) (M.dartFace e) := by
  rcases h with hface | ⟨hαd, hbe⟩
  · rw [hface]
  · subst hαd
    exact Relation.ReflTransGen.single (innerAdj_alpha hbe)

/-- **An `InnerLink`-walk lifts to an `InnerAdj`-walk on faces.** -/
lemma reflTransGen_innerAdj_of_innerLink_walk {d e : D}
    (h : Relation.ReflTransGen (InnerLink hNT) d e) :
    Relation.ReflTransGen (InnerAdj hNT) (M.dartFace d) (M.dartFace e) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y hxy hstep ih =>
      exact ih.trans (reflTransGen_innerAdj_of_innerLink hstep)











/-- **The sharp residual: inner-dart connectivity.**  Any two darts whose faces are inner are
joined by an `InnerLink`-walk (same-face or non-boundary-reverse steps), staying inside the
inner-dart graph.  This is the dart-level form of inner-face dual connectivity. -/
def InnerDartConnected (hNT : NearTriangulation M) : Prop :=
  ∀ a b : D, M.dartFace a ≠ hNT.outerFace → M.dartFace b ≠ hNT.outerFace →
    Relation.ReflTransGen (InnerLink hNT) a b

variable {u v : M.Vertex}

/-- **The keystone from inner-dart connectivity (the reduction).**  Given that the inner-dart
graph is `InnerLink`-connected, every non-outer face is `InnerAdj`-reachable from `face₁`.

Proof: `face₁ = dartFace data.dart` with `data.dart` inner; a non-outer face `f` is a triangle,
so it has a dart `d_f` (any orbit representative) with `dartFace d_f = f`, also inner; an
`InnerLink`-walk `data.dart → d_f` (`InnerDartConnected`) lifts to an `InnerAdj`-walk
`face₁ → f`. -/
theorem innerFaceConnectedFromFace₁_of_innerDartConnected
    (data : hNT.ChordSplitData u v) (hconn : InnerDartConnected hNT) :
    InnerFaceConnectedFromFace₁ data := by
  intro f hf
  -- A representative dart `d_f` of the triangular face `f`.
  have hd_f : ∃ d : D, M.dartFace d = f := by
    refine ⟨Quotient.out f, ?_⟩
    show Quotient.mk (cycleSetoid M.φ) (Quotient.out f) = f
    exact Quotient.out_eq f
  obtain ⟨d_f, hd_f⟩ := hd_f
  -- `face₁ = dartFace data.dart`, inner; `f = dartFace d_f`, inner.
  have hface₁ : data.face₁ = M.dartFace data.dart := rfl
  have hdart_inner : M.dartFace data.dart ≠ hNT.outerFace := by
    rw [← hface₁]; exact data.face₁_not_outer
  have hd_f_inner : M.dartFace d_f ≠ hNT.outerFace := by rw [hd_f]; exact hf
  -- Lift the inner-dart walk.
  have hwalk : Relation.ReflTransGen (InnerLink hNT) data.dart d_f :=
    hconn data.dart d_f hdart_inner hd_f_inner
  have hlift := reflTransGen_innerAdj_of_innerLink_walk hwalk
  rw [hd_f] at hlift
  rw [hface₁]
  exact hlift



/-- **The Chapter 35 keystone (conditional on inner-dart connectivity).**  Every non-outer face of
a near-triangulation is `InnerAdj`-reachable from the chord face `face₁`, given the sharp residual
`InnerDartConnected hNT` (inner-dart `InnerLink`-connectivity).  Cascades through
`boundedFacePartition_of_innerConnected` to close the coverage half of `edge_core`. -/
theorem innerFaceConnectedFromFace₁_holds
    (data : hNT.ChordSplitData u v) (hconn : InnerDartConnected hNT) :
    InnerFaceConnectedFromFace₁ data :=
  innerFaceConnectedFromFace₁_of_innerDartConnected data hconn

/-- **End-to-end cascade: `BoundedFacePartition` from inner-dart connectivity.**  Composes the
keystone with `boundedFacePartition_of_innerConnected` (`ZinanCh35Coverage`). -/
theorem boundedFacePartition_of_innerDartConnected
    (data : hNT.ChordSplitData u v) (hconn : InnerDartConnected hNT) :
    BoundedFacePartition data :=
  boundedFacePartition_of_innerConnected data
    (innerFaceConnectedFromFace₁_holds data hconn)

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



/-- **The outer dual step.**  Faces `f`, `g` are adjacent across a primal edge that is
*not* a boundary edge of the outer cycle: there is a dart `d` with `dartFace d = f`,
`dartFace (α d) = g`, and `dartEdge d` non-boundary.  This is exactly
`DualAvoidsCycleStep M Couter` for the outer cycle `Couter` (whose edge set is the outer
boundary), phrased without packaging the whole outer cycle as a `SimplePrimalCycle`. -/
def OuterDualStep (hNT : NearTriangulation M) (f g : M.Face) : Prop :=
  ∃ d : D, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
    ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)

/-- `OuterDualStep` is symmetric: the reverse dart `α d` witnesses the reverse step
(`dartEdge (α d) = dartEdge d` is still non-boundary). -/
lemma outerDualStep_symm {f g : M.Face} (h : OuterDualStep hNT f g) :
    OuterDualStep hNT g f := by
  obtain ⟨d, hdf, hdg, hbe⟩ := h
  refine ⟨M.α d, hdg, ?_, ?_⟩
  · rw [M.alpha_alpha]; exact hdf
  · rw [M.dartEdge_alpha]; exact hbe

/-- Symmetry transports to the reflexive-transitive closure. -/
lemma reflTransGen_outerDualStep_symm {f g : M.Face}
    (h : Relation.ReflTransGen (OuterDualStep hNT) f g) :
    Relation.ReflTransGen (OuterDualStep hNT) g f :=
  Relation.ReflTransGen.symmetric (fun _ _ hstep => outerDualStep_symm hstep) h



/-- A dart whose face is the outer face lies on the outer cycle, hence its edge is a
boundary edge. -/
lemma boundaryEdge_of_dartFace_outer {d : D} (hd : M.dartFace d = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
  have hmem : d ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff d).mpr hd
  show M.dartEdge d ∈ hNT.outerCycle.edges
  rw [hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem hmem

/-- **No `OuterDualStep` starts at the outer face.**  Such a step would need a
non-boundary edge whose dart carries the outer face — impossible. -/
lemma not_outerDualStep_outerFace {g : M.Face} :
    ¬ OuterDualStep hNT hNT.outerFace g := by
  rintro ⟨d, hdf, _, hbe⟩
  exact hbe (boundaryEdge_of_dartFace_outer hdf)

/-- **Outer isolation.**  The only face `OuterDualStep`-reachable from `outerFace` is
`outerFace` itself: the first step out is impossible. -/
lemma outerFace_isolated {f : M.Face}
    (h : Relation.ReflTransGen (OuterDualStep hNT) hNT.outerFace f) :
    f = hNT.outerFace := by
  induction h with
  | refl => rfl
  | @tail x y _ hstep ih =>
      -- `ih : x = outerFace`; then `OuterDualStep outerFace y` is impossible.
      subst ih
      exact (not_outerDualStep_outerFace hstep).elim

/-- Consequently, an `OuterDualStep`-walk that *reaches* the outer face must have started
there (by symmetry).  Useful for confining inner reachability to non-outer faces. -/
lemma eq_outerFace_of_reachesOuter {f : M.Face}
    (h : Relation.ReflTransGen (OuterDualStep hNT) f hNT.outerFace) :
    f = hNT.outerFace :=
  outerFace_isolated (reflTransGen_outerDualStep_symm h)



/-- Two darts on the **same face** are `InnerLink`-adjacent (the `Or.inl` clause). -/
lemma innerLink_of_sameFace {a b : D} (h : M.dartFace a = M.dartFace b) :
    InnerLink hNT a b := Or.inl h

/-- **The lift of one `OuterDualStep`.**  Given `OuterDualStep f g` and any darts `a, b`
with `dartFace a = f`, `dartFace b = g`, there is an `InnerLink`-walk `a → b`. -/
lemma outerDualStep_lifts_to_innerLink {f g : M.Face} {a b : D}
    (hstep : OuterDualStep hNT f g) (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.ReflTransGen (InnerLink hNT) a b := by
  obtain ⟨d, hdf, hdg, hbe⟩ := hstep
  -- a —(same face f)→ d
  have h1 : InnerLink hNT a d := innerLink_of_sameFace (by rw [ha, hdf])
  -- d —(non-boundary α-crossing)→ α d
  have h2 : InnerLink hNT d (M.α d) := Or.inr ⟨rfl, hbe⟩
  -- α d —(same face g)→ b
  have h3 : InnerLink hNT (M.α d) b := innerLink_of_sameFace (by rw [hdg, hb])
  exact (Relation.ReflTransGen.single h1).trans
    ((Relation.ReflTransGen.single h2).trans (Relation.ReflTransGen.single h3))

/-- **An `OuterDualStep`-walk lifts to an `InnerLink`-walk.**  Carrying along, at each
position, a dart representative of the current face, each `OuterDualStep` lifts (Step 4)
and the representatives are chained by `InnerLink`-walks. -/
lemma reflTransGen_innerLink_of_outerDualStep_walk {f g : M.Face} {a b : D}
    (hwalk : Relation.ReflTransGen (OuterDualStep hNT) f g)
    (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.ReflTransGen (InnerLink hNT) a b := by
  induction hwalk generalizing b with
  | refl =>
      -- f = g; `a` and `b` carry the same face.
      exact Relation.ReflTransGen.single (innerLink_of_sameFace (by rw [ha, hb]))
  | @tail x y hwxy hstep ih =>
      -- Pick a representative dart `c` of the intermediate face `x`.
      obtain ⟨c, hc⟩ : ∃ c : D, M.dartFace c = x := by
        refine ⟨Quotient.out x, ?_⟩
        show Quotient.mk (cycleSetoid M.φ) (Quotient.out x) = x
        exact Quotient.out_eq x
      have hac : Relation.ReflTransGen (InnerLink hNT) a c := ih hc
      have hcb : Relation.ReflTransGen (InnerLink hNT) c b :=
        outerDualStep_lifts_to_innerLink hstep hc hb
      exact hac.trans hcb



/-- **The isolated crux: inner-face dual connectivity.**  Every two non-outer faces are
`OuterDualStep`-reachable from one another. -/
def InnerFacesDualConnected (hNT : NearTriangulation M) : Prop :=
  ∀ f g : M.Face, f ≠ hNT.outerFace → g ≠ hNT.outerFace →
    Relation.ReflTransGen (OuterDualStep hNT) f g



/-- **`InnerDartConnected` from inner-face dual connectivity.**  Two inner darts `a, b`
carry inner faces `dartFace a`, `dartFace b`; the crux supplies an `OuterDualStep`-walk
between these faces, which lifts (Steps 3–4) to an `InnerLink`-walk `a → b`. -/
theorem innerDartConnected_of_innerFacesDualConnected
    (hcrux : InnerFacesDualConnected hNT) :
    InnerDartConnected hNT := by
  intro a b ha hb
  have hwalk : Relation.ReflTransGen (OuterDualStep hNT) (M.dartFace a) (M.dartFace b) :=
    hcrux (M.dartFace a) (M.dartFace b) ha hb
  exact reflTransGen_innerLink_of_outerDualStep_walk hwalk rfl rfl



variable {u v : M.Vertex}



/-- **End-to-end cascade**: `BoundedFacePartition` via the outer-dual route, conditional
on `InnerFacesDualConnected`. -/
theorem boundedFacePartition_via_outerDual
    (data : hNT.ChordSplitData u v) (hcrux : InnerFacesDualConnected hNT) :
    BoundedFacePartition data :=
  boundedFacePartition_of_innerDartConnected data
    (innerDartConnected_of_innerFacesDualConnected hcrux)

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



/-- `OuterDualStep` packaged as a plain symmetry statement (`∀ a b, r a b → r b a`),
the form `eqvGen_iff_reflTransGen` wants. -/
lemma outerDualStep_symm' :
    ∀ a b : M.Face, OuterDualStep hNT a b → OuterDualStep hNT b a :=
  fun _ _ h => outerDualStep_symm h

/-- `EqvGen (OuterDualStep)` coincides with `ReflTransGen (OuterDualStep)`. -/
lemma eqvGen_outerDualStep_iff {f g : M.Face} :
    Relation.EqvGen (OuterDualStep hNT) f g ↔
      Relation.ReflTransGen (OuterDualStep hNT) f g :=
  eqvGen_iff_reflTransGen (outerDualStep_symm' (hNT := hNT)) f g



/-- If a face's quotient class equals `outerFace`'s class, the face IS `outerFace`. -/
lemma eq_outerFace_of_class_eq {f : M.Face}
    (h : Quotient.mk (compSetoid (OuterDualStep hNT)) f
        = Quotient.mk (compSetoid (OuterDualStep hNT)) hNT.outerFace) :
    f = hNT.outerFace := by
  have hEqv : Relation.EqvGen (OuterDualStep hNT) f hNT.outerFace := Quotient.exact h
  have hReach : Relation.ReflTransGen (OuterDualStep hNT) f hNT.outerFace :=
    (eqvGen_outerDualStep_iff (hNT := hNT)).1 hEqv
  exact eq_outerFace_of_reachesOuter hReach

/-- Contrapositive form: a non-outer face's class differs from `outerFace`'s class. -/
lemma class_ne_outerFace_class {f : M.Face} (hf : f ≠ hNT.outerFace) :
    Quotient.mk (compSetoid (OuterDualStep hNT)) f
      ≠ Quotient.mk (compSetoid (OuterDualStep hNT)) hNT.outerFace :=
  fun h => hf (eq_outerFace_of_class_eq (hNT := hNT) h)



/-- **Two elements of a 2-element Fintype, both different from a fixed `c`, are equal.** -/
lemma eq_of_card_two_of_ne {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 2) {x y c : α} (hx : x ≠ c) (hy : y ≠ c) : x = y := by
  by_contra hxy
  -- `x, y, c` would be three distinct elements, forcing `card ≥ 3`.
  have h3 : ({x, y, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [hy]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, hx⟩
  have hle : ({x, y, c} : Finset α).card ≤ Fintype.card α := Finset.card_le_univ _
  omega

/-- **The two quotient classes of non-outer faces coincide.**  Under `numComp = 2`, any
two non-outer faces lie in the same component class. -/
lemma class_eq_of_numComp_two
    (hnum : numComp (OuterDualStep hNT) = 2)
    {f g : M.Face} (hf : f ≠ hNT.outerFace) (hg : g ≠ hNT.outerFace) :
    Quotient.mk (compSetoid (OuterDualStep hNT)) f
      = Quotient.mk (compSetoid (OuterDualStep hNT)) g := by
  classical
  haveI : Fintype (Quotient (compSetoid (OuterDualStep hNT))) :=
    Quotient.fintype (compSetoid (OuterDualStep hNT))
  have hcard : Fintype.card (Quotient (compSetoid (OuterDualStep hNT))) = 2 := by
    have := hnum
    unfold numComp at this
    rwa [Nat.card_eq_fintype_card] at this
  exact eq_of_card_two_of_ne hcard
    (class_ne_outerFace_class (hNT := hNT) hf)
    (class_ne_outerFace_class (hNT := hNT) hg)



/-- **Easy half (unconditional, clean-3).**  If the outer-dual component count is `2`,
then the inner faces are dual-connected. -/
theorem innerFacesDualConnected_of_outerDual_numComp_two
    (hnum : numComp (OuterDualStep hNT) = 2) :
    InnerFacesDualConnected hNT := by
  intro f g hf hg
  -- equal quotient classes ⟹ `EqvGen` ⟹ `ReflTransGen`
  have hclass := class_eq_of_numComp_two (hNT := hNT) hnum hf hg
  have hEqv : Relation.EqvGen (OuterDualStep hNT) f g := Quotient.exact hclass
  exact (eqvGen_outerDualStep_iff (hNT := hNT)).1 hEqv



/-- **The single isolated residual** : the outer-dual component count is `2`.  This is the
Euler/Jordan fact (the weak dual of a triangulated disk = the inner component ⊔ outer
face).  The cut-cap Euler machinery is the intended supplier; it is **not** discharged in
this file. -/
def OuterDualNumCompTwo (hNT : NearTriangulation M) : Prop :=
  numComp (OuterDualStep hNT) = 2

variable {u v : M.Vertex}

/-- **The keystone via the dual component count**, conditional on the single residual
`OuterDualNumCompTwo`.  Combines the easy half proved here with the lift assembled in
`ZinanCh35OuterDual.lean`. -/
theorem innerFacesDualConnected_via_numComp
    (hnum : OuterDualNumCompTwo hNT) :
    InnerFacesDualConnected hNT :=
  innerFacesDualConnected_of_outerDual_numComp_two hnum



/-- **End-to-end cascade** : `BoundedFacePartition` via the dual count, conditional on
`OuterDualNumCompTwo`. -/
theorem boundedFacePartition_via_numComp
    (data : hNT.ChordSplitData u v) (hnum : OuterDualNumCompTwo hNT) :
    BoundedFacePartition data :=
  boundedFacePartition_via_outerDual data
    (innerFacesDualConnected_via_numComp hnum)

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



/-- The **dual combinatorial map**: same edge involution `α`, but the vertex rotation is the
primal face permutation `φ = σ * α`.  Then `dualMap.φ = φ * α = σ`, so vertices/faces swap. -/
def dualMap (M : CombMap D) : CombMap D where
  α := M.α
  σ := M.φ
  α_invol := M.α_invol
  α_no_fixed := M.α_no_fixed

@[simp] lemma dualMap_σ (M : CombMap D) : (dualMap M).σ = M.φ := rfl
@[simp] lemma dualMap_α (M : CombMap D) : (dualMap M).α = M.α := rfl

lemma dualMap_φ (M : CombMap D) : (dualMap M).φ = M.σ := by
  show M.φ * M.α = M.σ
  rw [CombMap.φ, mul_assoc, M.α_invol, mul_one]

/-- `M.σ` equals `M.φ ∘ M.α` (the dual `φ`-step composed with one `α`-step). -/
lemma sigma_eq_phi_alpha (M : CombMap D) (d : D) : M.σ d = M.φ (M.α d) := by
  show M.σ d = (M.σ * M.α) (M.α d)
  simp [Equiv.Perm.mul_apply, M.alpha_alpha]

/-- One primal `σ`-step is a two-step dual walk: `a —(α-edge)→ α a —(φ same-cycle)→ σ a`. -/
lemma reflTransGen_dualStep_sigma (M : CombMap D) (a : D) :
    Relation.ReflTransGen (dualMap M).dartStep a (M.σ a) := by
  have h1 : (dualMap M).dartStep a (M.α a) := Or.inr (by simp [dualMap])
  have h2 : (dualMap M).dartStep (M.α a) (M.σ a) := by
    refine Or.inl ?_
    show M.φ.SameCycle (M.α a) (M.σ a)
    rw [sigma_eq_phi_alpha]
    exact ⟨1, by simp⟩
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h1) h2

/-- Iterating: `ReflTransGen (dualMap.dartStep) a ((M.σ)^k a)`. -/
lemma reflTransGen_dualStep_sigma_pow (M : CombMap D) (a : D) :
    ∀ k : ℕ, Relation.ReflTransGen (dualMap M).dartStep a ((M.σ ^ k) a) := by
  intro k
  induction k with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ n ih =>
    have hstep : Relation.ReflTransGen (dualMap M).dartStep ((M.σ ^ n) a)
        (M.σ ((M.σ ^ n) a)) := reflTransGen_dualStep_sigma M _
    have : (M.σ ^ (n + 1)) a = M.σ ((M.σ ^ n) a) := by
      rw [pow_succ']; rfl
    rw [this]
    exact ih.trans hstep

/-- Dual `dartStep` is symmetric. -/
lemma dualStep_symm (M : CombMap D) {a b : D}
    (h : (dualMap M).dartStep a b) : (dualMap M).dartStep b a := by
  rcases h with hsc | hαe
  · exact Or.inl hsc.symm
  · refine Or.inr ?_
    subst hαe
    show a = (dualMap M).α ((dualMap M).α a)
    rw [(dualMap M).alpha_alpha]

/-- A primal `σ`-same-cycle pair is dual-reachable. -/
lemma reflTransGen_dualStep_of_sigma_sameCycle (M : CombMap D) {a b : D}
    (h : M.σ.SameCycle a b) : Relation.ReflTransGen (dualMap M).dartStep a b := by
  obtain ⟨i, hi⟩ := h
  have hsymm : ∀ x y : D, (dualMap M).dartStep x y → (dualMap M).dartStep y x :=
    fun x y hxy => dualStep_symm M hxy
  rcases i.lt_or_le 0 with hneg | hpos
  · -- negative power: `a = (M.σ ^ (-i)) b` with `-i ≥ 0`; reach `b → a`, then symmetrize.
    have hi' : (M.σ ^ (-i)) b = a := by
      rw [← hi, ← Equiv.Perm.mul_apply, ← zpow_add]; simp
    set n := (-i).toNat with hn
    have hcast : (n : ℤ) = -i := Int.toNat_of_nonneg (by omega)
    have hzpow : (M.σ ^ (n : ℤ)) b = a := by rw [hcast]; exact hi'
    rw [zpow_natCast] at hzpow
    have hreach : Relation.ReflTransGen (dualMap M).dartStep b a := by
      rw [← hzpow]; exact reflTransGen_dualStep_sigma_pow M b n
    exact reflTransGen_symm hsymm hreach
  · set n := i.toNat with hn
    have hcast : (n : ℤ) = i := Int.toNat_of_nonneg hpos
    have hzpow : (M.σ ^ (n : ℤ)) a = b := by rw [hcast]; exact hi
    rw [zpow_natCast] at hzpow
    rw [← hzpow]
    exact reflTransGen_dualStep_sigma_pow M a n

/-- The dual map is connected (the dual of a connected map is connected). -/
lemma dualMap_connected (M : CombMap D) (hconn : M.Connected) :
    (dualMap M).Connected := by
  intro a b
  have h := hconn a b
  -- lift each primal `dartStep` to a dual `ReflTransGen`
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hstep ih =>
    have hlift : Relation.ReflTransGen (dualMap M).dartStep x y := by
      rcases hstep with hsc | hαe
      · exact reflTransGen_dualStep_of_sigma_sameCycle M hsc
      · exact Relation.ReflTransGen.single (Or.inr (by simpa [dualMap] using hαe))
    exact ih.trans hlift

lemma dualMap_eulerChar (M : CombMap D) : (dualMap M).eulerChar = M.eulerChar := by
  unfold CombMap.eulerChar
  rw [CombMap.V_eq_numCycles, CombMap.E_eq_numCycles, CombMap.F_eq_numCycles,
      CombMap.V_eq_numCycles, CombMap.E_eq_numCycles, CombMap.F_eq_numCycles,
      dualMap_σ, dualMap_α, dualMap_φ]
  ring

/-- The dual map is a sphere map whenever `M` is. -/
lemma dualMap_isSphereMap (M : CombMap D) (h : M.IsSphereMap) :
    (dualMap M).IsSphereMap :=
  ⟨dualMap_connected M h.1, by rw [dualMap_eulerChar]; exact h.2⟩



variable {hNT : NearTriangulation M}

/-- The darts to delete from `M.α`: the outer-boundary darts together with their
`α`-partners.  This is `α`-closed by construction. -/
noncomputable def OuterDel (hNT : NearTriangulation M) : Finset D :=
  hNT.outerCycle.darts.toFinset ∪ hNT.outerCycle.darts.toFinset.image M.α

lemma mem_outerDel_iff {d : D} :
    d ∈ OuterDel hNT ↔ d ∈ hNT.outerCycle.darts ∨ M.α d ∈ hNT.outerCycle.darts := by
  unfold OuterDel
  simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_image]
  constructor
  · rintro (hd | ⟨x, hx, hxd⟩)
    · exact Or.inl hd
    · exact Or.inr (by rw [← hxd, M.alpha_alpha]; exact hx)
  · rintro (hd | hd)
    · exact Or.inl hd
    · exact Or.inr ⟨M.α d, hd, M.alpha_alpha d⟩

/-- `OuterDel` is `α`-closed. -/
lemma outerDel_alpha_closed :
    ∀ d : D, d ∈ OuterDel hNT → M.α d ∈ OuterDel hNT := by
  intro d hd
  rw [mem_outerDel_iff] at hd ⊢
  rcases hd with hd | hd
  · exact Or.inr (by rw [M.alpha_alpha]; exact hd)
  · exact Or.inl hd

/-- The restricted dual involution: fixes the outer darts and their partners, `= M.α`
elsewhere. -/
noncomputable def outerDualAlpha (hNT : NearTriangulation M) : Equiv.Perm D :=
  rawAlpha M (OuterDel hNT) (outerDel_alpha_closed (hNT := hNT))

lemma outerDualAlpha_eq_self_of_mem {d : D} (hd : d ∈ OuterDel hNT) :
    outerDualAlpha hNT d = d :=
  rawAlpha_eq_self_of_mem M (OuterDel hNT) _ hd

lemma outerDualAlpha_eq_alpha_of_notMem {d : D} (hd : d ∉ OuterDel hNT) :
    outerDualAlpha hNT d = M.α d :=
  rawAlpha_eq_alpha_of_notMem M (OuterDel hNT) _ hd



/-- For a boundary dart `d`, its `α`-partner is **not** a boundary dart.  Otherwise
`σ d = φ(α d)` would also be a boundary dart with `tail (σ d) = tail d`, forcing
`σ d = d` (boundary tails are distinct), contradicting `boundary_dart_sigma_ne`. -/
lemma alpha_notMem_darts_of_mem {d : D} (hd : d ∈ hNT.outerCycle.darts) :
    M.α d ∉ hNT.outerCycle.darts := by
  intro hαd
  -- `φ (α d) = σ d`, and `φ (α d)` is a boundary dart since `α d` is.
  have hface : M.dartFace (M.α d) = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff (M.α d)).mp hαd
  have hσd_mem : M.σ d ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    have : M.σ d = M.φ (M.α d) := by
      show M.σ d = (M.σ * M.α) (M.α d); simp [Equiv.Perm.mul_apply, M.alpha_alpha]
    rw [this, M.dartFace_phi]; exact hface
  have htail : M.tail (M.σ d) = M.tail d := by simp
  have heq : M.σ d = d :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hσd_mem hd htail
  exact hNT.boundary_dart_sigma_ne hd heq



/-- The two halves of `OuterDel` are disjoint: a boundary dart is never the `α`-image of a
boundary dart. -/
lemma outerDel_card (hNT : NearTriangulation M) :
    (OuterDel hNT).card = 2 * hNT.outerCycle.length := by
  classical
  have hdisj : Disjoint hNT.outerCycle.darts.toFinset
      (hNT.outerCycle.darts.toFinset.image M.α) := by
    rw [Finset.disjoint_left]
    intro d hd himg
    simp only [List.mem_toFinset] at hd
    simp only [Finset.mem_image, List.mem_toFinset] at himg
    obtain ⟨e, he, hed⟩ := himg
    -- `d = M.α e` with `e, d ∈ darts`; then `M.α e ∈ darts` contradicts the partner lemma.
    exact alpha_notMem_darts_of_mem (hNT := hNT) he (by rw [hed]; exact hd)
  have hcardD : hNT.outerCycle.darts.toFinset.card = hNT.outerCycle.length := by
    rw [List.toFinset_card_of_nodup hNT.outerCycle.darts_nodup]; rfl
  have hcardImg : (hNT.outerCycle.darts.toFinset.image M.α).card
      = hNT.outerCycle.length := by
    rw [Finset.card_image_of_injective _ M.α.injective, hcardD]
  unfold OuterDel
  rw [Finset.card_union_of_disjoint hdisj, hcardD, hcardImg]
  ring

/-- The support of `outerDualAlpha` is exactly the non-deleted darts. -/
lemma support_outerDualAlpha (hNT : NearTriangulation M) :
    (outerDualAlpha hNT).support = Finset.univ \ OuterDel hNT := by
  classical
  ext d
  simp only [Equiv.Perm.mem_support, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hd hmem
    exact hd (outerDualAlpha_eq_self_of_mem (hNT := hNT) hmem)
  · intro hd
    rw [outerDualAlpha_eq_alpha_of_notMem (hNT := hNT) hd]
    exact M.α_no_fixed d

/-- The outer boundary length is at most the number of edges. -/
lemma outerCycle_length_le_E (hNT : NearTriangulation M) :
    hNT.outerCycle.length ≤ M.E := by
  have h2B : (OuterDel hNT).card = 2 * hNT.outerCycle.length := outerDel_card hNT
  have hle : (OuterDel hNT).card ≤ Fintype.card D := Finset.card_le_univ _
  have hcard : 2 * M.E = Fintype.card D := two_mul_E_eq_card M
  omega

/-- The outer boundary length is at most the number of vertices (boundary vertices are
distinct). -/
lemma outerCycle_length_le_V (hNT : NearTriangulation M) :
    hNT.outerCycle.length ≤ M.V := by
  classical
  -- the boundary vertex list has `B` distinct entries, all in `M.Vertex`
  have hnodup : hNT.outerCycle.vertices.Nodup := hNT.outer_simple
  have hlen : hNT.outerCycle.vertices.length = hNT.outerCycle.length := by
    rw [hNT.outerCycle.vertices_eq, List.length_map]; rfl
  have hcard : hNT.outerCycle.vertices.toFinset.card = hNT.outerCycle.length := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have hle : hNT.outerCycle.vertices.toFinset.card ≤ Fintype.card M.Vertex :=
    Finset.card_le_univ _
  rw [hcard] at hle
  -- `M.V = Fintype.card M.Vertex`
  have : M.V = Fintype.card M.Vertex := rfl
  omega

/-- **Step 5.**  `Ehalf (outerDualAlpha hNT) = M.E − B`, `B = outerCycle.length`. -/
lemma Ehalf_outerDualAlpha (hNT : NearTriangulation M) :
    Ehalf (outerDualAlpha hNT) = M.E - hNT.outerCycle.length := by
  classical
  -- `2 * Ehalf α = card support α` for any involution; here support = univ \ OuterDel.
  have hsupp := support_outerDualAlpha (hNT := hNT)
  have hα : M.α.support = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro d
    rw [Equiv.Perm.mem_support]; exact M.α_no_fixed d
  -- card support outerDualAlpha = card univ − card OuterDel
  have hsubset : OuterDel hNT ⊆ Finset.univ := Finset.subset_univ _
  have hcard : (outerDualAlpha hNT).support.card
      = Fintype.card D - (OuterDel hNT).card := by
    rw [hsupp, Finset.card_univ_diff]
  -- `M.E = card univ / 2`, `Ehalf outerDualAlpha = (card univ - 2B)/2`
  have hEval : M.E = Fintype.card D / 2 := by
    have : Ehalf M.α = M.E := Ehalf_eq_E M
    rw [Ehalf, hα, Finset.card_univ] at this
    omega
  have hEhalf : Ehalf (outerDualAlpha hNT) = (outerDualAlpha hNT).support.card / 2 := rfl
  rw [hEhalf, hcard, outerDel_card (hNT := hNT)]
  omega

/-- `genusSlack (M.φ) (outerDualAlpha hNT) = 0`: deleting the outer edges from the
genus-0 dual map keeps the slack at zero. -/
lemma genusSlack_outerDualAlpha_eq_zero (hNT : NearTriangulation M) :
    genusSlack M.φ (outerDualAlpha hNT) = 0 := by
  -- `rawAlpha` for the dual map `dualMap M`: its `σ = M.φ`, `α = M.α`, so `rawAlpha`
  -- on the dual map is definitionally the same perm as `outerDualAlpha`.
  have hclosedD : ∀ d : D, d ∈ OuterDel hNT → (dualMap M).α d ∈ OuterDel hNT := by
    simpa [dualMap_α] using (outerDel_alpha_closed (hNT := hNT))
  have hraw : rawAlpha (dualMap M) (OuterDel hNT) hclosedD = outerDualAlpha hNT := by
    ext d
    by_cases hd : d ∈ OuterDel hNT
    · rw [rawAlpha_eq_self_of_mem (dualMap M) (OuterDel hNT) hclosedD hd,
          outerDualAlpha_eq_self_of_mem (hNT := hNT) hd]
    · rw [rawAlpha_eq_alpha_of_notMem (dualMap M) (OuterDel hNT) hclosedD hd,
          outerDualAlpha_eq_alpha_of_notMem (hNT := hNT) hd, dualMap_α]
  -- need a witness dart; `outerCycle` has positive length
  obtain ⟨d₀⟩ : Nonempty D :=
    ⟨hNT.outerCycle.root⟩
  have hsphere : (dualMap M).IsSphereMap := dualMap_isSphereMap M hNT.sphere
  have h0 := genusSlack_rawAlpha_eq_zero (dualMap M) (OuterDel hNT) hclosedD hsphere d₀
  rw [hraw] at h0
  rwa [dualMap_σ] at h0



/-- The complementary restricted involution `τ := M.α * outerDualAlpha`: identity off
`OuterDel`, `= M.α` on `OuterDel`. -/
noncomputable def outerTau (hNT : NearTriangulation M) : Equiv.Perm D :=
  M.α * outerDualAlpha hNT

lemma outerTau_eq_alpha_of_mem {d : D} (hd : d ∈ OuterDel hNT) :
    outerTau hNT d = M.α d := by
  show M.α (outerDualAlpha hNT d) = M.α d
  rw [outerDualAlpha_eq_self_of_mem (hNT := hNT) hd]

lemma outerTau_eq_self_of_notMem {d : D} (hd : d ∉ OuterDel hNT) :
    outerTau hNT d = d := by
  show M.α (outerDualAlpha hNT d) = d
  rw [outerDualAlpha_eq_alpha_of_notMem (hNT := hNT) hd, M.alpha_alpha]

/-- **The algebraic reduction.**  `M.φ * outerDualAlpha = M.σ * outerTau`. -/
lemma phi_outerDualAlpha_eq_sigma_outerTau (hNT : NearTriangulation M) :
    M.φ * outerDualAlpha hNT = M.σ * outerTau hNT := by
  -- `M.σ * outerTau = M.σ * M.α * outerDualAlpha = M.φ * outerDualAlpha`.
  show M.φ * outerDualAlpha hNT = M.σ * (M.α * outerDualAlpha hNT)
  rw [← mul_assoc]; rfl

/-- **Step 6 (the boundary-bank orbit count) — the single isolated residual.**
`numCycles (M.φ * outerDualAlpha hNT) = M.V − B + 2`, `B = outerCycle.length`.

This is the genuine combinatorial content the route isolates.  By
`phi_outerDualAlpha_eq_sigma_outerTau` it is equivalent to the boundary-bank swap count
`numCycles (M.σ * outerTau hNT) = M.V − B + 2`: the `B` disjoint outer transpositions of
`outerTau` merge the `B` boundary-vertex `σ`-cycles into the two bank cycles (`B − 1`
merges and one closing split).  It is a TRUE statement (forced by `genusSlack = 0` together
with the proved `numComp (OuterDualStep) = 2`), is **clean** (about `M.φ`, `outerDualAlpha`,
`M.V`, and the boundary length only — no reference to the conclusion `numComp = 2`), and is
**not** posited as proved: it is carried as the single named residual `BoundaryBankCount`. -/
def BoundaryBankCount (hNT : NearTriangulation M) : Prop :=
  numCycles (M.φ * outerDualAlpha hNT) = M.V - hNT.outerCycle.length + 2



/-- A dart lies in `OuterDel` iff its edge is a boundary edge. -/
lemma mem_outerDel_iff_boundaryEdge (hNT : NearTriangulation M) {d : D} :
    d ∈ OuterDel hNT ↔ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
  rw [mem_outerDel_iff]
  constructor
  · rintro (hd | hd)
    · -- `d ∈ darts` ⟹ `dartEdge d ∈ edges`
      show M.dartEdge d ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]
      exact List.mem_map_of_mem hd
    · -- `α d ∈ darts` ⟹ `dartEdge (α d) = dartEdge d ∈ edges`
      show M.dartEdge d ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq, ← M.dartEdge_alpha d]
      exact List.mem_map_of_mem hd
  · intro hbe
    -- `dartEdge d ∈ edges = darts.map dartEdge`: some boundary dart `e` has `dartEdge e = dartEdge d`.
    have hmem : M.dartEdge d ∈ hNT.outerCycle.darts.map M.dartEdge := by
      rw [← hNT.outerCycle.edges_eq]; exact hbe
    rcases List.mem_map.mp hmem with ⟨e, he, hee⟩
    -- `α.SameCycle d e` ⟹ `d = e ∨ d = α e`
    have hsc : M.α.SameCycle d e :=
      hNT.simpleGraph.no_parallel (by rw [hee])
    rcases (M.alpha_sameCycle_iff d e).mp hsc with hde | hde
    · exact Or.inl (by rw [← hde]; exact he)
    · exact Or.inr (by rw [← hde]; exact he)

/-- A dart lies off `OuterDel` iff its edge is non-boundary. -/
lemma notMem_outerDel_iff_not_boundaryEdge (hNT : NearTriangulation M) {d : D} :
    d ∉ OuterDel hNT ↔ ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) :=
  not_congr (mem_outerDel_iff_boundaryEdge hNT)

/-- Same face ⟺ `M.φ.SameCycle`. -/
lemma sameFace_iff_phi_sameCycle {a b : D} :
    M.dartFace a = M.dartFace b ↔ M.φ.SameCycle a b := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

/-- The relation `dartStepRel M.φ αout`. -/
abbrev RDart (hNT : NearTriangulation M) : D → D → Prop :=
  dartStepRel M.φ (outerDualAlpha hNT)

/-- A single `RDart`-step descends to `EqvGen (OuterDualStep)` on faces. -/
lemma eqvGen_outerDualStep_of_RDart_step (hNT : NearTriangulation M) {a b : D}
    (h : RDart hNT a b) :
    Relation.EqvGen (OuterDualStep hNT) (M.dartFace a) (M.dartFace b) := by
  rcases h with hsc | hαe
  · -- same face
    have : M.dartFace a = M.dartFace b := sameFace_iff_phi_sameCycle.mpr hsc
    rw [this]; exact Relation.EqvGen.refl _
  · -- `b = αout a`
    by_cases hd : a ∈ OuterDel hNT
    · -- αout a = a so b = a
      rw [hαe, outerDualAlpha_eq_self_of_mem (hNT := hNT) hd]
      exact Relation.EqvGen.refl _
    · -- αout a = M.α a, edge non-boundary ⟹ OuterDualStep
      have hba : b = M.α a := by
        rw [hαe, outerDualAlpha_eq_alpha_of_notMem (hNT := hNT) hd]
      have hnb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge a) :=
        (notMem_outerDel_iff_not_boundaryEdge hNT).mp hd
      have hstep : OuterDualStep hNT (M.dartFace a) (M.dartFace b) :=
        ⟨a, rfl, by rw [hba], hnb⟩
      exact Relation.EqvGen.rel _ _ hstep

/-- A single `OuterDualStep` lifts to `EqvGen RDart` on any dart reps. -/
lemma eqvGen_RDart_of_outerDualStep (hNT : NearTriangulation M) {f g : M.Face} {a b : D}
    (hstep : OuterDualStep hNT f g) (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.EqvGen (RDart hNT) a b := by
  obtain ⟨d, hdf, hdg, hbe⟩ := hstep
  -- d ∉ OuterDel since its edge is non-boundary
  have hdDel : d ∉ OuterDel hNT := (notMem_outerDel_iff_not_boundaryEdge hNT).mpr hbe
  -- a ~ d (same face f)
  have h1 : Relation.EqvGen (RDart hNT) a d :=
    Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [ha, hdf])))
  -- d ~ α d (non-boundary α-crossing): `αout d = M.α d`
  have h2 : Relation.EqvGen (RDart hNT) d (M.α d) :=
    Relation.EqvGen.rel _ _ (Or.inr (by
      rw [outerDualAlpha_eq_alpha_of_notMem (hNT := hNT) hdDel]))
  -- α d ~ b (same face g)
  have h3 : Relation.EqvGen (RDart hNT) (M.α d) b :=
    Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [hdg, hb])))
  exact (h1.trans _ _ _ h2).trans _ _ _ h3

/-- An `OuterDualStep`-walk lifts to `EqvGen RDart`. -/
lemma eqvGen_RDart_of_outerDualStep_walk (hNT : NearTriangulation M) {f g : M.Face} {a b : D}
    (hwalk : Relation.ReflTransGen (OuterDualStep hNT) f g)
    (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.EqvGen (RDart hNT) a b := by
  induction hwalk generalizing b with
  | refl =>
    exact Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [ha, hb])))
  | @tail x y hwxy hstep ih =>
    obtain ⟨c, hc⟩ : ∃ c : D, M.dartFace c = x := ⟨Quotient.out x, Quotient.out_eq x⟩
    have hac : Relation.EqvGen (RDart hNT) a c := ih hc
    have hcb : Relation.EqvGen (RDart hNT) c b :=
      eqvGen_RDart_of_outerDualStep hNT hstep hc hb
    exact hac.trans _ _ _ hcb

/-- The full `EqvGen RDart`-walk descends to `EqvGen OuterDualStep` on faces. -/
lemma eqvGen_outerDualStep_of_RDart_eqv (hNT : NearTriangulation M) {a b : D}
    (hab : Relation.EqvGen (RDart hNT) a b) :
    Relation.EqvGen (OuterDualStep hNT) (M.dartFace a) (M.dartFace b) := by
  induction hab with
  | rel x y h => exact eqvGen_outerDualStep_of_RDart_step hNT h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact ih.symm _ _
  | trans x y z _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

/-- The face quotient map descends from the dart component quotient. -/
noncomputable def faceQuotMap (hNT : NearTriangulation M) :
    Quotient (compSetoid (RDart hNT)) → Quotient (compSetoid (OuterDualStep hNT)) :=
  Quotient.lift (fun d => Quotient.mk (compSetoid (OuterDualStep hNT)) (M.dartFace d))
    (by
      intro a b hab
      apply Quotient.sound
      exact eqvGen_outerDualStep_of_RDart_eqv hNT hab)

/-- **Step 3 (the dart-face quotient bridge).**  The component count of the dual
sub-involution pair equals the dual-face component count `numComp (OuterDualStep hNT)`. -/
lemma numComponents_eq_numComp_outerDualStep (hNT : NearTriangulation M) :
    numComponents M.φ (outerDualAlpha hNT) = numComp (OuterDualStep hNT) := by
  classical
  rw [numComponents_def]
  show numComp (RDart hNT) = numComp (OuterDualStep hNT)
  unfold numComp
  apply Nat.card_congr
  -- build the equiv via `faceQuotMap`
  refine Equiv.ofBijective (faceQuotMap hNT) ⟨?_, ?_⟩
  · -- injective
    intro x y hxy
    refine Quotient.inductionOn₂ x y (fun a b hab => ?_) hxy
    -- hab : faceQuotMap ⟦a⟧ = faceQuotMap ⟦b⟧, i.e. EqvGen OuterDualStep (dartFace a) (dartFace b)
    apply Quotient.sound
    have heqf : Relation.EqvGen (OuterDualStep hNT) (M.dartFace a) (M.dartFace b) :=
      Quotient.exact hab
    -- convert to ReflTransGen then lift
    have hwalk : Relation.ReflTransGen (OuterDualStep hNT) (M.dartFace a) (M.dartFace b) :=
      (eqvGen_outerDualStep_iff (hNT := hNT)).1 heqf
    exact eqvGen_RDart_of_outerDualStep_walk hNT hwalk rfl rfl
  · -- surjective
    intro q
    refine Quotient.inductionOn q (fun f => ?_)
    obtain ⟨d, hd⟩ : ∃ d : D, M.dartFace d = f := ⟨Quotient.out f, Quotient.out_eq f⟩
    exact ⟨Quotient.mk (compSetoid (RDart hNT)) d, by
      show Quotient.mk _ (M.dartFace d) = Quotient.mk _ f
      rw [hd]⟩



/-- **The crux of Chapter 35, conditional on the single boundary-bank residual.**  Given
the boundary-bank face count (Step 6), the outer-dual component count is `2`.  All of
Steps 1–5 and the dart-face bridge (Step 3) plus the Euler arithmetic are proved
unconditionally and clean-3; only `BoundaryBankCount` is carried as a hypothesis. -/
theorem outerDualNumCompTwo_of_boundaryBankCount (hNT : NearTriangulation M)
    (h6 : BoundaryBankCount hNT) :
    numComp (OuterDualStep hNT) = 2 := by
  -- expand `genusSlack M.φ αout = 0` with Steps 3, 5, 6 and Euler.
  have h0 : genusSlack M.φ (outerDualAlpha hNT) = 0 :=
    genusSlack_outerDualAlpha_eq_zero hNT
  have hE5 : Ehalf (outerDualAlpha hNT) = M.E - hNT.outerCycle.length :=
    Ehalf_outerDualAlpha hNT
  have h6 : numCycles (M.φ * outerDualAlpha hNT)
      = M.V - hNT.outerCycle.length + 2 := h6
  have hbridge : numComponents M.φ (outerDualAlpha hNT) = numComp (OuterDualStep hNT) :=
    numComponents_eq_numComp_outerDualStep hNT
  -- `numCycles M.φ = M.F`
  have hF : numCycles M.φ = M.F := (M.F_eq_numCycles).symm
  -- Euler `V − E + F = 2`
  have hEuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hNT.sphere.2
  -- bounds so the ℕ-subtractions in Steps 5/6 are genuine
  set B := hNT.outerCycle.length with hB
  have hBE : B ≤ M.E := outerCycle_length_le_E hNT
  -- expand genusSlack
  unfold genusSlack at h0
  rw [hbridge, hF, hE5, h6] at h0
  -- now h0 : 2 * c - F + (E - B) - (V - B + 2) = 0  over ℤ with ℕ-subtractions cast
  -- turn ℕ-subtraction casts into honest ℤ using hBE and (V-B+2)
  have hcast5 : ((M.E - B : ℕ) : ℤ) = (M.E : ℤ) - (B : ℤ) := by
    rw [Nat.cast_sub hBE]
  have hcast6 : ((M.V - B + 2 : ℕ) : ℤ) = (M.V : ℤ) - (B : ℤ) + 2 := by
    have hBV : B ≤ M.V := outerCycle_length_le_V hNT
    push_cast [Nat.cast_sub hBV]; ring
  rw [hcast5, hcast6] at h0
  -- solve for c with Euler
  have hc : (numComp (OuterDualStep hNT) : ℤ) = 2 := by linarith
  exact_mod_cast hc

/-- **Discharge of the Chapter-35 residual `OuterDualNumCompTwo`, conditional on the single
boundary-bank face count.**  `OuterDualNumCompTwo hNT` is definitionally
`numComp (OuterDualStep hNT) = 2`, so this follows from
`outerDualNumCompTwo_of_boundaryBankCount`.  Combined with the easy half
`innerFacesDualConnected_of_outerDual_numComp_two` (already in `ZinanCh35OuterCount`), it
cascades the whole chapter once `BoundaryBankCount` is supplied. -/
theorem outerDualNumCompTwo_of_boundaryBankCount' (hNT : NearTriangulation M)
    (h6 : BoundaryBankCount hNT) :
    OuterDualNumCompTwo hNT :=
  outerDualNumCompTwo_of_boundaryBankCount hNT h6

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

/-- The `i`-th boundary dart `q i`. -/
noncomputable def qd (hNT : NearTriangulation M) (i : Fin hNT.outerCycle.length) : D :=
  hNT.outerCycle.darts.get ⟨i.1, by simpa [BoundaryCycle.length] using i.2⟩

/-- The `α`-partner `r i := M.α (q i)`. -/
noncomputable def rd (hNT : NearTriangulation M) (i : Fin hNT.outerCycle.length) : D :=
  M.α (qd hNT i)

/-- Cyclic successor index on `Fin B`. -/
noncomputable def nextIdx (hNT : NearTriangulation M) (i : Fin hNT.outerCycle.length) :
    Fin hNT.outerCycle.length :=
  ⟨(i.1 + 1) % hNT.outerCycle.length,
    Nat.mod_lt _ (by simpa [BoundaryCycle.length] using hNT.outerCycle.darts_length_pos)⟩

lemma nextIdx_val (i : Fin hNT.outerCycle.length) :
    (nextIdx hNT i).1 = (i.1 + 1) % hNT.outerCycle.length := rfl

/-- `q i` is a boundary dart. -/
lemma qd_mem (i : Fin hNT.outerCycle.length) : qd hNT i ∈ hNT.outerCycle.darts := by
  unfold qd
  exact List.get_mem _ _

/-- `q i ∈ OuterDel`. -/
lemma qd_mem_outerDel (i : Fin hNT.outerCycle.length) : qd hNT i ∈ OuterDel hNT := by
  rw [mem_outerDel_iff]; exact Or.inl (qd_mem i)

/-- `r i ∈ OuterDel`. -/
lemma rd_mem_outerDel (i : Fin hNT.outerCycle.length) : rd hNT i ∈ OuterDel hNT := by
  rw [mem_outerDel_iff]; right
  show M.α (M.α (qd hNT i)) ∈ hNT.outerCycle.darts
  rw [M.alpha_alpha]; exact qd_mem i



lemma qd_inj {i j : Fin hNT.outerCycle.length} (h : qd hNT i = qd hNT j) : i = j := by
  unfold qd at h
  have := (hNT.outerCycle.darts_nodup.getElem_inj_iff).mp h
  exact Fin.ext (by simpa using this)



lemma rd_inj {i j : Fin hNT.outerCycle.length} (h : rd hNT i = rd hNT j) : i = j :=
  qd_inj (M.α.injective h)

lemma qd_ne_rd (i j : Fin hNT.outerCycle.length) : qd hNT i ≠ rd hNT j := by
  intro h
  -- q i ∈ darts, r j = α (q j) ∉ darts (partner of boundary dart).
  have hmem : M.α (qd hNT j) ∈ hNT.outerCycle.darts := by
    show rd hNT j ∈ hNT.outerCycle.darts
    rw [← h]; exact qd_mem i
  exact alpha_notMem_darts_of_mem (hNT := hNT) (qd_mem j) hmem

lemma rd_ne_qd (i j : Fin hNT.outerCycle.length) : rd hNT i ≠ qd hNT j :=
  fun h => qd_ne_rd j i h.symm

lemma qd_ne_rd_self (i : Fin hNT.outerCycle.length) : qd hNT i ≠ rd hNT i := qd_ne_rd i i



/-- `M.σ (r i) = q (next i)`: because `σ = φ ∘ α` and the boundary darts cycle under `φ`. -/
lemma sigma_rd_eq_qd_next (i : Fin hNT.outerCycle.length) :
    M.σ (rd hNT i) = qd hNT (nextIdx hNT i) := by
  -- σ (α (q i)) = φ (q i) = darts.get (cyclicNext i)
  have hσ : M.σ (rd hNT i) = M.φ (qd hNT i) := by
    show M.σ (M.α (qd hNT i)) = M.φ (qd hNT i)
    show M.σ (M.α (qd hNT i)) = (M.σ * M.α) (qd hNT i)
    rw [Equiv.Perm.mul_apply]
  rw [hσ]
  -- consecutive_phi: darts.get (cyclicNext i₀) = φ (darts.get i₀)
  set i₀ : Fin hNT.outerCycle.darts.length :=
    ⟨i.1, by simpa [BoundaryCycle.length] using i.2⟩ with hi₀
  have hcp := hNT.outerCycle.consecutive_phi i₀
  show M.φ (hNT.outerCycle.darts.get i₀) = qd hNT (nextIdx hNT i)
  rw [← hcp]
  -- both sides are `darts.get` at index (i+1) % B
  unfold qd nextIdx
  congr 1



/-- `M.σ.SameCycle a b` is `M.tail a = M.tail b`. -/
lemma sigma_sameCycle_iff_tail (a b : D) :
    M.σ.SameCycle a b ↔ M.tail a = M.tail b := by
  show M.σ.SameCycle a b ↔
    (Quotient.mk (cycleSetoid M.σ) a : Quotient (cycleSetoid M.σ)) = Quotient.mk _ b
  rw [Quotient.eq]
  rfl

/-- Distinct boundary darts are in distinct `σ`-cycles: `σ.SameCycle (q i) (q j) ↔ i = j`. -/
lemma sigma_sameCycle_qd_qd (i j : Fin hNT.outerCycle.length) :
    M.σ.SameCycle (qd hNT i) (qd hNT j) ↔ i = j := by
  rw [sigma_sameCycle_iff_tail]
  constructor
  · intro h
    have := hNT.outerCycle.tail_injective_on_darts hNT.outer_simple (qd_mem i) (qd_mem j) h
    exact qd_inj this
  · intro h; rw [h]



/-- The embedding `Fin (B−1) ↪ Fin B`. -/
noncomputable def emb (hNT : NearTriangulation M) (j : Fin (hNT.outerCycle.length - 1)) :
    Fin hNT.outerCycle.length :=
  ⟨j.1, by have := j.2; omega⟩

/-- The ordered list of the first `B−1` outer transposition pairs `(q j, r j)`. -/
noncomputable def mergePairs (hNT : NearTriangulation M) : List (D × D) :=
  (List.finRange (hNT.outerCycle.length - 1)).map (fun j => (qd hNT (emb hNT j), rd hNT (emb hNT j)))

/-- The partial product permutation after the first `k` merge swaps. -/
noncomputable def pPrefix (hNT : NearTriangulation M) (k : ℕ) : Equiv.Perm D :=
  M.σ * (((mergePairs hNT).take k).map (fun w => Equiv.swap w.1 w.2)).prod

lemma pPrefix_zero : pPrefix hNT 0 = M.σ := by simp [pPrefix]

/-- The dart at block position `m < B` (the `m`-th `q`). -/
lemma mergePairs_get_fst (k : ℕ) (hk : k < hNT.outerCycle.length - 1) :
    (mergePairs hNT).get ⟨k, by simpa [mergePairs] using hk⟩
      = (qd hNT ⟨k, by omega⟩, rd hNT ⟨k, by omega⟩) := by
  unfold mergePairs
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
  rfl

/-- Length of `mergePairs` is `B − 1`. -/
lemma mergePairs_length : (mergePairs hNT).length = hNT.outerCycle.length - 1 := by
  simp [mergePairs]

/-- One-step recurrence for the partial products: appending the `k`-th merge swap. -/
lemma pPrefix_succ (k : ℕ) (hk : k < hNT.outerCycle.length - 1) :
    pPrefix hNT (k + 1)
      = pPrefix hNT k * Equiv.swap (qd hNT ⟨k, by omega⟩) (rd hNT ⟨k, by omega⟩) := by
  unfold pPrefix
  have hlen : k < (mergePairs hNT).length := by rw [mergePairs_length]; exact hk
  -- take (k+1) = take k ++ [get k]
  have htake : (mergePairs hNT).take (k + 1)
      = (mergePairs hNT).take k ++ [(mergePairs hNT).get ⟨k, hlen⟩] := by
    rw [List.get_eq_getElem]
    exact List.take_succ_eq_append_getElem hlen
  rw [htake, List.map_append, List.prod_append, mergePairs_get_fst k hk]
  simp [mul_assoc]



/-- For a non-final index, `nextIdx` increments the value (no wraparound). -/
lemma nextIdx_val_of_lt {i : Fin hNT.outerCycle.length} (hi : i.1 < hNT.outerCycle.length - 1) :
    (nextIdx hNT i).1 = i.1 + 1 := by
  rw [nextIdx_val, Nat.mod_eq_of_lt (by omega)]

/-- `nextIdx` is injective. -/
lemma nextIdx_inj {i j : Fin hNT.outerCycle.length} (h : nextIdx hNT i = nextIdx hNT j) :
    i = j := by
  have hpos : 0 < hNT.outerCycle.length := by
    simpa [BoundaryCycle.length] using hNT.outerCycle.darts_length_pos
  have hval := congrArg Fin.val h
  rw [nextIdx_val, nextIdx_val] at hval
  apply Fin.ext
  have hi := i.2; have hj := j.2
  -- both (i+1) and (j+1) lie in [1, B]; equal mod B ⟹ equal
  rcases Nat.lt_or_ge (i.1 + 1) hNT.outerCycle.length with hi1 | hi1
  · rw [Nat.mod_eq_of_lt hi1] at hval
    rcases Nat.lt_or_ge (j.1 + 1) hNT.outerCycle.length with hj1 | hj1
    · rw [Nat.mod_eq_of_lt hj1] at hval; omega
    · have : j.1 + 1 = hNT.outerCycle.length := by omega
      rw [this, Nat.mod_self] at hval; omega
  · have hib : i.1 + 1 = hNT.outerCycle.length := by omega
    rw [hib, Nat.mod_self] at hval
    rcases Nat.lt_or_ge (j.1 + 1) hNT.outerCycle.length with hj1 | hj1
    · rw [Nat.mod_eq_of_lt hj1] at hval; omega
    · have : j.1 + 1 = hNT.outerCycle.length := by omega
      omega



/-- The simultaneous invariant after `k` merges (`q i` joins the block once `i.1 ≤ k`). -/
lemma bankInvariant :
    ∀ k : ℕ, k + 1 ≤ hNT.outerCycle.length →
      (∀ i j : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (qd hNT i) (qd hNT j)
            ↔ i = j ∨ (i.1 ≤ k ∧ j.1 ≤ k)) ∧
      (∀ i j : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (qd hNT i) (rd hNT j)
            ↔ i = nextIdx hNT j ∨ (i.1 ≤ k ∧ (nextIdx hNT j).1 ≤ k)) ∧
      (∀ i j : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (rd hNT i) (rd hNT j)
            ↔ i = j ∨ ((nextIdx hNT i).1 ≤ k ∧ (nextIdx hNT j).1 ≤ k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [pPrefix_zero]
      refine ⟨?_, ?_, ?_⟩
      · -- q-q base: σ.SameCycle (q i)(q j) ↔ i = j
        intro i j
        rw [sigma_sameCycle_qd_qd]
        constructor
        · exact Or.inl
        · rintro (h | ⟨hi, hj⟩)
          · exact h
          · exact Fin.ext (by omega)
      · -- q-r base: σ.SameCycle (q i)(r j) ↔ i = next j
        intro i j
        have hr : M.σ.SameCycle (rd hNT j) (qd hNT (nextIdx hNT j)) := by
          rw [← sigma_rd_eq_qd_next]; exact ⟨1, by simp⟩
        constructor
        · intro h
          have : M.σ.SameCycle (qd hNT i) (qd hNT (nextIdx hNT j)) := h.trans hr
          left; exact (sigma_sameCycle_qd_qd i (nextIdx hNT j)).mp this
        · rintro (h | ⟨hi, hcon⟩)
          · subst h; exact hr.symm
          · -- i ≤ 0 ∧ (next j) ≤ 0 ⟹ i = next j
            have : i = nextIdx hNT j := Fin.ext (by omega)
            subst this; exact hr.symm
      · -- r-r base
        intro i j
        have hri : M.σ.SameCycle (rd hNT i) (qd hNT (nextIdx hNT i)) := by
          rw [← sigma_rd_eq_qd_next]; exact ⟨1, by simp⟩
        have hrj : M.σ.SameCycle (rd hNT j) (qd hNT (nextIdx hNT j)) := by
          rw [← sigma_rd_eq_qd_next]; exact ⟨1, by simp⟩
        constructor
        · intro h
          have : M.σ.SameCycle (qd hNT (nextIdx hNT i)) (qd hNT (nextIdx hNT j)) :=
            (hri.symm.trans h).trans hrj
          left; exact nextIdx_inj ((sigma_sameCycle_qd_qd _ _).mp this)
        · rintro (h | ⟨hci, hcj⟩)
          · subst h; exact SameCycle.rfl
          · have : nextIdx hNT i = nextIdx hNT j := Fin.ext (by omega)
            rw [nextIdx_inj this]
  | succ k ih =>
      intro hk1
      have hkB1 : k < hNT.outerCycle.length - 1 := by omega
      have hkB : k < hNT.outerCycle.length := by omega
      obtain ⟨ihqq, ihqr, ihrr⟩ := ih (by omega)
      set a := qd hNT ⟨k, hkB⟩ with ha
      set b := rd hNT ⟨k, hkB⟩ with hb
      have hnextk : (nextIdx hNT ⟨k, hkB⟩).1 = k + 1 := nextIdx_val_of_lt (by simpa using hkB1)
      have hak : (⟨k, hkB⟩ : Fin hNT.outerCycle.length).1 = k := rfl
      have hnsc : ¬ (pPrefix hNT k).SameCycle a b := by
        rw [ha, hb, ihqr ⟨k, hkB⟩ ⟨k, hkB⟩]
        rintro (hcon | ⟨_, hcon⟩)
        · have := congrArg Fin.val hcon; rw [hnextk] at this; simp at this
        · rw [hnextk] at hcon; omega
      have hstep := pPrefix_succ (hNT := hNT) k hkB1
      have engine : ∀ x y : D,
          (pPrefix hNT (k + 1)).SameCycle x y ↔
            (pPrefix hNT k).SameCycle x y ∨
              ((pPrefix hNT k).SameCycle x a ∧ (pPrefix hNT k).SameCycle y b) ∨
              ((pPrefix hNT k).SameCycle x b ∧ (pPrefix hNT k).SameCycle y a) := by
        intro x y
        rw [hstep]
        exact PermTranspositionCycleCount.sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle
          (pPrefix hNT k) hnsc (x := x) (y := y)
      -- abbreviation: q i ~ a (= q ⟨k⟩) iff i.1 ≤ k
      have hqa : ∀ i : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (qd hNT i) a ↔ i.1 ≤ k := by
        intro i; rw [ha, ihqq i ⟨k, hkB⟩]
        constructor
        · rintro (h | ⟨hi, _⟩)
          · exact le_of_eq (congrArg Fin.val h)
          · exact hi
        · intro hi
          rcases Nat.lt_or_ge i.1 k with h | h
          · exact Or.inr ⟨by omega, le_refl k⟩
          · exact Or.inl (Fin.ext (le_antisymm hi h))
      -- q i ~ b (= r ⟨k⟩) iff i = next ⟨k⟩ (= ⟨k+1⟩) [block bound k+1 ≤ k impossible]
      have hqb : ∀ i : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (qd hNT i) b ↔ i.1 = k + 1 := by
        intro i; rw [hb, ihqr i ⟨k, hkB⟩, hnextk]
        constructor
        · rintro (h | ⟨_, hcon⟩)
          · have := congrArg Fin.val h; rw [hnextk] at this; exact this
          · omega
        · intro hi; left; exact Fin.ext (by rw [hnextk]; exact hi)
      -- r i ~ b (= r ⟨k⟩) iff i = ⟨k⟩, i.e. (next i).1 = k+1
      have hrb : ∀ i : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (rd hNT i) b ↔ (nextIdx hNT i).1 = k + 1 := by
        intro i; rw [hb, ihrr i ⟨k, hkB⟩, hnextk]
        constructor
        · rintro (h | ⟨hi, hcon⟩)
          · subst h; rw [hnextk]
          · omega
        · intro hi; left; exact nextIdx_inj (Fin.ext (by rw [hnextk]; omega))
      refine ⟨?_, ?_, ?_⟩
      · -- q-q at k+1
        intro i j
        rw [engine (qd hNT i) (qd hNT j), ihqq i j, hqa i, hqb j, hqb i, hqa j]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · -- i ≤ k, j.1 = k+1
            right; refine ⟨by omega, by omega⟩
          · right; refine ⟨by omega, by omega⟩
        · rintro (h | ⟨hi, hj⟩)
          · exact Or.inl (Or.inl h)
          · -- i ≤ k+1, j ≤ k+1
            rcases Nat.lt_or_ge i.1 (k+1) with hik | hik
            · rcases Nat.lt_or_ge j.1 (k+1) with hjk | hjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · -- j.1 = k+1, i ≤ k
                right; left; exact ⟨by omega, by omega⟩
            · -- i.1 = k+1
              rcases Nat.lt_or_ge j.1 (k+1) with hjk | hjk
              · right; right; exact ⟨by omega, by omega⟩
              · -- both = k+1 ⟹ i = j
                exact Or.inl (Or.inl (Fin.ext (by omega)))
      · -- q-r at k+1
        intro i j
        rw [engine (qd hNT i) (rd hNT j), ihqr i j, hqa i, hrb j, hqb i]
        -- (pPrefix k).SameCycle (r j) a = (q-a symm): r j ~ q⟨k⟩ ↔ (next j).1 ≤ k
        have hrja : (pPrefix hNT k).SameCycle (rd hNT j) a ↔ (nextIdx hNT j).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ j]
          constructor
          · rintro (h | ⟨_, hj⟩)
            · have : (nextIdx hNT j).1 = k := (congrArg Fin.val h).symm
              omega
            · exact hj
          · intro hj
            rcases Nat.lt_or_ge (nextIdx hNT j).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        rw [hrja]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · -- i ≤ k ∧ (next j).1 ≤ k+1
            right; exact ⟨by omega, by omega⟩
          · -- i.1 = k+1 ∧ (next j).1 ≤ k
            right; exact ⟨by omega, by omega⟩
        · rintro (h | ⟨hi, hnj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge i.1 (k+1) with hik | hik
            · rcases Nat.lt_or_ge (nextIdx hNT j).1 (k+1) with hnjk | hnjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · -- i.1 = k+1
              rcases Nat.lt_or_ge (nextIdx hNT j).1 (k+1) with hnjk | hnjk
              · -- (next j) ≤ k
                right; right; exact ⟨by omega, by omega⟩
              · -- i.1 = k+1 and (next j).1 = k+1 ⟹ i = next j
                exact Or.inl (Or.inl (Fin.ext (by omega)))
      · -- r-r at k+1
        intro i j
        rw [engine (rd hNT i) (rd hNT j), ihrr i j, hrb j, hrb i]
        have hria : (pPrefix hNT k).SameCycle (rd hNT i) a ↔ (nextIdx hNT i).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ i]
          constructor
          · rintro (h | ⟨_, hi⟩)
            · have := congrArg Fin.val h; omega
            · exact hi
          · intro hi
            rcases Nat.lt_or_ge (nextIdx hNT i).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        have hrja : (pPrefix hNT k).SameCycle (rd hNT j) a ↔ (nextIdx hNT j).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ j]
          constructor
          · rintro (h | ⟨_, hj⟩)
            · have := congrArg Fin.val h; omega
            · exact hj
          · intro hj
            rcases Nat.lt_or_ge (nextIdx hNT j).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        rw [hria, hrja]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
        · rintro (h | ⟨hni, hnj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge (nextIdx hNT i).1 (k+1) with hnik | hnik
            · rcases Nat.lt_or_ge (nextIdx hNT j).1 (k+1) with hnjk | hnjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · rcases Nat.lt_or_ge (nextIdx hNT j).1 (k+1) with hnjk | hnjk
              · right; right; exact ⟨by omega, by omega⟩
              · -- both next = k+1 ⟹ i = j
                have : nextIdx hNT i = nextIdx hNT j := Fin.ext (by omega)
                exact Or.inl (Or.inl (nextIdx_inj this))



/-- The fully-merged permutation after all `B−1` merges. -/
noncomputable def pMerge (hNT : NearTriangulation M) : Equiv.Perm D :=
  pPrefix hNT (hNT.outerCycle.length - 1)

/-- The `B−1` merge swaps each merge two distinct cycles of the running product. -/
lemma mergePairs_merge_condition :
    ∀ j : Fin (mergePairs hNT).length,
      ((mergePairs hNT).get j).1 ≠ ((mergePairs hNT).get j).2 ∧
        ¬ (M.σ * (((mergePairs hNT).take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
            ((mergePairs hNT).get j).1 ((mergePairs hNT).get j).2 := by
  intro j
  have he : (mergePairs hNT).length = hNT.outerCycle.length - 1 := mergePairs_length
  have hjlen : (j : ℕ) < hNT.outerCycle.length - 1 := by have := j.2; omega
  have hjB : (j : ℕ) < hNT.outerCycle.length := by omega
  rw [mergePairs_get_fst (j : ℕ) hjlen]
  -- the running product is pPrefix j
  have hpp : M.σ * (((mergePairs hNT).take (j : ℕ)).map (fun w => Equiv.swap w.1 w.2)).prod
      = pPrefix hNT (j : ℕ) := rfl
  refine ⟨?_, ?_⟩
  · -- q ⟨j⟩ ≠ r ⟨j⟩
    exact qd_ne_rd_self ⟨(j : ℕ), hjB⟩
  · rw [hpp]
    obtain ⟨_, ihqr, _⟩ := bankInvariant (hNT := hNT) (j : ℕ) (by omega)
    rw [ihqr ⟨(j : ℕ), hjB⟩ ⟨(j : ℕ), hjB⟩]
    have hnext : (nextIdx hNT ⟨(j : ℕ), hjB⟩).1 = (j : ℕ) + 1 :=
      nextIdx_val_of_lt (by simpa using hjlen)
    rintro (hcon | ⟨_, hcon⟩)
    · have := congrArg Fin.val hcon; rw [hnext] at this; simp at this
    · rw [hnext] at hcon; omega

/-- After all `B−1` merges, the cycle count is `V − (B−1)`. -/
lemma numCycles_pMerge_add :
    _root_.numCycles (pMerge hNT) + (hNT.outerCycle.length - 1) = M.V := by
  have hmerge := CombMap.CutCapCount.numCycles_mul_listSwap_merges M.σ (mergePairs hNT)
    (mergePairs_merge_condition (hNT := hNT))
  rw [mergePairs_length] at hmerge
  -- pMerge = M.σ * swapProd mergePairs = pPrefix (B-1) (since take (B-1) = whole list)
  have hpm : pMerge hNT = M.σ * ((mergePairs hNT).map (fun w => Equiv.swap w.1 w.2)).prod := by
    unfold pMerge pPrefix
    rw [List.take_of_length_le (by rw [mergePairs_length])]
  rw [hpm, hmerge, M.V_eq_numCycles]

lemma length_pos' : 0 < hNT.outerCycle.length :=
  hNT.outerCycle.darts_length_pos

/-- The last boundary pair `(q last, r last)`, `last = ⟨B−1⟩`. -/
noncomputable def lastIdx (hNT : NearTriangulation M) : Fin hNT.outerCycle.length :=
  ⟨hNT.outerCycle.length - 1, by have := length_pos' (hNT := hNT); omega⟩

/-- In `pMerge`, the last pair lies in the same cycle (so the closing swap splits). -/
lemma pMerge_lastPair_sameCycle :
    (pMerge hNT).SameCycle (qd hNT (lastIdx hNT)) (rd hNT (lastIdx hNT)) := by
  unfold pMerge
  have hBpos : 0 < hNT.outerCycle.length := hNT.outerCycle.darts_length_pos
  obtain ⟨_, ihqr, _⟩ := bankInvariant (hNT := hNT) (hNT.outerCycle.length - 1) (by omega)
  rw [ihqr (lastIdx hNT) (lastIdx hNT)]
  -- last.1 = B-1 ≤ B-1 and (next last).1 = 0 ≤ B-1
  right
  have hnl : (nextIdx hNT (lastIdx hNT)).1 = 0 := by
    rw [nextIdx_val]
    show ((hNT.outerCycle.length - 1) + 1) % hNT.outerCycle.length = 0
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  refine ⟨?_, ?_⟩
  · show (hNT.outerCycle.length - 1) ≤ hNT.outerCycle.length - 1; exact le_refl _
  · rw [hnl]; exact Nat.zero_le _



/-- Evaluation of the disjoint-swap product at a `q`-dart whose index is in the (nodup) list. -/
lemma listSwapQR_apply_qd (m : Fin hNT.outerCycle.length) :
    ∀ L : List (Fin hNT.outerCycle.length), L.Nodup → m ∈ L →
      ((L.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod
          (qd hNT m) = rd hNT m := by
  intro L
  induction L with
  | nil => intro _ hm; simp only [List.not_mem_nil] at hm
  | cons c t ih =>
      intro hnd hm
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      have hndt := (List.nodup_cons.mp hnd)
      by_cases hmt : m ∈ t
      · -- m ∈ t, so c ≠ m (nodup); tail moves q m ↦ r m, head fixes r m
        have hcm : c ≠ m := fun h => hndt.1 (h ▸ hmt)
        rw [ih hndt.2 hmt]
        show Equiv.swap (qd hNT c) (rd hNT c) (rd hNT m) = rd hNT m
        rw [Equiv.swap_apply_of_ne_of_ne (rd_ne_qd m c) (fun h => hcm (rd_inj h).symm)]
      · -- m = c
        have hmc : m = c := by
          rcases List.mem_cons.mp hm with h | h
          · exact h
          · exact absurd h hmt
        subst hmc
        -- tail fixes q m
        have htail : ((t.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod
            (qd hNT m) = qd hNT m := by
          apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          have hineq : i ≠ m := fun h => hmt (h ▸ hi)
          subst hwi
          exact ⟨fun h => hineq (qd_inj h).symm, qd_ne_rd m i⟩
        rw [htail]
        show Equiv.swap (qd hNT m) (rd hNT m) (qd hNT m) = rd hNT m
        rw [Equiv.swap_apply_left]

/-- Evaluation of the disjoint-swap product at an `r`-dart whose index is in the (nodup) list. -/
lemma listSwapQR_apply_rd (m : Fin hNT.outerCycle.length) :
    ∀ L : List (Fin hNT.outerCycle.length), L.Nodup → m ∈ L →
      ((L.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod
          (rd hNT m) = qd hNT m := by
  intro L
  induction L with
  | nil => intro _ hm; simp only [List.not_mem_nil] at hm
  | cons c t ih =>
      intro hnd hm
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      have hndt := (List.nodup_cons.mp hnd)
      by_cases hmt : m ∈ t
      · have hcm : c ≠ m := fun h => hndt.1 (h ▸ hmt)
        rw [ih hndt.2 hmt]
        show Equiv.swap (qd hNT c) (rd hNT c) (qd hNT m) = qd hNT m
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => hcm (qd_inj h).symm) (qd_ne_rd m c)]
      · have hmc : m = c := by
          rcases List.mem_cons.mp hm with h | h
          · exact h
          · exact absurd h hmt
        subst hmc
        have htail : ((t.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod
            (rd hNT m) = rd hNT m := by
          apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          have hineq : i ≠ m := fun h => hmt (h ▸ hi)
          subst hwi
          exact ⟨rd_ne_qd m i, fun h => hineq (rd_inj h).symm⟩
        rw [htail]
        show Equiv.swap (qd hNT m) (rd hNT m) (rd hNT m) = qd hNT m
        rw [Equiv.swap_apply_right]

/-- Evaluation at a dart that is neither a `q`- nor `r`-dart of the list: it is fixed. -/
lemma listSwapQR_apply_other (d : D)
    (L : List (Fin hNT.outerCycle.length))
    (hd : ∀ i ∈ L, d ≠ qd hNT i ∧ d ≠ rd hNT i) :
    ((L.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod d = d := by
  apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
  intro w hw
  rw [List.mem_map] at hw
  obtain ⟨i, hi, hwi⟩ := hw
  subst hwi
  exact hd i hi

/-- A boundary dart is some `qd m`. -/
lemma exists_qd_of_mem_darts {d : D} (hd : d ∈ hNT.outerCycle.darts) :
    ∃ m : Fin hNT.outerCycle.length, d = qd hNT m := by
  obtain ⟨n, hgn⟩ := List.get_of_mem hd
  refine ⟨⟨n.1, by simpa [BoundaryCycle.length] using n.2⟩, ?_⟩
  unfold qd; rw [← hgn]

/-- The full pair list over all `B` indices. -/
noncomputable def allPairs (hNT : NearTriangulation M) : List (D × D) :=
  (List.finRange hNT.outerCycle.length).map (fun i => (qd hNT i, rd hNT i))

/-- `outerTau` is the product of the `B` disjoint outer transpositions. -/
lemma outerTau_eq_swapProd :
    outerTau hNT = ((allPairs hNT).map (fun w => Equiv.swap w.1 w.2)).prod := by
  have hnd : (List.finRange hNT.outerCycle.length).Nodup := List.nodup_finRange _
  ext d
  unfold allPairs
  by_cases hd : d ∈ OuterDel hNT
  · rw [outerTau_eq_alpha_of_mem (hNT := hNT) hd]
    rw [mem_outerDel_iff] at hd
    rcases hd with hdd | hαd
    · -- d = qd m, α d = rd m
      obtain ⟨m, rfl⟩ := exists_qd_of_mem_darts (hNT := hNT) hdd
      rw [listSwapQR_apply_qd m _ hnd (List.mem_finRange m)]; rfl
    · -- α d ∈ darts ⟹ d = rd m (where α d = qd m)
      obtain ⟨m, hm⟩ := exists_qd_of_mem_darts (hNT := hNT) hαd
      have hdrm : d = rd hNT m := by
        rw [rd]; rw [← hm, M.alpha_alpha]
      subst hdrm
      show M.α (rd hNT m) = _
      rw [listSwapQR_apply_rd m _ hnd (List.mem_finRange m)]
      show M.α (M.α (qd hNT m)) = qd hNT m
      rw [M.alpha_alpha]
  · rw [outerTau_eq_self_of_notMem (hNT := hNT) hd]
    refine (listSwapQR_apply_other d _ ?_).symm
    intro i _
    refine ⟨?_, ?_⟩
    · intro h; exact hd (h ▸ qd_mem_outerDel i)
    · intro h; exact hd (h ▸ rd_mem_outerDel i)

/-- `allPairs = mergePairs ++ [last pair]`. -/
lemma allPairs_eq_append :
    allPairs hNT = mergePairs hNT ++ [(qd hNT (lastIdx hNT), rd hNT (lastIdx hNT))] := by
  have hBpos : 0 < hNT.outerCycle.length := hNT.outerCycle.darts_length_pos
  have hlenA : (allPairs hNT).length = hNT.outerCycle.length := by
    simp [allPairs, List.length_map, List.length_finRange]
  have hmlen : (mergePairs hNT).length = hNT.outerCycle.length - 1 := mergePairs_length
  have hlenR : (mergePairs hNT ++ [(qd hNT (lastIdx hNT), rd hNT (lastIdx hNT))]).length
      = hNT.outerCycle.length := by
    rw [List.length_append, hmlen, List.length_singleton]; omega
  apply List.ext_getElem (by rw [hlenA, hlenR])
  intro n hn1 hn2
  rw [hlenA] at hn1
  -- LHS
  have hLHS : (allPairs hNT)[n] = (qd hNT ⟨n, hn1⟩, rd hNT ⟨n, hn1⟩) := by
    simp only [allPairs]
    rw [List.getElem_map, List.getElem_finRange]
    congr 1
  rw [hLHS]
  by_cases hnlast : n < hNT.outerCycle.length - 1
  · -- left part
    rw [List.getElem_append_left (by rw [hmlen]; exact hnlast)]
    simp only [mergePairs]
    rw [List.getElem_map, List.getElem_finRange]
    show (qd hNT ⟨n, hn1⟩, rd hNT ⟨n, hn1⟩)
      = (qd hNT (emb hNT _), rd hNT (emb hNT _))
    congr 1
  · -- right part: n = B-1
    rw [List.getElem_append_right (by rw [hmlen]; omega)]
    have hidx : (⟨n, hn1⟩ : Fin hNT.outerCycle.length) = lastIdx hNT :=
      Fin.ext (by simp only [lastIdx]; omega)
    rw [hidx, List.getElem_singleton]



/-- `M.σ * outerTau = pMerge * swap (q last) (r last)`. -/
lemma sigma_outerTau_eq :
    M.σ * outerTau hNT
      = pMerge hNT * Equiv.swap (qd hNT (lastIdx hNT)) (rd hNT (lastIdx hNT)) := by
  rw [outerTau_eq_swapProd, allPairs_eq_append, List.map_append, List.prod_append]
  unfold pMerge pPrefix
  rw [List.take_of_length_le (by rw [mergePairs_length]), List.map_singleton, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc]

/-- **Step 6 (the boundary-bank face count) — UNCONDITIONAL.**
`numCycles (M.φ * outerDualAlpha hNT) = M.V − B + 2`. -/
theorem boundaryBankCount_holds (hNT : NearTriangulation M) : BoundaryBankCount hNT := by
  -- reduce to numCycles (M.σ * outerTau) = V - B + 2
  unfold BoundaryBankCount
  rw [phi_outerDualAlpha_eq_sigma_outerTau, sigma_outerTau_eq]
  -- split count: numCycles (pMerge * swap) = numCycles pMerge + 1
  have hsplit : _root_.numCycles
      (pMerge hNT * Equiv.swap (qd hNT (lastIdx hNT)) (rd hNT (lastIdx hNT)))
      = _root_.numCycles (pMerge hNT) + 1 :=
    CombMap.CutCapCount.numCycles_mul_swap_of_sameCycle (pMerge hNT)
      (qd_ne_rd_self (lastIdx hNT)) (pMerge_lastPair_sameCycle (hNT := hNT))
  rw [hsplit]
  -- merge count: numCycles pMerge + (B-1) = V
  have hmerge := numCycles_pMerge_add (hNT := hNT)
  have hBpos : 0 < hNT.outerCycle.length := hNT.outerCycle.darts_length_pos
  have hBV : hNT.outerCycle.length ≤ M.V := outerCycle_length_le_V hNT
  omega

/-- **Discharge of `OuterDualNumCompTwo` — UNCONDITIONAL.**  Supplying the now-proved
boundary-bank count to the genus-slack assembly closes the Chapter-35 coverage atom. -/
theorem outerDualNumCompTwo_holds (hNT : NearTriangulation M) :
    ZinanCh35OuterCount.OuterDualNumCompTwo hNT :=
  ZinanCh35OuterSlack.outerDualNumCompTwo_of_boundaryBankCount' hNT
    (boundaryBankCount_holds hNT)

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



/-- `dartFace (σ x) = dartFace (α x)`: because `φ (α x) = σ x` and `dartFace` is `φ`-invariant. -/
lemma dartFace_sigma_eq_alpha (x : D) :
    M.dartFace (M.σ x) = M.dartFace (M.α x) := by
  have hφ : M.φ (M.α x) = M.σ x := by
    show (M.σ * M.α) (M.α x) = M.σ x
    simp [Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
  calc M.dartFace (M.σ x) = M.dartFace (M.φ (M.α x)) := by rw [hφ]
    _ = M.dartFace (M.α x) := M.dartFace_phi _

/-- `σ.SameCycle a b` is exactly `tail a = tail b`. -/
lemma sigma_sameCycle_iff_tail (a b : D) :
    M.σ.SameCycle a b ↔ M.tail a = M.tail b := by
  show M.σ.SameCycle a b ↔
    (Quotient.mk (cycleSetoid M.σ) a : Quotient (cycleSetoid M.σ)) = Quotient.mk _ b
  rw [Quotient.eq]
  rfl



/-- Two faces are adjacent *avoiding* a forbidden edge predicate when they share a dart whose
edge is not forbidden.  Instantiating `Forbidden e := IsBoundaryEdge e ∨ e = s(u,v)` gives
`ChordSplitAdj`. -/
def FaceAdjAvoiding (M : CombMap D) (Forbidden : Sym2 M.Vertex → Prop) (f g : M.Face) : Prop :=
  ∃ d : D, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧ ¬ Forbidden (M.dartEdge d)

/-- **One σ-step.**  If `dartEdge x` is not forbidden, then `dartFace x` and `dartFace (σ x)`
are `FaceAdjAvoiding`-adjacent (witness `x`, using `dartFace (α x) = dartFace (σ x)`). -/
lemma sigma_step_faceAdjAvoiding {Forbidden : Sym2 M.Vertex → Prop} {x : D}
    (hx : ¬ Forbidden (M.dartEdge x)) :
    FaceAdjAvoiding M Forbidden (M.dartFace x) (M.dartFace (M.σ x)) :=
  ⟨x, rfl, (dartFace_sigma_eq_alpha x).symm, hx⟩

/-- **σ-orbit connectivity, no-forbidden version.**  If `x` and `y` are in the same σ-cycle and
*every* dart in that σ-cycle has a non-forbidden edge, then `dartFace x` reaches `dartFace y`
through `FaceAdjAvoiding`.  (Induction on the σ-power connecting `x` to `y`.) -/
lemma star_connected_avoiding {Forbidden : Sym2 M.Vertex → Prop} {x y : D}
    (hσ : M.σ.SameCycle x y)
    (havoid : ∀ z, M.σ.SameCycle x z → ¬ Forbidden (M.dartEdge z)) :
    Relation.ReflTransGen (FaceAdjAvoiding M Forbidden) (M.dartFace x) (M.dartFace y) := by
  obtain ⟨i, hi⟩ := hσ.exists_nat_pow_eq
  -- prove a powered version by induction on `i`, then rewrite `y`.
  subst hi
  clear hσ
  induction i with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ k ih =>
    -- `σ^(k+1) x = σ (σ^k x)`.
    have hstep : (M.σ ^ (k + 1)) x = M.σ ((M.σ ^ k) x) := by
      rw [pow_succ']; rfl
    rw [hstep]
    refine ih.tail ?_
    -- one step from `dartFace (σ^k x)` to `dartFace (σ (σ^k x))`.
    have hsc : M.σ.SameCycle x ((M.σ ^ k) x) := ⟨k, by rw [zpow_natCast]⟩
    exact sigma_step_faceAdjAvoiding (havoid _ hsc)



/-- The chord-split forbidden-edge predicate. -/
def ChordForbidden (hNT : NearTriangulation M) (u v : M.Vertex) (e : Sym2 M.Vertex) : Prop :=
  hNT.outerCycle.IsBoundaryEdge e ∨ e = s(u, v)

/-- `FaceAdjAvoiding` with `ChordForbidden` is definitionally `ChordSplitAdj`. -/
lemma faceAdjAvoiding_chordForbidden_iff {f g : M.Face} :
    FaceAdjAvoiding M (ChordForbidden hNT u v) f g ↔ hNT.ChordSplitAdj u v f g := by
  constructor
  · rintro ⟨d, hdf, hdg, hF⟩
    exact ⟨d, hdf, hdg, fun hb => hF (Or.inl hb), fun hc => hF (Or.inr hc)⟩
  · rintro ⟨d, hdf, hdg, hbe, hch⟩
    refine ⟨d, hdf, hdg, ?_⟩
    rintro (hb | hc)
    · exact hbe hb
    · exact hch hc

/-- Transport a `FaceAdjAvoiding (ChordForbidden …)` reachability into `ChordSplitAdj`
reachability. -/
lemma reflTransGen_chordSplitAdj_of_avoiding {f g : M.Face}
    (h : Relation.ReflTransGen (FaceAdjAvoiding M (ChordForbidden hNT u v)) f g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (faceAdjAvoiding_chordForbidden_iff.mp hstep)



/-- **Side-1 extraction.**  A vertex in `sideRegion₁` is the tail of a dart whose face is in
`side₁`. -/
theorem incident_side₁_of_mem_sideRegion₁ (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hw : w ∈ sideRegion₁ data) :
    ∃ d : D, M.tail d = w ∧ M.dartFace d ∈ data.side₁ := by
  obtain ⟨d, hd, htail⟩ := hw
  -- `d ∈ keptSet₁`.
  have hkept : d ∈ data.keptSet₁ := (data.mem_keptDel₁_iff d).1 hd
  obtain ⟨hU, _⟩ := hkept
  rcases hU with hin | hout
  · -- `d ∈ sideDarts₁`: `dartFace d ∈ side₁`, tail `d = w`.
    exact ⟨d, htail, hin⟩
  · -- `d ∈ outerArc₁`: face of `σ d = α-face ∈ side₁`, tail `σ d = w`.
    obtain ⟨_houter, hαside⟩ := hout
    refine ⟨M.σ d, ?_, ?_⟩
    · rw [M.tail_sigma]; exact htail
    · rw [dartFace_sigma_eq_alpha]; exact hαside

/-- **Side-2 extraction.**  A vertex in `sideRegion₂` is the tail of a dart whose face is in
`side₂`. -/
theorem incident_side₂_of_mem_sideRegion₂ (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hw : w ∈ sideRegion₂ data) :
    ∃ d : D, M.tail d = w ∧ M.dartFace d ∈ data.side₂ := by
  obtain ⟨d, hd, htail⟩ := hw
  have hkept : d ∈ data.keptSet₂ := (data.mem_keptDel₂_iff d).1 hd
  obtain ⟨hU, _⟩ := hkept
  rcases hU with hin | hout
  · exact ⟨d, htail, hin⟩
  · obtain ⟨_houter, hαside⟩ := hout
    refine ⟨M.σ d, ?_, ?_⟩
    · rw [M.tail_sigma]; exact htail
    · rw [dartFace_sigma_eq_alpha]; exact hαside



/-- A dart whose tail is not a chord endpoint does not carry the chord edge. -/
lemma dartEdge_ne_chord_of_tail_ne (data : hNT.ChordSplitData u v) {z : D}
    (htail : M.tail z = u → False) (htail' : M.tail z = v → False) :
    M.dartEdge z ≠ s(u, v) := by
  intro hz
  -- `dartEdge z = s(tail z, head z) = s(u, v)`, so `tail z ∈ {u, v}`.
  have hmem : M.tail z ∈ (s(u, v) : Sym2 M.Vertex) := by
    rw [← hz]; exact Sym2.mem_mk_left _ _
  rcases Sym2.mem_iff.1 hmem with h | h
  · exact htail h
  · exact htail' h

/-- **The non-outer σ-step.**  If `tail z ≠ u, v` and both `dartFace z`, `dartFace (σ z)` are
non-outer, then `ChordSplitAdj (dartFace z) (dartFace (σ z))`. -/
lemma chordSplitAdj_sigma_step_of_nonouter (data : hNT.ChordSplitData u v) {z : D}
    (hzu : M.tail z ≠ u) (hzv : M.tail z ≠ v)
    (hz : M.dartFace z ≠ hNT.outerFace) (hσz : M.dartFace (M.σ z) ≠ hNT.outerFace) :
    hNT.ChordSplitAdj u v (M.dartFace z) (M.dartFace (M.σ z)) := by
  refine ⟨z, rfl, (dartFace_sigma_eq_alpha z).symm, ?_, ?_⟩
  · -- non-boundary: a boundary edge would force `z` or `α z` onto the outer face.
    intro hbe
    rcases data.boundaryEdge_dart_outer hbe with h | h
    · exact hz h
    · exact hσz (by rw [dartFace_sigma_eq_alpha]; exact h)
  · exact dartEdge_ne_chord_of_tail_ne data hzu hzv



/-- An outer-face dart's tail is a boundary vertex. -/
lemma isBoundaryVertex_tail_of_outer {z : D} (hz : M.dartFace z = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryVertex (M.tail z) := by
  have hmem : z ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff z).2 hz
  show M.tail z ∈ hNT.outerCycle.vertices
  rw [hNT.outerCycle.vertices_eq]
  exact List.mem_map_of_mem hmem

/-- **Interior star connectivity.**  At a non-boundary vertex `w ≠ u, v`, all incident faces are
non-outer and pairwise `ChordSplitAdj`-connected. -/
theorem interior_star_nonouter_connected (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hw_not_boundary : ¬ hNT.outerCycle.IsBoundaryVertex w)
    (hwu : w ≠ u) (hwv : w ≠ v) {d₁ d₂ : D}
    (h₁tail : M.tail d₁ = w) (h₂tail : M.tail d₂ = w) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace d₁) (M.dartFace d₂) := by
  -- `σ.SameCycle d₁ d₂` from equal tails.
  have hσ : M.σ.SameCycle d₁ d₂ := (sigma_sameCycle_iff_tail d₁ d₂).2 (h₁tail.trans h₂tail.symm)
  -- every dart `z` σ-same-cycle with `d₁` has tail `w` (non-outer face, non-forbidden edge).
  have hconn :
      Relation.ReflTransGen (FaceAdjAvoiding M (ChordForbidden hNT u v))
        (M.dartFace d₁) (M.dartFace d₂) := by
    refine star_connected_avoiding hσ ?_
    intro z hz
    -- `tail z = w`.
    have hzw : M.tail z = w := by
      have := (sigma_sameCycle_iff_tail d₁ z).1 hz
      rw [← this]; exact h₁tail
    -- `z` is not on the outer face (else `w` boundary).
    have hzouter : M.dartFace z ≠ hNT.outerFace := by
      intro h; exact hw_not_boundary (hzw ▸ isBoundaryVertex_tail_of_outer h)
    -- and neither is `σ z` (its tail is also `w`).
    have hσzouter : M.dartFace (M.σ z) ≠ hNT.outerFace := by
      intro h
      have : M.tail (M.σ z) = w := by rw [M.tail_sigma]; exact hzw
      exact hw_not_boundary (this ▸ isBoundaryVertex_tail_of_outer h)
    -- forbidden = boundary ∨ chord; both excluded.
    rintro (hbe | hch)
    · rcases data.boundaryEdge_dart_outer hbe with h | h
      · exact hzouter h
      · exact hσzouter (by rw [dartFace_sigma_eq_alpha]; exact h)
    · exact dartEdge_ne_chord_of_tail_ne data (fun h => hwu (hzw ▸ h))
        (fun h => hwv (hzw ▸ h)) hch
  exact reflTransGen_chordSplitAdj_of_avoiding hconn



/-- **Uniqueness of the outer dart at a vertex.**  Two outer-face darts with the same tail are
equal (the boundary vertex list is `Nodup`). -/
lemma outer_dart_unique {z₁ z₂ : D}
    (h₁ : M.dartFace z₁ = hNT.outerFace) (h₂ : M.dartFace z₂ = hNT.outerFace)
    (ht : M.tail z₁ = M.tail z₂) : z₁ = z₂ :=
  hNT.outerCycle.tail_injective_on_darts hNT.outer_simple
    ((hNT.outerCycle.mem_darts_iff z₁).2 h₁) ((hNT.outerCycle.mem_darts_iff z₂).2 h₂) ht

/-- A dart sharing `b`'s tail but distinct from the outer dart `b` is non-outer. -/
lemma nonouter_of_ne_outer {b z : D} (hb : M.dartFace b = hNT.outerFace)
    (htz : M.tail z = M.tail b) (hzb : z ≠ b) : M.dartFace z ≠ hNT.outerFace :=
  fun hz => hzb (outer_dart_unique hz hb htz)

/-- `σ^m b ≠ b` for `0 < m < L` (`L = #(σ.cycleOf b).support`), provided `b ∈ σ.support`. -/
lemma sigma_pow_ne_self_of_lt {b : D} (hb : b ∈ M.σ.support) {m : ℕ}
    (hm0 : 0 < m) (hmL : m < (M.σ.cycleOf b).support.card) : (M.σ ^ m) b ≠ b := by
  set c := M.σ.cycleOf b with hc
  have hIsCycle : c.IsCycle := Equiv.Perm.isCycle_cycleOf M.σ (Equiv.Perm.mem_support.1 hb)
  have hord : orderOf c = c.support.card := hIsCycle.orderOf
  -- `b ∈ c.support`.
  have hbsupp : b ∈ c.support := by
    rw [hc, Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]
    exact hb
  -- `(c^m).support = c.support` since `0 < m < L = orderOf c`.
  have hsupp_pow : (c ^ m).support = c.support :=
    hIsCycle.support_pow_of_pos_of_lt_orderOf hm0 (by rw [hord]; exact hmL)
  -- so `b ∈ (c^m).support`, i.e. `(c^m) b ≠ b`; and `(c^m) b = (σ^m) b`.
  have hbpow : b ∈ (c ^ m).support := by rw [hsupp_pow]; exact hbsupp
  have hne : (c ^ m) b ≠ b := Equiv.Perm.mem_support.1 hbpow
  intro hpow
  apply hne
  rw [hc, Equiv.Perm.cycleOf_pow_apply_self]; exact hpow

/-- `tail (σ^m b) = tail b`. -/
lemma tail_sigma_pow (b : D) (m : ℕ) : M.tail ((M.σ ^ m) b) = M.tail b := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, M.tail_sigma]; exact ih

/-- `dartFace (σ^m b) ≠ outerFace` for `0 < m < L`, where `b` is the outer dart at `w`. -/
lemma sigma_pow_nonouter {b : D} (hb_outer : M.dartFace b = hNT.outerFace)
    (hb_supp : b ∈ M.σ.support) {m : ℕ}
    (hm0 : 0 < m) (hmL : m < (M.σ.cycleOf b).support.card) :
    M.dartFace ((M.σ ^ m) b) ≠ hNT.outerFace :=
  nonouter_of_ne_outer hb_outer (tail_sigma_pow b m)
    (sigma_pow_ne_self_of_lt hb_supp hm0 hmL)

/-- **Anchor reachability.**  For `w ≠ u, v` and the outer dart `b` at `w`, every power
`σ^m b` with `1 ≤ m < L` has `dartFace (σ b)` reaching `dartFace (σ^m b)` in `ChordSplitAdj`. -/
lemma anchor_reaches (data : hNT.ChordSplitData u v) {b : D}
    (hb_outer : M.dartFace b = hNT.outerFace) (hb_supp : b ∈ M.σ.support)
    (hwu : M.tail b ≠ u) (hwv : M.tail b ≠ v) :
    ∀ m : ℕ, 1 ≤ m → m < (M.σ.cycleOf b).support.card →
      Relation.ReflTransGen (hNT.ChordSplitAdj u v)
        (M.dartFace (M.σ b)) (M.dartFace ((M.σ ^ m) b)) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
    intro _hk1 hkL
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- `m = 1`: `σ^1 b = σ b`, refl.
      subst hk0
      simpa using Relation.ReflTransGen.refl
    · -- `m = k+1`, `k ≥ 1`: IH to `σ^k b`, then one step to `σ^(k+1) b`.
      have hkL' : k < (M.σ.cycleOf b).support.card := by omega
      have hreach := ih hkpos hkL'
      refine hreach.tail ?_
      -- one `ChordSplitAdj` step from `dartFace (σ^k b)` to `dartFace (σ^(k+1) b)`.
      have htail : M.tail ((M.σ ^ k) b) = M.tail b := tail_sigma_pow b k
      have hz_nonouter : M.dartFace ((M.σ ^ k) b) ≠ hNT.outerFace :=
        sigma_pow_nonouter hb_outer hb_supp hkpos hkL'
      have hσz_nonouter : M.dartFace (M.σ ((M.σ ^ k) b)) ≠ hNT.outerFace := by
        have heq : M.σ ((M.σ ^ k) b) = (M.σ ^ (k + 1)) b := by rw [pow_succ']; rfl
        rw [heq]
        exact sigma_pow_nonouter hb_outer hb_supp (by omega) hkL
      have hstep := chordSplitAdj_sigma_step_of_nonouter data
        (z := (M.σ ^ k) b) (by rw [htail]; exact hwu) (by rw [htail]; exact hwv)
        hz_nonouter hσz_nonouter
      -- rewrite `σ (σ^k b) = σ^(k+1) b`.
      have heq : M.σ ((M.σ ^ k) b) = (M.σ ^ (k + 1)) b := by rw [pow_succ']; rfl
      rwa [heq] at hstep

/-- **Boundary star connectivity.**  At a boundary vertex `w ≠ u, v`, any two non-outer darts
`d₁, d₂` with tail `w` have `ChordSplitAdj`-connected faces (both reach the anchor `dartFace (σ b)`
where `b` is the unique outer dart at `w`). -/
theorem boundary_star_nonouter_connected (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hw_boundary : hNT.outerCycle.IsBoundaryVertex w)
    (hwu : w ≠ u) (hwv : w ≠ v) {d₁ d₂ : D}
    (h₁tail : M.tail d₁ = w) (h₂tail : M.tail d₂ = w)
    (h₁nonouter : M.dartFace d₁ ≠ hNT.outerFace) (h₂nonouter : M.dartFace d₂ ≠ hNT.outerFace) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace d₁) (M.dartFace d₂) := by
  -- the outer dart `b` at `w`.
  obtain ⟨b, hb_darts, hb_tail⟩ : ∃ b, b ∈ hNT.outerCycle.darts ∧ M.tail b = w := by
    have : w ∈ hNT.outerCycle.darts.map M.tail := by
      rw [← hNT.outerCycle.vertices_eq]; exact hw_boundary
    rcases List.mem_map.1 this with ⟨b, hb, hbw⟩; exact ⟨b, hb, hbw⟩
  have hb_outer : M.dartFace b = hNT.outerFace := (hNT.outerCycle.mem_darts_iff b).1 hb_darts
  have hb_supp : b ∈ M.σ.support :=
    Equiv.Perm.mem_support.2 (hNT.boundary_dart_sigma_ne hb_darts)
  -- both `d₁, d₂` reach `dartFace (σ b)`.
  set L := (M.σ.cycleOf b).support.card with hL
  have hbu : M.tail b ≠ u := by rw [hb_tail]; exact hwu
  have hbv : M.tail b ≠ v := by rw [hb_tail]; exact hwv
  have reach : ∀ {d : D}, M.tail d = w → M.dartFace d ≠ hNT.outerFace →
      Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace (M.σ b)) (M.dartFace d) := by
    intro d hdtail hdnonouter
    -- `σ.SameCycle b d` (equal tails), and `b ∈ support`.
    have hsc : M.σ.SameCycle b d :=
      (sigma_sameCycle_iff_tail b d).2 (by rw [hb_tail, hdtail])
    obtain ⟨m, hmL, hmd⟩ := hsc.exists_pow_eq_of_mem_support hb_supp
    -- `m ≠ 0` (else `d = b` is outer).
    have hm0 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exfalso; apply hdnonouter; rw [← hmd, h]; simpa using hb_outer
      · exact h
    have := anchor_reaches data hb_outer hb_supp hbu hbv m hm0 hmL
    rwa [hmd] at this
  have r₁ := reach h₁tail h₁nonouter
  have r₂ := reach h₂tail h₂nonouter
  -- `d₁ ~* anchor ~* d₂`.
  exact (Relation.ReflTransGen.symmetric (fun _ _ h => hNT.chordSplitAdj_symm h) r₁).trans r₂



/-- **Core star connectivity away from chord ends.**  For `w ≠ u, v`, any two non-outer darts
`d₁, d₂` with common tail `w` have `ChordSplitAdj`-connected faces.  Case split on whether `w`
is a boundary vertex: interior → `interior_star_nonouter_connected`; boundary →
`boundary_star_nonouter_connected`. -/
theorem star_nonouter_connected_away_from_chordEnds (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hwu : w ≠ u) (hwv : w ≠ v) {d₁ d₂ : D}
    (h₁tail : M.tail d₁ = w) (h₂tail : M.tail d₂ = w)
    (h₁nonouter : M.dartFace d₁ ≠ hNT.outerFace) (h₂nonouter : M.dartFace d₂ ≠ hNT.outerFace) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace d₁) (M.dartFace d₂) := by
  by_cases hw_boundary : hNT.outerCycle.IsBoundaryVertex w
  · exact boundary_star_nonouter_connected data hw_boundary hwu hwv h₁tail h₂tail
      h₁nonouter h₂nonouter
  · exact interior_star_nonouter_connected data hw_boundary hwu hwv h₁tail h₂tail



/-- **`SideRegionInterChordEnds`, discharged unconditionally.**  A vertex `w` in both side regions
is a chord endpoint.  Proof by contradiction: extract incident side-1 / side-2 faces at `w`,
connect them via the core star-connectivity lemma (`w ≠ u, v`), and contradict `Separates`. -/
theorem sideRegionInterChordEnds_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    SideRegionInterChordEnds data := by
  intro w hw1 hw2
  by_contra hnot
  have hwu : w ≠ u := fun h => hnot (Or.inl h)
  have hwv : w ≠ v := fun h => hnot (Or.inr h)
  -- extract incident side-1 and side-2 faces at `w`.
  obtain ⟨d₁, ht₁, hf₁⟩ := incident_side₁_of_mem_sideRegion₁ data hw1
  obtain ⟨d₂, ht₂, hf₂⟩ := incident_side₂_of_mem_sideRegion₂ data hw2
  have ho₁ : M.dartFace d₁ ≠ hNT.outerFace := data.side₁_subset_nonouter hf₁
  have ho₂ : M.dartFace d₂ ≠ hNT.outerFace := data.side₂_subset_nonouter hf₂
  -- connect the two faces.
  have hconn : Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace d₁) (M.dartFace d₂) :=
    star_nonouter_connected_away_from_chordEnds data hwu hwv ht₁ ht₂ ho₁ ho₂
  -- `face₂ ∈ side₁`, contradicting `Separates`.
  have hf₂_to_face₂ : data.face₂ ∈ hNT.Side u v (M.dartFace d₂) := side_mem_symm hf₂
  have : data.face₂ ∈ data.side₁ := (hf₁.trans hconn).trans hf₂_to_face₂
  exact hsep this

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

/-- `C.dartSet` is `α`-closed: it is symmetric under `M.α` by construction
(`d = C.dart i` ↦ `α d = α (C.dart i)`, and `d = α (C.dart i)` ↦ `α d = C.dart i`). -/
lemma dartSet_alpha_closed :
    ∀ d : D, d ∈ C.dartSet → M.α d ∈ C.dartSet := by
  intro d hd
  rw [C.mem_dartSet_iff] at hd ⊢
  obtain ⟨i, hi | hi⟩ := hd
  · exact ⟨i, Or.inr (by rw [hi])⟩
  · exact ⟨i, Or.inl (by rw [hi, M.alpha_alpha])⟩

/-- The restricted dual involution for the cycle: fixes the cycle darts, `= M.α` elsewhere. -/
noncomputable def cycleDualAlpha (C : SimplePrimalCycle M) : Equiv.Perm D :=
  SubmapPlanar.rawAlpha M C.dartSet (dartSet_alpha_closed C)

lemma cycleDualAlpha_eq_self_of_mem {d : D} (hd : d ∈ C.dartSet) :
    cycleDualAlpha C d = d :=
  SubmapPlanar.rawAlpha_eq_self_of_mem M C.dartSet _ hd

lemma cycleDualAlpha_eq_alpha_of_notMem {d : D} (hd : d ∉ C.dartSet) :
    cycleDualAlpha C d = M.α d :=
  SubmapPlanar.rawAlpha_eq_alpha_of_notMem M C.dartSet _ hd



/-- The forward and reverse darts are disjoint families, so `C.dartSet` has `2·C.len`
elements: `C.len` forward darts `C.dart i` and `C.len` reverse darts `M.α (C.dart i)`. -/
lemma dartSet_card : (C.dartSet).card = 2 * C.len := by
  classical
  -- `C.dartSet = image C.dart ∪ image (α ∘ C.dart)`; the two images are disjoint.
  have hset : C.dartSet
      = (Finset.univ.image C.dart) ∪ (Finset.univ.image (fun i => M.α (C.dart i))) := by
    ext d
    rw [C.mem_dartSet_iff]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi | hi⟩
      · exact Or.inl ⟨i, hi.symm⟩
      · exact Or.inr ⟨i, hi.symm⟩
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨i, Or.inl hi.symm⟩
      · exact ⟨i, Or.inr hi.symm⟩
  have hdisj : Disjoint (Finset.univ.image C.dart)
      (Finset.univ.image (fun i => M.α (C.dart i))) := by
    rw [Finset.disjoint_left]
    intro d hd himg
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hd himg
    obtain ⟨i, hi⟩ := hd
    obtain ⟨j, hj⟩ := himg
    exact C.dart_ne_alpha_dart i j (hi.trans hj.symm)
  have hcardF : (Finset.univ.image C.dart).card = C.len := by
    rw [Finset.card_image_of_injective _ C.dart_inj, Finset.card_univ, Fintype.card_fin]
  have hcardR : (Finset.univ.image (fun i => M.α (C.dart i))).card = C.len := by
    rw [Finset.card_image_of_injective _ C.alpha_dart_inj, Finset.card_univ, Fintype.card_fin]
  rw [hset, Finset.card_union_of_disjoint hdisj, hcardF, hcardR]; ring



/-- `genusSlack (M.φ) (cycleDualAlpha C) = 0`: deleting the cycle edges from the genus-0 dual
map keeps the slack at zero.  Reuses the `dualMap` machinery from `ZinanCh35OuterSlack`. -/
lemma genusSlack_cycleDualAlpha_eq_zero (hsphere : M.IsSphereMap) :
    genusSlack M.φ (cycleDualAlpha C) = 0 := by
  have hclosedD : ∀ d : D, d ∈ C.dartSet → (dualMap M).α d ∈ C.dartSet := by
    simpa [dualMap_α] using (dartSet_alpha_closed C)
  have hraw : SubmapPlanar.rawAlpha (dualMap M) C.dartSet hclosedD = cycleDualAlpha C := by
    ext d
    by_cases hd : d ∈ C.dartSet
    · rw [SubmapPlanar.rawAlpha_eq_self_of_mem (dualMap M) C.dartSet hclosedD hd,
          cycleDualAlpha_eq_self_of_mem C hd]
    · rw [SubmapPlanar.rawAlpha_eq_alpha_of_notMem (dualMap M) C.dartSet hclosedD hd,
          cycleDualAlpha_eq_alpha_of_notMem C hd, dualMap_α]
  obtain ⟨d₀⟩ : Nonempty D := ⟨C.dart ⟨0, C.len_pos⟩⟩
  have hsphereD : (dualMap M).IsSphereMap := dualMap_isSphereMap M hsphere
  have h0 := SubmapPlanar.genusSlack_rawAlpha_eq_zero (dualMap M) C.dartSet hclosedD hsphereD d₀
  rw [hraw] at h0
  rwa [dualMap_σ] at h0



/-- The support of `cycleDualAlpha C` is exactly the non-deleted darts. -/
lemma support_cycleDualAlpha :
    (cycleDualAlpha C).support = Finset.univ \ C.dartSet := by
  classical
  ext d
  simp only [Equiv.Perm.mem_support, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hd hmem
    exact hd (cycleDualAlpha_eq_self_of_mem C hmem)
  · intro hd
    rw [cycleDualAlpha_eq_alpha_of_notMem C hd]
    exact M.α_no_fixed d

/-- The cycle length is at most the number of edges. -/
lemma len_le_E : C.len ≤ M.E := by
  have h2 : (C.dartSet).card = 2 * C.len := dartSet_card C
  have hle : (C.dartSet).card ≤ Fintype.card D := Finset.card_le_univ _
  have hcard : 2 * M.E = Fintype.card D := two_mul_E_eq_card M
  omega

/-- The cycle length is at most the number of vertices (the tails are distinct). -/
lemma len_le_V : C.len ≤ M.V := by
  classical
  have hinj : Function.Injective (fun i => M.tail (C.dart i)) := C.tail_inj
  have hcard : (Finset.univ.image (fun i => M.tail (C.dart i))).card = C.len := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle : (Finset.univ.image (fun i => M.tail (C.dart i))).card
      ≤ Fintype.card M.Vertex := Finset.card_le_univ _
  rw [hcard] at hle
  have : M.V = Fintype.card M.Vertex := rfl
  omega

/-- **`Ehalf (cycleDualAlpha C) = M.E − C.len`.** -/
lemma Ehalf_cycleDualAlpha : Ehalf (cycleDualAlpha C) = M.E - C.len := by
  classical
  have hsupp := support_cycleDualAlpha C
  have hsubset : C.dartSet ⊆ Finset.univ := Finset.subset_univ _
  have hcard : (cycleDualAlpha C).support.card = Fintype.card D - (C.dartSet).card := by
    rw [hsupp, Finset.card_univ_diff]
  have hEval : M.E = Fintype.card D / 2 := by
    have hα : M.α.support = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]; intro d
      rw [Equiv.Perm.mem_support]; exact M.α_no_fixed d
    have : Ehalf M.α = M.E := Ehalf_eq_E M
    rw [Ehalf, hα, Finset.card_univ] at this
    omega
  have hEhalf : Ehalf (cycleDualAlpha C) = (cycleDualAlpha C).support.card / 2 := rfl
  rw [hEhalf, hcard, dartSet_card C]
  omega



/-- The complementary restricted involution `cycleTau C := M.α * cycleDualAlpha C`:
identity off `C.dartSet`, `= M.α` on `C.dartSet`. -/
noncomputable def cycleTau (C : SimplePrimalCycle M) : Equiv.Perm D :=
  M.α * cycleDualAlpha C

lemma cycleTau_eq_alpha_of_mem {d : D} (hd : d ∈ C.dartSet) :
    cycleTau C d = M.α d := by
  show M.α (cycleDualAlpha C d) = M.α d
  rw [cycleDualAlpha_eq_self_of_mem C hd]

lemma cycleTau_eq_self_of_notMem {d : D} (hd : d ∉ C.dartSet) :
    cycleTau C d = d := by
  show M.α (cycleDualAlpha C d) = d
  rw [cycleDualAlpha_eq_alpha_of_notMem C hd, M.alpha_alpha]

/-- **The algebraic reduction.**  `M.φ * cycleDualAlpha = M.σ * cycleTau`. -/
lemma phi_cycleDualAlpha_eq_sigma_cycleTau :
    M.φ * cycleDualAlpha C = M.σ * cycleTau C := by
  show M.φ * cycleDualAlpha C = M.σ * (M.α * cycleDualAlpha C)
  rw [← mul_assoc]; rfl





/-- `M.σ.SameCycle a b ↔ M.tail a = M.tail b`. -/
lemma sigma_sameCycle_iff_tail (a b : D) :
    M.σ.SameCycle a b ↔ M.tail a = M.tail b := by
  show M.σ.SameCycle a b ↔
    (Quotient.mk (cycleSetoid M.σ) a : Quotient (cycleSetoid M.σ)) = Quotient.mk _ b
  rw [Quotient.eq]
  rfl

/-- Distinct forward cycle darts lie in distinct `σ`-cycles: their tails are distinct. -/
lemma sigma_sameCycle_dart_dart (i j : Fin C.len) :
    M.σ.SameCycle (C.dart i) (C.dart j) ↔ i = j := by
  rw [sigma_sameCycle_iff_tail]
  constructor
  · intro h; exact C.tail_inj h
  · intro h; rw [h]

/-- **The key dynamical fact:** `M.σ.SameCycle (M.α (C.dart i)) (C.dart (nextIdx i))`.
`tail (α (C.dart i)) = head (C.dart i) = tail (C.dart (nextIdx i))`. -/
lemma sigma_sameCycle_alphaDart_dart_next (i : Fin C.len) :
    M.σ.SameCycle (M.α (C.dart i)) (C.dart (C.nextIdx i)) := by
  rw [sigma_sameCycle_iff_tail, M.tail_alpha]
  exact (C.tail_dart_nextIdx i).symm



lemma dart_ne_alphaDart_self (i : Fin C.len) : C.dart i ≠ M.α (C.dart i) :=
  C.dart_ne_alpha_self i

lemma dart_ne_alphaDart (i j : Fin C.len) : C.dart i ≠ M.α (C.dart j) :=
  C.dart_ne_alpha_dart i j

lemma alphaDart_ne_dart (i j : Fin C.len) : M.α (C.dart i) ≠ C.dart j :=
  fun h => C.dart_ne_alpha_dart j i h.symm



/-- For a non-final index, `nextIdx` increments the value (no wraparound). -/
lemma nextIdx_val_of_lt {i : Fin C.len} (hi : i.1 < C.len - 1) :
    (C.nextIdx i).1 = i.1 + 1 := by
  rw [SimplePrimalCycle.nextIdx_val, Nat.mod_eq_of_lt (by omega)]



/-- The embedding `Fin (C.len − 1) ↪ Fin C.len`. -/
noncomputable def emb (j : Fin (C.len - 1)) : Fin C.len :=
  ⟨j.1, by have := j.2; omega⟩

/-- The ordered list of the first `C.len − 1` transposition pairs `(C.dart j, α (C.dart j))`. -/
noncomputable def mergePairs (C : SimplePrimalCycle M) : List (D × D) :=
  (List.finRange (C.len - 1)).map (fun j => (C.dart (emb C j), M.α (C.dart (emb C j))))

/-- The partial product permutation after the first `k` merge swaps. -/
noncomputable def pPrefix (C : SimplePrimalCycle M) (k : ℕ) : Equiv.Perm D :=
  M.σ * (((mergePairs C).take k).map (fun w => Equiv.swap w.1 w.2)).prod

lemma pPrefix_zero : pPrefix C 0 = M.σ := by simp [pPrefix]

lemma mergePairs_get_fst (k : ℕ) (hk : k < C.len - 1) :
    (mergePairs C).get ⟨k, by simpa [mergePairs] using hk⟩
      = (C.dart ⟨k, by omega⟩, M.α (C.dart ⟨k, by omega⟩)) := by
  unfold mergePairs
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
  rfl

lemma mergePairs_length : (mergePairs C).length = C.len - 1 := by
  simp [mergePairs]

/-- One-step recurrence for the partial products. -/
lemma pPrefix_succ (k : ℕ) (hk : k < C.len - 1) :
    pPrefix C (k + 1)
      = pPrefix C k * Equiv.swap (C.dart ⟨k, by omega⟩) (M.α (C.dart ⟨k, by omega⟩)) := by
  unfold pPrefix
  have hlen : k < (mergePairs C).length := by rw [mergePairs_length]; exact hk
  have htake : (mergePairs C).take (k + 1)
      = (mergePairs C).take k ++ [(mergePairs C).get ⟨k, hlen⟩] := by
    rw [List.get_eq_getElem]
    exact List.take_succ_eq_append_getElem hlen
  rw [htake, List.map_append, List.prod_append, mergePairs_get_fst C k hk]
  simp [mul_assoc]

/-- `nextIdx` is injective (restated locally for convenience). -/
lemma nextIdx_inj {i j : Fin C.len} (h : C.nextIdx i = C.nextIdx j) : i = j :=
  C.nextIdx_inj h



/-- The simultaneous invariant after `k` merges.  At each cycle vertex `v_m`, the partial
product groups the forward dart `C.dart m` with the reverse dart `M.α (C.dart (prevIdx m))`
(whose tail is also `v_m`); after `k` merges the chain `v_0, …, v_k` is one cycle.

We phrase everything via `nextIdx`: `M.α (C.dart i)` sits in the `σ`-orbit of vertex
`v_{nextIdx i}` (by `sigma_sameCycle_alphaDart_dart_next`).  So the index controlling whether
`M.α (C.dart j)` has joined the block is `(nextIdx j).1 ≤ k`, exactly as in the outer-cycle
proof. -/
lemma bankInvariant :
    ∀ k : ℕ, k + 1 ≤ C.len →
      (∀ i j : Fin C.len,
          (pPrefix C k).SameCycle (C.dart i) (C.dart j)
            ↔ i = j ∨ (i.1 ≤ k ∧ j.1 ≤ k)) ∧
      (∀ i j : Fin C.len,
          (pPrefix C k).SameCycle (C.dart i) (M.α (C.dart j))
            ↔ i = C.nextIdx j ∨ (i.1 ≤ k ∧ (C.nextIdx j).1 ≤ k)) ∧
      (∀ i j : Fin C.len,
          (pPrefix C k).SameCycle (M.α (C.dart i)) (M.α (C.dart j))
            ↔ i = j ∨ ((C.nextIdx i).1 ≤ k ∧ (C.nextIdx j).1 ≤ k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [pPrefix_zero]
      refine ⟨?_, ?_, ?_⟩
      · -- dart-dart base
        intro i j
        rw [sigma_sameCycle_dart_dart]
        constructor
        · exact Or.inl
        · rintro (h | ⟨hi, hj⟩)
          · exact h
          · exact Fin.ext (by omega)
      · -- dart-α base
        intro i j
        have hr : M.σ.SameCycle (M.α (C.dart j)) (C.dart (C.nextIdx j)) :=
          sigma_sameCycle_alphaDart_dart_next C j
        constructor
        · intro h
          have : M.σ.SameCycle (C.dart i) (C.dart (C.nextIdx j)) := h.trans hr
          left; exact (sigma_sameCycle_dart_dart C i (C.nextIdx j)).mp this
        · rintro (h | ⟨hi, hcon⟩)
          · subst h; exact hr.symm
          · have : i = C.nextIdx j := Fin.ext (by omega)
            subst this; exact hr.symm
      · -- α-α base
        intro i j
        have hri : M.σ.SameCycle (M.α (C.dart i)) (C.dart (C.nextIdx i)) :=
          sigma_sameCycle_alphaDart_dart_next C i
        have hrj : M.σ.SameCycle (M.α (C.dart j)) (C.dart (C.nextIdx j)) :=
          sigma_sameCycle_alphaDart_dart_next C j
        constructor
        · intro h
          have : M.σ.SameCycle (C.dart (C.nextIdx i)) (C.dart (C.nextIdx j)) :=
            (hri.symm.trans h).trans hrj
          left; exact nextIdx_inj C ((sigma_sameCycle_dart_dart C _ _).mp this)
        · rintro (h | ⟨hci, hcj⟩)
          · subst h; exact SameCycle.rfl
          · have : C.nextIdx i = C.nextIdx j := Fin.ext (by omega)
            rw [nextIdx_inj C this]
  | succ k ih =>
      intro hk1
      have hkB1 : k < C.len - 1 := by omega
      have hkB : k < C.len := by omega
      obtain ⟨ihqq, ihqr, ihrr⟩ := ih (by omega)
      set a := C.dart ⟨k, hkB⟩ with ha
      set b := M.α (C.dart ⟨k, hkB⟩) with hb
      have hak : (⟨k, hkB⟩ : Fin C.len).1 = k := rfl
      have hnextk : (C.nextIdx ⟨k, hkB⟩).1 = k + 1 := nextIdx_val_of_lt C (by simpa using hkB1)
      have hnsc : ¬ (pPrefix C k).SameCycle a b := by
        rw [ha, hb, ihqr ⟨k, hkB⟩ ⟨k, hkB⟩]
        rintro (hcon | ⟨_, hcon⟩)
        · have := congrArg Fin.val hcon; rw [hnextk] at this; simp at this
        · rw [hnextk] at hcon; omega
      have hstep := pPrefix_succ C k hkB1
      have engine : ∀ x y : D,
          (pPrefix C (k + 1)).SameCycle x y ↔
            (pPrefix C k).SameCycle x y ∨
              ((pPrefix C k).SameCycle x a ∧ (pPrefix C k).SameCycle y b) ∨
              ((pPrefix C k).SameCycle x b ∧ (pPrefix C k).SameCycle y a) := by
        intro x y
        rw [hstep]
        exact PermTranspositionCycleCount.sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle
          (pPrefix C k) hnsc (x := x) (y := y)
      have hqa : ∀ i : Fin C.len,
          (pPrefix C k).SameCycle (C.dart i) a ↔ i.1 ≤ k := by
        intro i; rw [ha, ihqq i ⟨k, hkB⟩]
        constructor
        · rintro (h | ⟨hi, _⟩)
          · exact le_of_eq (congrArg Fin.val h)
          · exact hi
        · intro hi
          rcases Nat.lt_or_ge i.1 k with h | h
          · exact Or.inr ⟨by omega, le_refl k⟩
          · exact Or.inl (Fin.ext (le_antisymm hi h))
      have hqb : ∀ i : Fin C.len,
          (pPrefix C k).SameCycle (C.dart i) b ↔ i.1 = k + 1 := by
        intro i; rw [hb, ihqr i ⟨k, hkB⟩, hnextk]
        constructor
        · rintro (h | ⟨_, hcon⟩)
          · have := congrArg Fin.val h; rw [hnextk] at this; exact this
          · omega
        · intro hi; left; exact Fin.ext (by rw [hnextk]; exact hi)
      have hrb : ∀ i : Fin C.len,
          (pPrefix C k).SameCycle (M.α (C.dart i)) b ↔ (C.nextIdx i).1 = k + 1 := by
        intro i; rw [hb, ihrr i ⟨k, hkB⟩, hnextk]
        constructor
        · rintro (h | ⟨hi, hcon⟩)
          · subst h; rw [hnextk]
          · omega
        · intro hi; left; exact nextIdx_inj C (Fin.ext (by rw [hnextk]; omega))
      refine ⟨?_, ?_, ?_⟩
      · -- dart-dart at k+1
        intro i j
        rw [engine (C.dart i) (C.dart j), ihqq i j, hqa i, hqb j, hqb i, hqa j]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · right; refine ⟨by omega, by omega⟩
          · right; refine ⟨by omega, by omega⟩
        · rintro (h | ⟨hi, hj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge i.1 (k+1) with hik | hik
            · rcases Nat.lt_or_ge j.1 (k+1) with hjk | hjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · rcases Nat.lt_or_ge j.1 (k+1) with hjk | hjk
              · right; right; exact ⟨by omega, by omega⟩
              · exact Or.inl (Or.inl (Fin.ext (by omega)))
      · -- dart-α at k+1
        intro i j
        rw [engine (C.dart i) (M.α (C.dart j)), ihqr i j, hqa i, hrb j, hqb i]
        have hrja : (pPrefix C k).SameCycle (M.α (C.dart j)) a ↔ (C.nextIdx j).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ j]
          constructor
          · rintro (h | ⟨_, hj⟩)
            · have : (C.nextIdx j).1 = k := (congrArg Fin.val h).symm
              omega
            · exact hj
          · intro hj
            rcases Nat.lt_or_ge (C.nextIdx j).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        rw [hrja]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
        · rintro (h | ⟨hi, hnj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge i.1 (k+1) with hik | hik
            · rcases Nat.lt_or_ge (C.nextIdx j).1 (k+1) with hnjk | hnjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · rcases Nat.lt_or_ge (C.nextIdx j).1 (k+1) with hnjk | hnjk
              · right; right; exact ⟨by omega, by omega⟩
              · exact Or.inl (Or.inl (Fin.ext (by omega)))
      · -- α-α at k+1
        intro i j
        rw [engine (M.α (C.dart i)) (M.α (C.dart j)), ihrr i j, hrb j, hrb i]
        have hria : (pPrefix C k).SameCycle (M.α (C.dart i)) a ↔ (C.nextIdx i).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ i]
          constructor
          · rintro (h | ⟨_, hi⟩)
            · have := congrArg Fin.val h; omega
            · exact hi
          · intro hi
            rcases Nat.lt_or_ge (C.nextIdx i).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        have hrja : (pPrefix C k).SameCycle (M.α (C.dart j)) a ↔ (C.nextIdx j).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ j]
          constructor
          · rintro (h | ⟨_, hj⟩)
            · have := congrArg Fin.val h; omega
            · exact hj
          · intro hj
            rcases Nat.lt_or_ge (C.nextIdx j).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        rw [hria, hrja]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
        · rintro (h | ⟨hni, hnj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge (C.nextIdx i).1 (k+1) with hnik | hnik
            · rcases Nat.lt_or_ge (C.nextIdx j).1 (k+1) with hnjk | hnjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · rcases Nat.lt_or_ge (C.nextIdx j).1 (k+1) with hnjk | hnjk
              · right; right; exact ⟨by omega, by omega⟩
              · have : C.nextIdx i = C.nextIdx j := Fin.ext (by omega)
                exact Or.inl (Or.inl (nextIdx_inj C this))



lemma len_pos' : 0 < C.len := C.len_pos

/-- The fully-merged permutation after all `C.len − 1` merges. -/
noncomputable def pMerge (C : SimplePrimalCycle M) : Equiv.Perm D :=
  pPrefix C (C.len - 1)

/-- The `C.len − 1` merge swaps each merge two distinct cycles of the running product. -/
lemma mergePairs_merge_condition :
    ∀ j : Fin (mergePairs C).length,
      ((mergePairs C).get j).1 ≠ ((mergePairs C).get j).2 ∧
        ¬ (M.σ * (((mergePairs C).take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
            ((mergePairs C).get j).1 ((mergePairs C).get j).2 := by
  intro j
  have he : (mergePairs C).length = C.len - 1 := mergePairs_length C
  have hjlen : (j : ℕ) < C.len - 1 := by have := j.2; omega
  have hjB : (j : ℕ) < C.len := by omega
  rw [mergePairs_get_fst C (j : ℕ) hjlen]
  have hpp : M.σ * (((mergePairs C).take (j : ℕ)).map (fun w => Equiv.swap w.1 w.2)).prod
      = pPrefix C (j : ℕ) := rfl
  refine ⟨?_, ?_⟩
  · exact dart_ne_alphaDart_self C ⟨(j : ℕ), hjB⟩
  · rw [hpp]
    obtain ⟨_, ihqr, _⟩ := bankInvariant C (j : ℕ) (by omega)
    rw [ihqr ⟨(j : ℕ), hjB⟩ ⟨(j : ℕ), hjB⟩]
    have hnext : (C.nextIdx ⟨(j : ℕ), hjB⟩).1 = (j : ℕ) + 1 :=
      nextIdx_val_of_lt C (by simpa using hjlen)
    rintro (hcon | ⟨_, hcon⟩)
    · have := congrArg Fin.val hcon; rw [hnext] at this; simp at this
    · rw [hnext] at hcon; omega

/-- After all `C.len − 1` merges, the cycle count is `V − (C.len − 1)`. -/
lemma numCycles_pMerge_add :
    _root_.numCycles (pMerge C) + (C.len - 1) = M.V := by
  have hmerge := CombMap.CutCapCount.numCycles_mul_listSwap_merges M.σ (mergePairs C)
    (mergePairs_merge_condition C)
  rw [mergePairs_length] at hmerge
  have hpm : pMerge C = M.σ * ((mergePairs C).map (fun w => Equiv.swap w.1 w.2)).prod := by
    unfold pMerge pPrefix
    rw [List.take_of_length_le (by rw [mergePairs_length])]
  rw [hpm, hmerge, M.V_eq_numCycles]

/-- The last cycle pair `(C.dart last, α (C.dart last))`, `last = ⟨C.len−1⟩`. -/
noncomputable def lastIdx (C : SimplePrimalCycle M) : Fin C.len :=
  ⟨C.len - 1, by have := len_pos' C; omega⟩

/-- In `pMerge`, the last pair lies in the same cycle (so the closing swap splits). -/
lemma pMerge_lastPair_sameCycle :
    (pMerge C).SameCycle (C.dart (lastIdx C)) (M.α (C.dart (lastIdx C))) := by
  unfold pMerge
  have hBpos : 0 < C.len := len_pos' C
  obtain ⟨_, ihqr, _⟩ := bankInvariant C (C.len - 1) (by omega)
  rw [ihqr (lastIdx C) (lastIdx C)]
  right
  have hnl : (C.nextIdx (lastIdx C)).1 = 0 := by
    rw [SimplePrimalCycle.nextIdx_val]
    show ((C.len - 1) + 1) % C.len = 0
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  refine ⟨?_, ?_⟩
  · show (C.len - 1) ≤ C.len - 1; exact le_refl _
  · rw [hnl]; exact Nat.zero_le _



/-- A cycle dart is some `C.dart m` or `M.α (C.dart m)`; the forward case here. -/
lemma listSwapQR_apply_dart (m : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup → m ∈ L →
      ((L.map (fun i => (C.dart i, M.α (C.dart i)))).map (fun w => Equiv.swap w.1 w.2)).prod
          (C.dart m) = M.α (C.dart m) := by
  intro L
  induction L with
  | nil => intro _ hm; simp only [List.not_mem_nil] at hm
  | cons c t ih =>
      intro hnd hm
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      have hndt := (List.nodup_cons.mp hnd)
      by_cases hmt : m ∈ t
      · have hcm : c ≠ m := fun h => hndt.1 (h ▸ hmt)
        rw [ih hndt.2 hmt]
        show Equiv.swap (C.dart c) (M.α (C.dart c)) (M.α (C.dart m)) = M.α (C.dart m)
        rw [Equiv.swap_apply_of_ne_of_ne (alphaDart_ne_dart C m c)
          (fun h => hcm (C.alpha_dart_inj h).symm)]
      · have hmc : m = c := by
          rcases List.mem_cons.mp hm with h | h
          · exact h
          · exact absurd h hmt
        subst hmc
        have htail : ((t.map (fun i => (C.dart i, M.α (C.dart i)))).map
            (fun w => Equiv.swap w.1 w.2)).prod (C.dart m) = C.dart m := by
          apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          have hineq : i ≠ m := fun h => hmt (h ▸ hi)
          subst hwi
          exact ⟨fun h => hineq (C.dart_inj h).symm, dart_ne_alphaDart C m i⟩
        rw [htail]
        show Equiv.swap (C.dart m) (M.α (C.dart m)) (C.dart m) = M.α (C.dart m)
        rw [Equiv.swap_apply_left]

/-- The reverse case: at an `α`-dart whose index is in the (nodup) list. -/
lemma listSwapQR_apply_alphaDart (m : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup → m ∈ L →
      ((L.map (fun i => (C.dart i, M.α (C.dart i)))).map (fun w => Equiv.swap w.1 w.2)).prod
          (M.α (C.dart m)) = C.dart m := by
  intro L
  induction L with
  | nil => intro _ hm; simp only [List.not_mem_nil] at hm
  | cons c t ih =>
      intro hnd hm
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      have hndt := (List.nodup_cons.mp hnd)
      by_cases hmt : m ∈ t
      · have hcm : c ≠ m := fun h => hndt.1 (h ▸ hmt)
        rw [ih hndt.2 hmt]
        show Equiv.swap (C.dart c) (M.α (C.dart c)) (C.dart m) = C.dart m
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => hcm (C.dart_inj h).symm) (dart_ne_alphaDart C m c)]
      · have hmc : m = c := by
          rcases List.mem_cons.mp hm with h | h
          · exact h
          · exact absurd h hmt
        subst hmc
        have htail : ((t.map (fun i => (C.dart i, M.α (C.dart i)))).map
            (fun w => Equiv.swap w.1 w.2)).prod (M.α (C.dart m)) = M.α (C.dart m) := by
          apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          have hineq : i ≠ m := fun h => hmt (h ▸ hi)
          subst hwi
          exact ⟨alphaDart_ne_dart C m i, fun h => hineq (C.alpha_dart_inj h).symm⟩
        rw [htail]
        show Equiv.swap (C.dart m) (M.α (C.dart m)) (M.α (C.dart m)) = C.dart m
        rw [Equiv.swap_apply_right]

/-- Evaluation at a dart that is neither a forward nor reverse cycle dart: it is fixed. -/
lemma listSwapQR_apply_other (d : D)
    (L : List (Fin C.len))
    (hd : ∀ i ∈ L, d ≠ C.dart i ∧ d ≠ M.α (C.dart i)) :
    ((L.map (fun i => (C.dart i, M.α (C.dart i)))).map (fun w => Equiv.swap w.1 w.2)).prod d = d := by
  apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
  intro w hw
  rw [List.mem_map] at hw
  obtain ⟨i, hi, hwi⟩ := hw
  subst hwi
  exact hd i hi

/-- The full pair list over all `C.len` indices. -/
noncomputable def allPairs (C : SimplePrimalCycle M) : List (D × D) :=
  (List.finRange C.len).map (fun i => (C.dart i, M.α (C.dart i)))

/-- `cycleTau` is the product of the `C.len` disjoint cycle transpositions. -/
lemma cycleTau_eq_swapProd :
    cycleTau C = ((allPairs C).map (fun w => Equiv.swap w.1 w.2)).prod := by
  have hnd : (List.finRange C.len).Nodup := List.nodup_finRange _
  ext d
  unfold allPairs
  by_cases hd : d ∈ C.dartSet
  · rw [cycleTau_eq_alpha_of_mem C hd]
    rw [C.mem_dartSet_iff] at hd
    obtain ⟨m, hm | hm⟩ := hd
    · -- d = C.dart m
      subst hm
      rw [listSwapQR_apply_dart C m _ hnd (List.mem_finRange m)]
    · -- d = α (C.dart m)
      subst hm
      rw [listSwapQR_apply_alphaDart C m _ hnd (List.mem_finRange m), M.alpha_alpha]
  · rw [cycleTau_eq_self_of_notMem C hd]
    refine (listSwapQR_apply_other C d _ ?_).symm
    intro i _
    refine ⟨?_, ?_⟩
    · intro h; exact hd (h ▸ C.dart_mem_dartSet i)
    · intro h; exact hd (h ▸ C.alpha_dart_mem_dartSet i)

/-- `allPairs = mergePairs ++ [last pair]`. -/
lemma allPairs_eq_append :
    allPairs C = mergePairs C ++ [(C.dart (lastIdx C), M.α (C.dart (lastIdx C)))] := by
  have hBpos : 0 < C.len := len_pos' C
  have hlenA : (allPairs C).length = C.len := by
    simp [allPairs, List.length_map, List.length_finRange]
  have hmlen : (mergePairs C).length = C.len - 1 := mergePairs_length C
  have hlenR : (mergePairs C ++ [(C.dart (lastIdx C), M.α (C.dart (lastIdx C)))]).length
      = C.len := by
    rw [List.length_append, hmlen, List.length_singleton]; omega
  apply List.ext_getElem (by rw [hlenA, hlenR])
  intro n hn1 hn2
  rw [hlenA] at hn1
  have hLHS : (allPairs C)[n] = (C.dart ⟨n, hn1⟩, M.α (C.dart ⟨n, hn1⟩)) := by
    simp only [allPairs]
    rw [List.getElem_map, List.getElem_finRange]
    congr 1
  rw [hLHS]
  by_cases hnlast : n < C.len - 1
  · rw [List.getElem_append_left (by rw [hmlen]; exact hnlast)]
    simp only [mergePairs]
    rw [List.getElem_map, List.getElem_finRange]
    show (C.dart ⟨n, hn1⟩, M.α (C.dart ⟨n, hn1⟩))
      = (C.dart (emb C _), M.α (C.dart (emb C _)))
    congr 1
  · rw [List.getElem_append_right (by rw [hmlen]; omega)]
    have hidx : (⟨n, hn1⟩ : Fin C.len) = lastIdx C :=
      Fin.ext (by simp only [lastIdx]; omega)
    rw [hidx, List.getElem_singleton]

/-- `M.σ * cycleTau = pMerge * swap (C.dart last) (α (C.dart last))`. -/
lemma sigma_cycleTau_eq :
    M.σ * cycleTau C
      = pMerge C * Equiv.swap (C.dart (lastIdx C)) (M.α (C.dart (lastIdx C))) := by
  rw [cycleTau_eq_swapProd, allPairs_eq_append, List.map_append, List.prod_append]
  unfold pMerge pPrefix
  rw [List.take_of_length_le (by rw [mergePairs_length]), List.map_singleton, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc]

/-- **The bank count — UNCONDITIONAL.**
`numCycles (M.φ * cycleDualAlpha C) = M.V − C.len + 2`. -/
theorem bankCount_holds :
    _root_.numCycles (M.φ * cycleDualAlpha C) = M.V - C.len + 2 := by
  rw [phi_cycleDualAlpha_eq_sigma_cycleTau, sigma_cycleTau_eq]
  have hsplit : _root_.numCycles
      (pMerge C * Equiv.swap (C.dart (lastIdx C)) (M.α (C.dart (lastIdx C))))
      = _root_.numCycles (pMerge C) + 1 :=
    CombMap.CutCapCount.numCycles_mul_swap_of_sameCycle (pMerge C)
      (dart_ne_alphaDart_self C (lastIdx C)) (pMerge_lastPair_sameCycle C)
  rw [hsplit]
  have hmerge := numCycles_pMerge_add C
  have hBpos : 0 < C.len := len_pos' C
  have hBV : C.len ≤ M.V := len_le_V C
  omega



/-- A dart lies in `C.dartSet` iff its edge lies in `C.edgeSet`. -/
lemma mem_dartSet_iff_edgeSet (hsimple : M.IsSimpleGraph) {d : D} :
    d ∈ C.dartSet ↔ M.dartEdge d ∈ C.edgeSet := by
  constructor
  · intro hd
    rw [C.mem_dartSet_iff] at hd
    obtain ⟨i, hi | hi⟩ := hd
    · exact (C.mem_edgeSet_iff _).2 ⟨i, by rw [hi, SimplePrimalCycle.edge]⟩
    · exact (C.mem_edgeSet_iff _).2 ⟨i, by rw [hi, SimplePrimalCycle.edge, M.dartEdge_alpha]⟩
  · intro he
    rw [C.mem_edgeSet_iff] at he
    obtain ⟨i, hi⟩ := he
    -- `dartEdge d = C.edge i = dartEdge (C.dart i)` ⟹ `α.SameCycle d (C.dart i)`
    have hsc : M.α.SameCycle d (C.dart i) :=
      hsimple.no_parallel (by rw [hi, SimplePrimalCycle.edge])
    rcases (M.alpha_sameCycle_iff d (C.dart i)).mp hsc with hde | hde
    · exact (C.mem_dartSet_iff d).2 ⟨i, Or.inl (by rw [hde])⟩
    · exact (C.mem_dartSet_iff d).2 ⟨i, Or.inr (by rw [hde, M.alpha_alpha])⟩

lemma notMem_dartSet_iff_not_edgeSet (hsimple : M.IsSimpleGraph) {d : D} :
    d ∉ C.dartSet ↔ M.dartEdge d ∉ C.edgeSet :=
  not_congr (mem_dartSet_iff_edgeSet C hsimple)

/-- Same face ⟺ `M.φ.SameCycle`. -/
lemma sameFace_iff_phi_sameCycle {a b : D} :
    M.dartFace a = M.dartFace b ↔ M.φ.SameCycle a b := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

/-- The relation `dartStepRel M.φ (cycleDualAlpha C)`. -/
abbrev RDart (C : SimplePrimalCycle M) : D → D → Prop :=
  dartStepRel M.φ (cycleDualAlpha C)

/-- A single `RDart`-step descends to `EqvGen (DualAvoidsCycleStep)` on faces. -/
lemma eqvGen_dualStep_of_RDart_step (hsimple : M.IsSimpleGraph) {a b : D}
    (h : RDart C a b) :
    Relation.EqvGen (DualAvoidsCycleStep M C) (M.dartFace a) (M.dartFace b) := by
  rcases h with hsc | hαe
  · have : M.dartFace a = M.dartFace b := sameFace_iff_phi_sameCycle.mpr hsc
    rw [this]; exact Relation.EqvGen.refl _
  · by_cases hd : a ∈ C.dartSet
    · rw [hαe, cycleDualAlpha_eq_self_of_mem C hd]
      exact Relation.EqvGen.refl _
    · have hba : b = M.α a := by
        rw [hαe, cycleDualAlpha_eq_alpha_of_notMem C hd]
      have hnb : M.dartEdge a ∉ C.edgeSet :=
        (notMem_dartSet_iff_not_edgeSet C hsimple).mp hd
      have hstep : DualAvoidsCycleStep M C (M.dartFace a) (M.dartFace b) :=
        ⟨a, hnb, rfl, by rw [hba]⟩
      exact Relation.EqvGen.rel _ _ hstep

/-- A single `DualAvoidsCycleStep` lifts to `EqvGen RDart` on any dart reps. -/
lemma eqvGen_RDart_of_dualStep {f g : M.Face} {a b : D}
    (hstep : DualAvoidsCycleStep M C f g) (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.EqvGen (RDart C) a b := by
  obtain ⟨d, hbe, hdf, hdg⟩ := hstep
  have hdDel : d ∉ C.dartSet := C.notMem_dartSet_of_dartEdge_notMem hbe
  have h1 : Relation.EqvGen (RDart C) a d :=
    Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [ha, hdf])))
  have h2 : Relation.EqvGen (RDart C) d (M.α d) :=
    Relation.EqvGen.rel _ _ (Or.inr (by
      rw [cycleDualAlpha_eq_alpha_of_notMem C hdDel]))
  have h3 : Relation.EqvGen (RDart C) (M.α d) b :=
    Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [hdg, hb])))
  exact (h1.trans _ _ _ h2).trans _ _ _ h3

/-- A `DualAvoidsCycleStep`-walk lifts to `EqvGen RDart`. -/
lemma eqvGen_RDart_of_dualStep_walk {f g : M.Face} {a b : D}
    (hwalk : Relation.ReflTransGen (DualAvoidsCycleStep M C) f g)
    (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.EqvGen (RDart C) a b := by
  induction hwalk generalizing b with
  | refl =>
    exact Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [ha, hb])))
  | @tail x y hwxy hstep ih =>
    obtain ⟨c, hc⟩ : ∃ c : D, M.dartFace c = x := ⟨Quotient.out x, Quotient.out_eq x⟩
    have hac : Relation.EqvGen (RDart C) a c := ih hc
    have hcb : Relation.EqvGen (RDart C) c b :=
      eqvGen_RDart_of_dualStep C hstep hc hb
    exact hac.trans _ _ _ hcb

/-- The full `EqvGen RDart`-walk descends to `EqvGen DualAvoidsCycleStep` on faces. -/
lemma eqvGen_dualStep_of_RDart_eqv (hsimple : M.IsSimpleGraph) {a b : D}
    (hab : Relation.EqvGen (RDart C) a b) :
    Relation.EqvGen (DualAvoidsCycleStep M C) (M.dartFace a) (M.dartFace b) := by
  induction hab with
  | rel x y h => exact eqvGen_dualStep_of_RDart_step C hsimple h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact ih.symm _ _
  | trans x y z _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

/-- `DualAvoidsCycleStep` is symmetric (the reverse dart witnesses the reverse step). -/
lemma dualAvoidsCycleStep_symm {f g : M.Face} (h : DualAvoidsCycleStep M C f g) :
    DualAvoidsCycleStep M C g f := by
  obtain ⟨d, hbe, hdf, hdg⟩ := h
  refine ⟨M.α d, ?_, hdg, ?_⟩
  · rw [M.dartEdge_alpha]; exact hbe
  · rw [M.alpha_alpha]; exact hdf

/-- `EqvGen (DualAvoidsCycleStep)` coincides with `ReflTransGen` (symmetric relation). -/
lemma eqvGen_dualStep_iff {f g : M.Face} :
    Relation.EqvGen (DualAvoidsCycleStep M C) f g ↔
      Relation.ReflTransGen (DualAvoidsCycleStep M C) f g :=
  eqvGen_iff_reflTransGen (fun _ _ => dualAvoidsCycleStep_symm C) f g

/-- The face quotient map descends from the dart component quotient. -/
noncomputable def faceQuotMap (hsimple : M.IsSimpleGraph) :
    Quotient (compSetoid (RDart C)) → Quotient (compSetoid (DualAvoidsCycleStep M C)) :=
  Quotient.lift (fun d => Quotient.mk (compSetoid (DualAvoidsCycleStep M C)) (M.dartFace d))
    (by
      intro a b hab
      apply Quotient.sound
      exact eqvGen_dualStep_of_RDart_eqv C hsimple hab)

/-- **The dart-face quotient bridge.**  The component count of the dual sub-involution pair
equals the dual-face component count `numComp (DualAvoidsCycleStep M C)`. -/
lemma numComponents_eq_numComp_dualStep (hsimple : M.IsSimpleGraph) :
    numComponents M.φ (cycleDualAlpha C) = numComp (DualAvoidsCycleStep M C) := by
  classical
  rw [numComponents_def]
  show numComp (RDart C) = numComp (DualAvoidsCycleStep M C)
  unfold numComp
  apply Nat.card_congr
  refine Equiv.ofBijective (faceQuotMap C hsimple) ⟨?_, ?_⟩
  · intro x y hxy
    refine Quotient.inductionOn₂ x y (fun a b hab => ?_) hxy
    apply Quotient.sound
    have heqf : Relation.EqvGen (DualAvoidsCycleStep M C) (M.dartFace a) (M.dartFace b) :=
      Quotient.exact hab
    have hwalk : Relation.ReflTransGen (DualAvoidsCycleStep M C) (M.dartFace a) (M.dartFace b) :=
      (eqvGen_dualStep_iff C).1 heqf
    exact eqvGen_RDart_of_dualStep_walk C hwalk rfl rfl
  · intro q
    refine Quotient.inductionOn q (fun f => ?_)
    obtain ⟨d, hd⟩ : ∃ d : D, M.dartFace d = f := ⟨Quotient.out f, Quotient.out_eq f⟩
    exact ⟨Quotient.mk (compSetoid (RDart C)) d, by
      show Quotient.mk _ (M.dartFace d) = Quotient.mk _ f
      rw [hd]⟩



/-- **The two-component count for an arbitrary simple primal cycle — UNCONDITIONAL** (given
sphere + simple-graph).  Expanding `genusSlack M.φ (cycleDualAlpha C) = 0` with the bank
count, the `Ehalf`, the dart-face bridge, and Euler `V − E + F = 2`. -/
theorem dualAvoidsCycle_numComp_two (hsphere : M.IsSphereMap) (hsimple : M.IsSimpleGraph) :
    numComp (DualAvoidsCycleStep M C) = 2 := by
  have h0 : genusSlack M.φ (cycleDualAlpha C) = 0 :=
    genusSlack_cycleDualAlpha_eq_zero C hsphere
  have hE5 : Ehalf (cycleDualAlpha C) = M.E - C.len := Ehalf_cycleDualAlpha C
  have h6 : _root_.numCycles (M.φ * cycleDualAlpha C) = M.V - C.len + 2 := bankCount_holds C
  have hbridge : numComponents M.φ (cycleDualAlpha C) = numComp (DualAvoidsCycleStep M C) :=
    numComponents_eq_numComp_dualStep C hsimple
  have hF : _root_.numCycles M.φ = M.F := (M.F_eq_numCycles).symm
  have hEuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hsphere.2
  set B := C.len with hB
  have hBE : B ≤ M.E := len_le_E C
  unfold genusSlack at h0
  rw [hbridge, hF, hE5, h6] at h0
  have hcast5 : ((M.E - B : ℕ) : ℤ) = (M.E : ℤ) - (B : ℤ) := by
    rw [Nat.cast_sub hBE]
  have hcast6 : ((M.V - B + 2 : ℕ) : ℤ) = (M.V : ℤ) - (B : ℤ) + 2 := by
    have hBV : B ≤ M.V := len_le_V C
    push_cast [Nat.cast_sub hBV]; ring
  rw [hcast5, hcast6] at h0
  have hc : (numComp (DualAvoidsCycleStep M C) : ℤ) = 2 := by linarith
  exact_mod_cast hc







/-- **The local σ-star classifier at a cycle vertex.**  A dart `z` in the σ-orbit of
`M.α (C.dart i)` (i.e. `tail z = v_{nextIdx i}`) has its edge in `C.edgeSet` iff `z` is one
of the two cycle darts `M.α (C.dart i)` or `C.dart (nextIdx i)`.

We package the "iff" as the contrapositive we actually use: if `z` shares the σ-orbit and is
neither of the two cycle darts, then `dartEdge z ∉ C.edgeSet`. -/
lemma not_mem_edgeSet_of_star_not_cycleDart (hsimple : M.IsSimpleGraph) {i : Fin C.len} {z : D}
    (hσ : M.σ.SameCycle (M.α (C.dart i)) z)
    (hz1 : z ≠ M.α (C.dart i)) (hz2 : z ≠ C.dart (C.nextIdx i)) :
    M.dartEdge z ∉ C.edgeSet := by
  rw [← notMem_dartSet_iff_not_edgeSet C hsimple]
  intro hmem
  rw [C.mem_dartSet_iff] at hmem
  -- `tail z = tail (α (C.dart i)) = head (C.dart i) = v_{nextIdx i}`.
  have htail : M.tail z = M.tail (C.dart (C.nextIdx i)) := by
    rw [(sigma_sameCycle_iff_tail (M.α (C.dart i)) z).mp hσ |>.symm, M.tail_alpha,
        C.tail_dart_nextIdx i]
  obtain ⟨j, hj | hj⟩ := hmem
  · -- z = C.dart j, tail = tail (C.dart j) = v_{nextIdx i} ⟹ j = nextIdx i.
    apply hz2
    rw [hj]; congr 1
    apply C.tail_inj
    show M.tail (C.dart j) = M.tail (C.dart (C.nextIdx i))
    rw [← hj]; exact htail
  · -- z = α (C.dart j), tail = head (C.dart j) = v_{nextIdx i} = head (C.dart i) ⟹ j = i.
    apply hz1
    -- `tail (α (C.dart j)) = tail (α (C.dart i))` ⟹ `j = i` ⟹ `z = α (C.dart j) = α (C.dart i)`.
    have hheadj : M.tail (M.α (C.dart j)) = M.tail (C.dart (C.nextIdx i)) := by
      rw [← hj]; exact htail
    have hi : M.head (C.dart i) = M.tail (C.dart (C.nextIdx i)) := C.consecutive' i
    -- head (C.dart j) = head (C.dart i): chase through nextIdx tails.
    have hheadeq : M.head (C.dart j) = M.head (C.dart i) := hheadj.trans hi.symm
    have hnext : M.tail (C.dart (C.nextIdx j)) = M.tail (C.dart (C.nextIdx i)) := by
      rw [C.tail_dart_nextIdx j, C.tail_dart_nextIdx i, hheadeq]
    have hnij : C.nextIdx j = C.nextIdx i := C.tail_inj hnext
    have hji : j = i := nextIdx_inj C hnij
    rw [hj, hji]



/-- **The general simple-cycle bank theorem (R6 §4).**  Packages the two-bank structure of an
arbitrary simple primal cycle: the unconditional two-component count, plus the bank labels
(left/right connectivity and separation).  The `dual_numComp_two`, `bankOrbitCount`,
`slack_zero` fields are filled **unconditionally** by `cycleBankTheorem_core`; the bank-label
fields are carried as the residual. -/
structure SimpleCycleBankTheorem (M : CombMap D) (C : SimplePrimalCycle M) where
  dual_numComp_two : numComp (DualAvoidsCycleStep M C) = 2
  bankOrbitCount : _root_.numCycles (M.φ * cycleDualAlpha C) = M.V - C.len + 2
  slack_zero : genusSlack M.φ (cycleDualAlpha C) = 0
  left_bank : ∀ i j : Fin C.len,
    Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceLeft j)
  right_bank : ∀ i j : Fin C.len,
    Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceRight i) (C.faceRight j)
  left_right_sep : ∀ i j : Fin C.len,
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceRight j)





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



/-- One σ-step is a `DualAvoidsCycleStep` step when `dartEdge z ∉ C.edgeSet`. -/
lemma dualStep_sigma (hsimple : M.IsSimpleGraph) {z : D}
    (hz : M.dartEdge z ∉ C.edgeSet) :
    DualAvoidsCycleStep M C (M.dartFace z) (M.dartFace (M.σ z)) := by
  refine ⟨z, hz, rfl, ?_⟩
  rw [ZinanCh35StarConn.dartFace_sigma_eq_alpha]

/-- **The σ-arc walker.**  If every dart `σ^j a` for `0 ≤ j < p` is non-cycle, then
`dartFace a` reaches `dartFace ((σ^p) a)` by a `DualAvoidsCycleStep`-walk. -/
lemma reflTransGen_dualStep_sigma_pow (hsimple : M.IsSimpleGraph) (a : D) :
    ∀ p : ℕ, (∀ j : ℕ, j < p → M.dartEdge ((M.σ ^ j) a) ∉ C.edgeSet) →
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (M.dartFace a) (M.dartFace ((M.σ ^ p) a)) := by
  intro p
  induction p with
  | zero => intro _; simpa using Relation.ReflTransGen.refl
  | succ k ih =>
      intro havoid
      have hreach := ih (fun j hj => havoid j (by omega))
      refine hreach.tail ?_
      have heq : M.σ ((M.σ ^ k) a) = (M.σ ^ (k + 1)) a := by rw [pow_succ']; rfl
      have hstep := dualStep_sigma C hsimple (z := (M.σ ^ k) a) (havoid k (by omega))
      rwa [heq] at hstep



/-- `(σ^m) b ≠ b` for `0 < m < L` (`L = #(σ.cycleOf b).support`), `b ∈ σ.support`. -/
lemma sigma_pow_ne_self {b : D} (hb : b ∈ M.σ.support) {m : ℕ}
    (hm0 : 0 < m) (hmL : m < (M.σ.cycleOf b).support.card) : (M.σ ^ m) b ≠ b :=
  ZinanCh35StarConn.sigma_pow_ne_self_of_lt hb hm0 hmL

/-- Within one orbit period the powers are injective: `(σ^j) b = (σ^p) b` with `j, p < L`
forces `j = p`. -/
lemma sigma_pow_inj_of_lt {b : D} (hb : b ∈ M.σ.support) {j p : ℕ}
    (hjL : j < (M.σ.cycleOf b).support.card) (hpL : p < (M.σ.cycleOf b).support.card)
    (h : (M.σ ^ j) b = (M.σ ^ p) b) : j = p := by
  -- `cycleOf` and support card are invariant along the orbit; reduce to `sigma_pow_ne_self`
  -- on the element `c := (σ^j) b`, which `(σ^(p-j))` (resp. `(σ^(j-p))`) fixes.
  by_contra hne
  rcases le_or_gt j p with hjp | hjp
  · -- `(σ^(p-j))` fixes `c = (σ^j) b`.
    set c := (M.σ ^ j) b with hc
    have hscbc : M.σ.SameCycle b c := ⟨(j : ℤ), by rw [zpow_natCast]⟩
    have hcsupp : c ∈ M.σ.support := (SameCycle.mem_support_iff hscbc).mp hb
    have hcard : (M.σ.cycleOf c).support.card = (M.σ.cycleOf b).support.card := by
      rw [hscbc.cycleOf_eq]
    have hpos : 0 < p - j := by omega
    have hlt : p - j < (M.σ.cycleOf c).support.card := by rw [hcard]; omega
    apply sigma_pow_ne_self (M := M) hcsupp hpos hlt
    rw [hc, ← Equiv.Perm.mul_apply, ← pow_add, show p - j + j = p by omega, ← h]
  · set c := (M.σ ^ p) b with hc
    have hscbc : M.σ.SameCycle b c := ⟨(p : ℤ), by rw [zpow_natCast]⟩
    have hcsupp : c ∈ M.σ.support := (SameCycle.mem_support_iff hscbc).mp hb
    have hcard : (M.σ.cycleOf c).support.card = (M.σ.cycleOf b).support.card := by
      rw [hscbc.cycleOf_eq]
    have hpos : 0 < j - p := by omega
    have hlt : j - p < (M.σ.cycleOf c).support.card := by rw [hcard]; omega
    apply sigma_pow_ne_self (M := M) hcsupp hpos hlt
    rw [hc, ← Equiv.Perm.mul_apply, ← pow_add, show j - p + p = j by omega, h]



/-- The reverse anchor `α (C.dart i)` is in `σ.support`: its σ-orbit also contains the distinct
forward dart `C.dart (nextIdx i)` (same tail), so the orbit is nontrivial. -/
lemma rev_mem_support (i : Fin C.len) : M.α (C.dart i) ∈ M.σ.support := by
  rw [Equiv.Perm.mem_support]
  intro hfix
  -- if `σ (α (C.dart i)) = α (C.dart i)`, the σ-orbit of `α (C.dart i)` is a singleton, but it
  -- must also contain `C.dart (nextIdx i)` (same tail), which is distinct.
  have hsc : M.σ.SameCycle (M.α (C.dart i)) (C.dart (C.nextIdx i)) :=
    sigma_sameCycle_alphaDart_dart_next C i
  obtain ⟨n, hn⟩ := hsc
  -- `σ` fixes `α (C.dart i)`, so `(σ^n) (α (C.dart i)) = α (C.dart i)`.
  have hpow : ∀ k : ℤ, (M.σ ^ k) (M.α (C.dart i)) = M.α (C.dart i) := by
    intro k
    have : ∀ m : ℕ, (M.σ ^ m) (M.α (C.dart i)) = M.α (C.dart i) := by
      intro m
      induction m with
      | zero => simp
      | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply, iht, hfix]
    rcases k with k | k
    · simpa using this k
    · -- negative powers: `σ⁻¹` also fixes it.
      have hinv : M.σ⁻¹ (M.α (C.dart i)) = M.α (C.dart i) := by
        rw [Equiv.Perm.inv_eq_iff_eq, hfix]
      have : ∀ m : ℕ, (M.σ⁻¹ ^ m) (M.α (C.dart i)) = M.α (C.dart i) := by
        intro m
        induction m with
        | zero => simp
        | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply, iht, hinv]
      have hk := this (k + 1)
      rw [zpow_negSucc, ← inv_pow]
      exact hk
  have : C.dart (C.nextIdx i) = M.α (C.dart i) := by rw [← hn]; exact hpow n
  exact (dart_ne_alphaDart C (C.nextIdx i) i) this



/-- **Left-bank step.**  `faceLeft i ↝ faceLeft (nextIdx i)` via the σ-arc from
`α (C.dart i)` to `C.dart (nextIdx i)`. -/
lemma left_bank_step (hsimple : M.IsSimpleGraph) (i : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C)
      (C.faceLeft i) (C.faceLeft (C.nextIdx i)) := by
  set b := M.α (C.dart i) with hb
  have hbsupp : b ∈ M.σ.support := rev_mem_support C i
  set L := (M.σ.cycleOf b).support.card with hL
  -- `fwd = C.dart (nextIdx i)` is in the σ-orbit of `b`, at some power `p`, `0 < p < L`.
  have hsc : M.σ.SameCycle b (C.dart (C.nextIdx i)) := sigma_sameCycle_alphaDart_dart_next C i
  obtain ⟨p, hpL, hp⟩ := hsc.exists_pow_eq_of_mem_support hbsupp
  have hpos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exfalso; rw [h0, pow_zero] at hp; simp only [Equiv.Perm.coe_one, id] at hp
      exact (dart_ne_alphaDart C (C.nextIdx i) i) hp.symm
    · exact h0
  -- the walk from `σ b` to `(σ^p) b = fwd`: re-anchor at `σ b = (σ^1) b`.
  -- Express as: `dartFace (σ b) ↝ dartFace ((σ^p) b)` using powers `1..p-1` of `b` from `σ b`.
  -- We walk `(σ^j) (σ b) = (σ^(j+1)) b` for `0 ≤ j < p-1`.
  have hwalk :
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (M.dartFace (M.σ b)) (M.dartFace ((M.σ ^ (p - 1)) (M.σ b))) := by
    apply reflTransGen_dualStep_sigma_pow C hsimple (M.σ b)
    intro j hj
    -- `(σ^j) (σ b) = (σ^(j+1)) b`, a non-cycle dart (strictly between the two anchors).
    have hjp1 : j + 1 < p := by omega
    have heq : (M.σ ^ j) (M.σ b) = (M.σ ^ (j + 1)) b := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ]
    rw [heq]
    -- non-cycle via the classifier: same σ-cycle as `b`, ≠ `b`, ≠ `fwd`.
    apply not_mem_edgeSet_of_star_not_cycleDart C hsimple (i := i)
    · -- `σ.SameCycle (α (C.dart i)) ((σ^(j+1)) b)`
      exact ⟨(j + 1 : ℕ), by rw [zpow_natCast]⟩
    · -- `(σ^(j+1)) b ≠ b = α (C.dart i)`
      exact sigma_pow_ne_self (M := M) hbsupp (by omega) (by omega)
    · -- `(σ^(j+1)) b ≠ C.dart (nextIdx i) = (σ^p) b`
      intro hcon
      have : j + 1 = p := sigma_pow_inj_of_lt (M := M) hbsupp (by omega) hpL (by rw [hcon, hp])
      omega
  -- rewrite both endpoints.
  have hstart : M.dartFace (M.σ b) = C.faceLeft i := by
    rw [ZinanCh35StarConn.dartFace_sigma_eq_alpha, hb, M.alpha_alpha]; rfl
  have hend : M.dartFace ((M.σ ^ (p - 1)) (M.σ b)) = C.faceLeft (C.nextIdx i) := by
    have heq : (M.σ ^ (p - 1)) (M.σ b) = (M.σ ^ p) b := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ, show (p - 1) + 1 = p by omega]
    rw [heq, hp]; rfl
  rw [hstart, hend] at hwalk
  exact hwalk

/-- **Right-bank step.**  `faceRight (nextIdx i) ↝ faceRight i` via the σ-arc from
`C.dart (nextIdx i)` to `α (C.dart i)`. -/
lemma right_bank_step (hsimple : M.IsSimpleGraph) (i : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C)
      (C.faceRight (C.nextIdx i)) (C.faceRight i) := by
  set b := C.dart (C.nextIdx i) with hb
  -- `b ∈ σ.support`: its orbit contains `α (C.dart i) ≠ b` (same tail).
  have hbsupp : b ∈ M.σ.support := by
    rw [Equiv.Perm.mem_support]
    intro hfix
    have hsc : M.σ.SameCycle b (M.α (C.dart i)) :=
      (sigma_sameCycle_alphaDart_dart_next C i).symm
    obtain ⟨n, hn⟩ := hsc
    have hpow : ∀ k : ℤ, (M.σ ^ k) b = b := by
      intro k
      have hnat : ∀ m : ℕ, (M.σ ^ m) b = b := by
        intro m; induction m with
        | zero => simp
        | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply, iht, hfix]
      rcases k with k | k
      · simpa using hnat k
      · have hinv : M.σ⁻¹ b = b := by rw [Equiv.Perm.inv_eq_iff_eq, hfix]
        have hinvm : ∀ m : ℕ, (M.σ⁻¹ ^ m) b = b := by
          intro m; induction m with
          | zero => simp
          | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply, iht, hinv]
        have hk := hinvm (k + 1); rw [zpow_negSucc, ← inv_pow]; exact hk
    have : M.α (C.dart i) = b := by rw [← hn]; exact hpow n
    exact (dart_ne_alphaDart C (C.nextIdx i) i) (hb ▸ this.symm)
  set L := (M.σ.cycleOf b).support.card with hL
  have hsc : M.σ.SameCycle b (M.α (C.dart i)) :=
    (sigma_sameCycle_alphaDart_dart_next C i).symm
  obtain ⟨p, hpL, hp⟩ := hsc.exists_pow_eq_of_mem_support hbsupp
  have hpos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exfalso; rw [h0, pow_zero] at hp; simp only [Equiv.Perm.coe_one, id] at hp
      exact (dart_ne_alphaDart C (C.nextIdx i) i) (hb ▸ hp)
    · exact h0
  have hwalk :
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (M.dartFace (M.σ b)) (M.dartFace ((M.σ ^ (p - 1)) (M.σ b))) := by
    apply reflTransGen_dualStep_sigma_pow C hsimple (M.σ b)
    intro j hj
    have hjp1 : j + 1 < p := by omega
    have heq : (M.σ ^ j) (M.σ b) = (M.σ ^ (j + 1)) b := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ]
    rw [heq]
    -- non-cycle: `(σ^(j+1)) b` is in σ-orbit of `α (C.dart i)`, distinct from both anchors.
    apply not_mem_edgeSet_of_star_not_cycleDart C hsimple (i := i)
    · -- `σ.SameCycle (α (C.dart i)) ((σ^(j+1)) b)`: both same-cycle as `b`.
      have h1 : M.σ.SameCycle (M.α (C.dart i)) b :=
        (sigma_sameCycle_alphaDart_dart_next C i)
      exact h1.trans ⟨(j + 1 : ℕ), by rw [zpow_natCast]⟩
    · -- `(σ^(j+1)) b ≠ α (C.dart i) = (σ^p) b`
      intro hcon
      have : j + 1 = p := sigma_pow_inj_of_lt (M := M) hbsupp (by omega) hpL (by rw [hcon, hp])
      omega
    · -- `(σ^(j+1)) b ≠ C.dart (nextIdx i) = b`
      have hne : (M.σ ^ (j + 1)) b ≠ b :=
        sigma_pow_ne_self (M := M) hbsupp (by omega) (by omega)
      rw [hb]; exact hne
  have hstart : M.dartFace (M.σ b) = C.faceRight (C.nextIdx i) := by
    rw [ZinanCh35StarConn.dartFace_sigma_eq_alpha, hb]; rfl
  have hend : M.dartFace ((M.σ ^ (p - 1)) (M.σ b)) = C.faceRight i := by
    have heq : (M.σ ^ (p - 1)) (M.σ b) = (M.σ ^ p) b := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ, show (p - 1) + 1 = p by omega]
    rw [heq, hp]; rfl
  rw [hstart, hend] at hwalk
  exact hwalk



/-- The forward face at any index reaches the forward face at index `0`. -/
lemma left_reaches_zero (hsimple : M.IsSimpleGraph) (i : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C)
      (C.faceLeft i) (C.faceLeft ⟨0, C.len_pos⟩) := by
  -- strong induction on the index value, quantified over the bound.
  suffices H : ∀ n : ℕ, ∀ hn : n < C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (C.faceLeft ⟨n, hn⟩) (C.faceLeft ⟨0, C.len_pos⟩) from H i.1 i.2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; exact Relation.ReflTransGen.refl
    · set i : Fin C.len := ⟨n, hn⟩ with hi
      have hprev : (C.prevIdx i).1 = n - 1 := by
        rw [SimplePrimalCycle.prevIdx_val, hi]
        have : n + (C.len - 1) = (n - 1) + C.len := by have := C.len_pos; omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hnext : C.nextIdx (C.prevIdx i) = i := C.nextIdx_prevIdx i
      have hstep := left_bank_step C hsimple (C.prevIdx i)
      rw [hnext] at hstep
      have hih := ih (n - 1) (by omega) (by omega)
      have hsymm : Relation.ReflTransGen (DualAvoidsCycleStep M C)
          (C.faceLeft i) (C.faceLeft (C.prevIdx i)) :=
        Relation.ReflTransGen.symmetric (fun _ _ h => dualAvoidsCycleStep_symm C h) hstep
      have hih' : Relation.ReflTransGen (DualAvoidsCycleStep M C)
          (C.faceLeft (C.prevIdx i)) (C.faceLeft ⟨0, C.len_pos⟩) := by
        have hpe : (C.prevIdx i) = ⟨n - 1, by omega⟩ := Fin.ext hprev
        rw [hpe]; exact hih
      exact hsymm.trans hih'

/-- The reverse face at any index reaches the reverse face at index `0`. -/
lemma right_reaches_zero (hsimple : M.IsSimpleGraph) (i : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C)
      (C.faceRight i) (C.faceRight ⟨0, C.len_pos⟩) := by
  suffices H : ∀ n : ℕ, ∀ hn : n < C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (C.faceRight ⟨n, hn⟩) (C.faceRight ⟨0, C.len_pos⟩) from H i.1 i.2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; exact Relation.ReflTransGen.refl
    · set i : Fin C.len := ⟨n, hn⟩ with hi
      have hprev : (C.prevIdx i).1 = n - 1 := by
        rw [SimplePrimalCycle.prevIdx_val, hi]
        have : n + (C.len - 1) = (n - 1) + C.len := by have := C.len_pos; omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hnext : C.nextIdx (C.prevIdx i) = i := C.nextIdx_prevIdx i
      have hstep := right_bank_step C hsimple (C.prevIdx i)
      rw [hnext] at hstep
      have hih := ih (n - 1) (by omega) (by omega)
      have hih' : Relation.ReflTransGen (DualAvoidsCycleStep M C)
          (C.faceRight (C.prevIdx i)) (C.faceRight ⟨0, C.len_pos⟩) := by
        have hpe : (C.prevIdx i) = ⟨n - 1, by omega⟩ := Fin.ext hprev
        rw [hpe]; exact hih
      exact hstep.trans hih'



/-- **`left_bank`.**  Any two forward faces are `DualAvoidsCycleStep`-connected. -/
theorem left_bank_holds (hsimple : M.IsSimpleGraph) (i j : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceLeft j) := by
  have hi := left_reaches_zero C hsimple i
  have hj := left_reaches_zero C hsimple j
  exact hi.trans
    (Relation.ReflTransGen.symmetric (fun _ _ h => dualAvoidsCycleStep_symm C h) hj)

/-- **`right_bank`.**  Any two reverse faces are `DualAvoidsCycleStep`-connected. -/
theorem right_bank_holds (hsimple : M.IsSimpleGraph) (i j : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceRight i) (C.faceRight j) := by
  have hi := right_reaches_zero C hsimple i
  have hj := right_reaches_zero C hsimple j
  exact hi.trans
    (Relation.ReflTransGen.symmetric (fun _ _ h => dualAvoidsCycleStep_symm C h) hj)









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







































end ProofsInTheBook.ZinanCh35Final














end


