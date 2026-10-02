-- Prove2me | Definitions.Def_P2MAssembly_Chapter35Canonical
-- name    : P2MAssembly_Chapter35Canonical
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T19:33:42.910124+00:00
-- url     : https://prove2.me/theorems/4a82128f-278d-4d36-841e-1876891cbf55
-- title:
--   Boundary alignment and canonical coloring recursion data
-- statement:
--   This part relates normalized boundary dart arcs to chord-side regions and constructs compatible side boundaries, region-coverage and edge-confinement records, and precolored-edge placements. It includes the canonical chord-branch supplier together with fan incidence, merged-face reconstruction, the deleted outer boundary, and adjusted color lists for the chordless branch. The retained chordless-oracle interface applies to near-triangulations with more than three vertices, Thomassen lists, and a chordless outer boundary; the canonical constructions assemble its branch supplier. These internal certificates do not add new parameters to the selected final theorem. This final part imports the two preceding parts and retains the original definition-module name.
-- source:
--   Representative original definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ZinanCh35BankOrient.lean#L176; https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ZinanCh35ChordResidue.lean#L164; https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ZinanCh35ChordSupplier2.lean#L579; https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ZinanCh35ChordlessOracle.lean#L244. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 39, “Five-coloring plane graphs”, pp. 277–280 (https://doi.org/10.1007/978-3-662-57265-8_39).

import Init
import Mathlib
import Mathlib.Data.Finset.Basic
import Definitions.Def_P2MAssembly_Chapter35Canonical_Part1
import Definitions.Def_P2MAssembly_Chapter35Canonical_Part2

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





































/-- **`left_right_sep`.**  No forward face reaches any reverse face avoiding the cycle.  If it
did, chaining through the two bank classes yields `faceLeft j ↝ faceRight j`, contradicting the
discharged Jordan gate `jordan_simple_cycle2_unconditional`. -/
theorem left_right_sep_holds (hsphere : M.IsSphereMap) (hsimple : M.IsSimpleGraph)
    (i j : Fin C.len) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceRight j) := by
  intro hreach
  -- `faceLeft j ↝ faceLeft i ↝ faceRight j ↝ faceRight j` (j↝j trivial), giving the forbidden pair.
  have hLj : Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft j) (C.faceLeft i) :=
    left_bank_holds C hsimple j i
  have hchain : Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft j) (C.faceRight j) :=
    hLj.trans hreach
  -- this IS `DualReachableAvoidingCycle M C (faceLeft j) (faceRight j)`.
  have hbad : DualReachableAvoidingCycle M C (C.faceLeft j) (C.faceRight j) := hchain
  exact (C.jordan_simple_cycle2_unconditional hsphere.2 hsphere.1 j) hbad



/-- **The full general simple-cycle bank theorem.**  For an arbitrary `SimplePrimalCycle` on a
sphere simple-graph map, all six fields of `SimpleCycleBankTheorem` are discharged: the count
core (`numComp = 2`, the bank orbit count, `genusSlack = 0`) unconditionally from
`ZinanCh35CycleBank`, and the three bank labels (`left_bank`, `right_bank`, `left_right_sep`)
from the σ-arc walker + the discharged Jordan gate. -/
def simpleCycleBankTheorem_holds (hsphere : M.IsSphereMap) (hsimple : M.IsSimpleGraph) :
    SimpleCycleBankTheorem M C where
  dual_numComp_two := dualAvoidsCycle_numComp_two C hsphere hsimple
  bankOrbitCount := bankCount_holds C
  slack_zero := genusSlack_cycleDualAlpha_eq_zero C hsphere
  left_bank := left_bank_holds C hsimple
  right_bank := right_bank_holds C hsimple
  left_right_sep := left_right_sep_holds C hsphere hsimple

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


noncomputable def cyclicDartArc (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < C.darts.length)
    (hp : p < C.darts.length) :
    DartArc M C (M.tail (C.darts[p]'hp))
      (M.tail (C.darts[(p + k) % C.darts.length]'(Nat.mod_lt _ (by omega)))) where
  len := k
  len_pos := hk
  arcDart j := C.darts[(p + j.1) % C.darts.length]'(Nat.mod_lt _ (by omega))
  boundary j := List.getElem_mem _
  chain j hj := by
    -- head (darts[(p+j)%L]) = tail (darts[((p+j)+1)%L]) = tail (darts[(p+(j+1))%L]).
    set L := C.darts.length with hL
    have hLpos : 0 < L := C.darts_length_pos
    have hpos : (p + (j : ℕ)) % L < L := Nat.mod_lt _ hLpos
    have hcv := C.consecutive_vertex ⟨(p + (j : ℕ)) % L, hpos⟩
    -- cyclicNext of ((p+j)%L) is (((p+j)%L)+1)%L = ((p+j)+1)%L = (p+(j+1))%L.
    have hcyc : (cyclicNext C.normalized.length_pos ⟨(p + (j : ℕ)) % L, hpos⟩ : Fin L)
        = ⟨(p + ((j : ℕ) + 1)) % L, Nat.mod_lt _ hLpos⟩ := by
      apply Fin.ext
      show ((p + (j : ℕ)) % L + 1) % L = (p + ((j : ℕ) + 1)) % L
      rw [Nat.mod_add_mod]
      congr 1
    rw [hcyc] at hcv
    -- Translate `.get` to `[…]` and conclude.
    show M.head (C.darts[(p + (j : ℕ)) % L]'_)
        = M.tail (C.darts[(p + ((j : ℕ) + 1)) % L]'_)
    rw [show (C.darts.get ⟨(p + (j : ℕ)) % L, hpos⟩) = C.darts[(p + (j : ℕ)) % L]'hpos from rfl,
      show (C.darts.get ⟨(p + ((j : ℕ) + 1)) % L, Nat.mod_lt _ hLpos⟩)
          = C.darts[(p + ((j : ℕ) + 1)) % L]'(Nat.mod_lt _ hLpos) from rfl] at hcv
    exact hcv.symm
  tail_first := by
    have hLpos : 0 < C.darts.length := C.darts_length_pos
    have heq : (p + (0 : ℕ)) % C.darts.length = p := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hp]
    show M.tail (C.darts[(p + (0 : ℕ)) % C.darts.length]'_) = M.tail (C.darts[p]'hp)
    simp only [heq]
  head_last := by
    set L := C.darts.length with hL
    have hLpos : 0 < L := C.darts_length_pos
    -- head (darts[(p+(k-1))%L]) = tail (darts[(p+k)%L]) via consecutive_vertex.
    have hpos : (p + (k - 1)) % L < L := Nat.mod_lt _ hLpos
    have hcv := C.consecutive_vertex ⟨(p + (k - 1)) % L, hpos⟩
    have hcyc : (cyclicNext C.normalized.length_pos ⟨(p + (k - 1)) % L, hpos⟩ : Fin L)
        = ⟨(p + k) % L, Nat.mod_lt _ hLpos⟩ := by
      apply Fin.ext
      show ((p + (k - 1)) % L + 1) % L = (p + k) % L
      rw [Nat.mod_add_mod]
      congr 1
      omega
    rw [hcyc] at hcv
    show M.head (C.darts[(p + ((k : ℕ) - 1)) % L]'_) = M.tail (C.darts[(p + k) % L]'_)
    rw [show (C.darts.get ⟨(p + (k - 1)) % L, hpos⟩) = C.darts[(p + (k - 1)) % L]'hpos from rfl,
      show (C.darts.get ⟨(p + k) % L, Nat.mod_lt _ hLpos⟩)
          = C.darts[(p + k) % L]'(Nat.mod_lt _ hLpos) from rfl] at hcv
    exact hcv.symm
  tail_nodup := by
    -- positions (p+i)%L (i < k ≤ L) are pairwise distinct, so darts and tails are.
    set L := C.darts.length with hL
    have hmap : (C.darts.map M.tail).Nodup := by
      simpa [BoundaryCycle.VertexNodup, C.vertices_eq] using hC
    intro i₁ i₂ htail
    have hi₁ : (i₁ : ℕ) < k := i₁.isLt
    have hi₂ : (i₂ : ℕ) < k := i₂.isLt
    have h1 : (p + (i₁ : ℕ)) % L < L := Nat.mod_lt _ C.darts_length_pos
    have h2 : (p + (i₂ : ℕ)) % L < L := Nat.mod_lt _ C.darts_length_pos
    have hdarts : C.darts[(p + (i₁ : ℕ)) % L]'h1 = C.darts[(p + (i₂ : ℕ)) % L]'h2 := by
      have hinj := List.inj_on_of_nodup_map hmap (List.getElem_mem h1) (List.getElem_mem h2)
      exact hinj htail
    have hpos_eq : (p + (i₁ : ℕ)) % L = (p + (i₂ : ℕ)) % L :=
      (C.normalized.nodup.getElem_inj_iff).mp hdarts
    -- both residues equal and both `< L` with `i < k ≤ L`: the `i`'s coincide.
    have hi₁L0 : (i₁ : ℕ) < L := lt_of_lt_of_le hi₁ (le_of_lt hkL)
    have hi₂L0 : (i₂ : ℕ) < L := lt_of_lt_of_le hi₂ (le_of_lt hkL)
    have hmodeq : Nat.ModEq L (p + (i₁ : ℕ)) (p + (i₂ : ℕ)) := hpos_eq
    have hcancel : Nat.ModEq L (i₁ : ℕ) (i₂ : ℕ) :=
      Nat.ModEq.add_left_cancel' p hmodeq
    have hi₁L : (i₁ : ℕ) % L = (i₁ : ℕ) := Nat.mod_eq_of_lt hi₁L0
    have hi₂L : (i₂ : ℕ) % L = (i₂ : ℕ) := Nat.mod_eq_of_lt hi₂L0
    apply Fin.ext
    have := hcancel
    rw [Nat.ModEq, hi₁L, hi₂L] at this
    exact this
  head_last_ne_tail := by
    set L := C.darts.length with hL
    have hmap : (C.darts.map M.tail).Nodup := by
      simpa [BoundaryCycle.VertexNodup, C.vertices_eq] using hC
    intro i htail
    -- v = tail darts[(p+k)%L]; tail darts[(p+i)%L] with i < k.  Positions distinct.
    have hi : (i : ℕ) < k := i.isLt
    have hposk : (p + k) % L < L := Nat.mod_lt _ C.darts_length_pos
    have hposi : (p + (i : ℕ)) % L < L := Nat.mod_lt _ C.darts_length_pos
    have hdarts : C.darts[(p + k) % L]'hposk = C.darts[(p + (i : ℕ)) % L]'hposi := by
      have hinj := List.inj_on_of_nodup_map hmap (List.getElem_mem hposk) (List.getElem_mem hposi)
      exact hinj htail
    have hpos_eq : (p + k) % L = (p + (i : ℕ)) % L :=
      (C.normalized.nodup.getElem_inj_iff).mp hdarts
    -- residues equal ⟹ k ≡ i [MOD L]; but i < k < L: contradiction.
    have hiltL : (i : ℕ) < L := lt_trans hi hkL
    have hmodeq : Nat.ModEq L (p + k) (p + (i : ℕ)) := hpos_eq
    have hcancel : Nat.ModEq L k (i : ℕ) := Nat.ModEq.add_left_cancel' p hmodeq
    have hkL' : k % L = k := Nat.mod_eq_of_lt hkL
    have hiL : (i : ℕ) % L = (i : ℕ) := Nat.mod_eq_of_lt hiltL
    rw [Nat.ModEq, hkL', hiL] at hcancel
    omega



@[simp] lemma cyclicDartArc_arcDart (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < C.darts.length) (hp : p < C.darts.length)
    (j : Fin k) :
    (cyclicDartArc C hC p k hk hkL hp).arcDart j
      = C.darts[(p + j.1) % C.darts.length]'(Nat.mod_lt _ (by omega)) := rfl

end BoundaryCycle



namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

/-- The position of a boundary vertex on the cyclic dart list (as the tail of a
listed dart), as a single existential over `Fin`. -/
lemma exists_pos_of_isBoundaryVertex (C : BoundaryCycle M f) {a : M.Vertex}
    (ha : C.IsBoundaryVertex a) :
    ∃ p : Fin C.darts.length, M.tail (C.darts[p.1]'p.2) = a := by
  have ha' : a ∈ C.darts.map M.tail := by
    simpa [BoundaryCycle.IsBoundaryVertex, C.vertices_eq] using ha
  rw [List.mem_iff_getElem] at ha'
  obtain ⟨p, hp, hget⟩ := ha'
  rw [List.length_map] at hp
  refine ⟨⟨p, hp⟩, ?_⟩
  rwa [List.getElem_map] at hget

/-- **The boundary arc of a non-boundary edge.**  From two distinct boundary
vertices `a, b` with `s(a, b)` not a boundary edge, the forward cyclic dart run
from `a` to `b` is a `DartArc … a b` of length `≥ 2`. -/
noncomputable def dartArcOfNonBoundaryEdge (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {a b : M.Vertex} (hab : a ≠ b) (ha : C.IsBoundaryVertex a) (hb : C.IsBoundaryVertex b)
    (hnbe : ¬ C.IsBoundaryEdge s(a, b)) :
    { A : DartArc M C a b // 2 ≤ A.len } := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  -- positions of a, b (extracted as data via choice).
  set paF := (C.exists_pos_of_isBoundaryVertex ha).choose with hpaF
  have hpaeq0 := (C.exists_pos_of_isBoundaryVertex ha).choose_spec
  set pbF := (C.exists_pos_of_isBoundaryVertex hb).choose with hpbF
  have hpbeq0 := (C.exists_pos_of_isBoundaryVertex hb).choose_spec
  set pa := paF.1 with hpaval
  set pb := pbF.1 with hpbval
  have hpa : pa < C.darts.length := paF.2
  have hpb : pb < C.darts.length := pbF.2
  have hpaeq : M.tail (C.darts[pa]'hpa) = a := hpaeq0
  have hpbeq : M.tail (C.darts[pb]'hpb) = b := hpbeq0
  -- forward cyclic distance from pa to pb.
  set k := (pb + L - pa) % L with hk
  have hkL : k < L := Nat.mod_lt _ hLpos
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · -- k = 0 ⟹ L ∣ (pb+L-pa) ⟹ (since 0 < pb+L-pa < 2L) pb = pa ⟹ a = b.
      exfalso
      have hmod0 : (pb + L - pa) % L = 0 := by rw [← hk]; exact h0
      have hdvd : L ∣ (pb + L - pa) := Nat.dvd_of_mod_eq_zero hmod0
      obtain ⟨m, hm⟩ := hdvd
      have hpapb : pa = pb := by
        have hb1 : pb + L - pa < 2 * L := by omega
        have hb2 : 0 < pb + L - pa := by omega
        -- L*m = pb+L-pa, 0 < L*m < 2L ⟹ m = 1 ⟹ pb+L-pa = L ⟹ pa = pb.
        have hm1 : m = 1 := by nlinarith [hm, hb1, hb2, hLpos]
        rw [hm1, Nat.mul_one] at hm; omega
      apply hab
      have hgeteq : C.darts.get ⟨pa, hpa⟩ = C.darts.get ⟨pb, hpb⟩ := by
        congr 1; exact Fin.ext hpapb
      calc a = M.tail (C.darts[pa]'hpa) := hpaeq.symm
        _ = M.tail (C.darts.get ⟨pa, hpa⟩) := rfl
        _ = M.tail (C.darts.get ⟨pb, hpb⟩) := by rw [hgeteq]
        _ = M.tail (C.darts[pb]'hpb) := rfl
        _ = b := hpbeq
    · exact h0
  -- endpoints: tail darts[pa] = a, tail darts[(pa+k)%L] = b.
  have hend : (pa + k) % L = pb := by
    rw [hk]
    -- (pa + (pb+L-pa)%L) % L = (pa + (pb+L-pa)) % L = (pb+L) % L = pb.
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L)]
    rw [← Nat.add_mod]
    have h1 : pa + (pb + L - pa) = pb + L := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hpb]
  -- length k ≥ 2: if k = 1 then darts[pa] has head b, so s(a,b) is a boundary edge.
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hlt' : k < 2 := Nat.lt_of_not_le hlt
    have hk1 : k = 1 := by omega
    -- tail darts[(pa+1)%L] = head darts[pa] by consecutive_vertex; (pa+1)%L = (pa+k)%L = pb.
    have hcv := C.consecutive_vertex ⟨pa, hpa⟩
    have hcyc : (cyclicNext C.normalized.length_pos ⟨pa, hpa⟩ : Fin L)
        = ⟨pb, hpb⟩ := by
      apply Fin.ext
      show (pa + 1) % L = pb
      have hkk : (pa + k) % L = pb := hend
      rw [hk1] at hkk; exact hkk
    rw [hcyc] at hcv
    -- hcv : tail darts[pb] = head darts[pa].  So s(a,b) = dartEdge darts[pa] ∈ edges.
    apply hnbe
    show s(a, b) ∈ C.edges
    rw [C.edges_eq]
    have hge : C.darts.get ⟨pa, hpa⟩ = C.darts[pa]'hpa := rfl
    have hgb : C.darts.get ⟨pb, hpb⟩ = C.darts[pb]'hpb := rfl
    rw [hge, hgb] at hcv
    -- M.dartEdge (darts[pa]) = s(tail darts[pa], head darts[pa]) = s(a, b).
    have hedge2 : M.dartEdge (C.darts[pa]'hpa) = s(a, b) := by
      show s(M.tail (C.darts[pa]'hpa), M.head (C.darts[pa]'hpa)) = s(a, b)
      rw [hpaeq, ← hcv, hpbeq]
    rw [← hedge2]
    exact List.mem_map_of_mem (List.getElem_mem hpa)
  -- The arc's head endpoint is `tail darts[(pa+k)%L] = tail darts[pb] = b`.
  have hbend : M.tail (C.darts[(pa + k) % C.darts.length]'(Nat.mod_lt _ hLpos)) = b := by
    have hcongr : C.darts.get ⟨(pa + k) % C.darts.length, Nat.mod_lt _ hLpos⟩
        = C.darts.get ⟨pb, hpb⟩ := by
      congr 1
      apply Fin.ext
      show (pa + k) % C.darts.length = pb
      simpa [hL] using hend
    have h1 : C.darts[(pa + k) % C.darts.length]'(Nat.mod_lt _ hLpos)
        = C.darts.get ⟨(pa + k) % C.darts.length, Nat.mod_lt _ hLpos⟩ := rfl
    have h2 : C.darts[pb]'hpb = C.darts.get ⟨pb, hpb⟩ := rfl
    rw [h1, hcongr, ← h2]; exact hpbeq
  -- Rewrite the goal's endpoints `a`, `b` back to the tail expressions and bundle.
  rw [show a = M.tail (C.darts[pa]'hpa) from hpaeq.symm,
      show b = M.tail (C.darts[(pa + k) % C.darts.length]'(Nat.mod_lt _ hLpos)) from hbend.symm]
  exact ⟨C.cyclicDartArc hC pa k hkpos hkL hpa, hk2⟩

end BoundaryCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- **Chord-cycle datum.**  The exact bundle `separates_closed` consumes: a simple
primal cycle made of the chord edge `s(u,v)` plus a boundary arc (`hsub`), with an
index `i₀` whose two incident faces are the two chord-dart faces. -/
structure ChordCycleData {u v : M.Vertex} (h : hNT.outerCycle.Chord u v) where
  /-- The chord ∪ arc simple primal cycle. -/
  C : CombMap.SimplePrimalCycle M
  /-- Every cycle edge is the chord or a boundary edge. -/
  hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e
  /-- The chord index. -/
  i₀ : Fin C.len
  /-- The left face at `i₀` is the chord-dart face. -/
  hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h)
  /-- The right face at `i₀` is the reverse-chord-dart face. -/
  hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))

variable {u v : M.Vertex}

/-- **The chord-cycle datum exists.**  Built from the boundary arc between the two
endpoints of the chord dart `c₀ := hNT.chordDart h`, with `c₀` placed at index `0`
of `ofDartArc`.  Then `dart 0 = c₀`, so the two `i₀ = 0` faces are *definitionally*
the chord-dart faces. -/
noncomputable def chordCycleData (h : hNT.outerCycle.Chord u v) :
    hNT.ChordCycleData h := by
  classical
  -- The chord dart and its (boundary) endpoints.  We keep `M.tail c₀`/`M.head c₀`
  -- inline (no `set`) to avoid reverting let-bound variables in rewrites.
  set c₀ := hNT.chordDart h with hc₀
  -- c₀ has edge s(u, v); its endpoints are the two boundary chord endpoints.
  have hedge : M.dartEdge c₀ = s(u, v) := hNT.chordDart_edge h
  have hxy_edge : s(M.tail c₀, M.head c₀) = s(u, v) := hedge
  -- the endpoints are distinct and both boundary vertices.
  have hxy_ne : M.tail c₀ ≠ M.head c₀ := by
    intro hcontra
    have h1 : s(M.head c₀, M.head c₀) = s(u, v) := hcontra ▸ hxy_edge
    have huv : u = v := by
      rcases Sym2.eq_iff.mp h1.symm with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · rw [hl, hr]
      · rw [hl, hr]
    exact h.endpoints_ne huv
  have hx_bv : hNT.outerCycle.IsBoundaryVertex (M.tail c₀) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · rw [hxu]; exact h.left_boundary
    · rw [hxv]; exact h.right_boundary
  have hy_bv : hNT.outerCycle.IsBoundaryVertex (M.head c₀) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨_, hyv⟩ | ⟨_, hyu⟩
    · rw [hyv]; exact h.right_boundary
    · rw [hyu]; exact h.left_boundary
  -- s(head, tail) = s(tail, head) = s(u, v) is not a boundary edge.
  have hnbe : ¬ hNT.outerCycle.IsBoundaryEdge s(M.head c₀, M.tail c₀) := by
    rw [show (s(M.head c₀, M.tail c₀) : Sym2 M.Vertex) = s(M.tail c₀, M.head c₀) from Sym2.eq_swap,
      hxy_edge]
    exact h.not_boundary_edge
  -- Build the boundary arc from `head c₀` to `tail c₀` (so c₀ : tail→...→head closes it).
  obtain ⟨A, hAlen⟩ := hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    (Ne.symm hxy_ne) hy_bv hx_bv hnbe
  -- The chord ∪ arc cycle: dart 0 = c₀.  ofDartArc needs tail c₀ = (arc's `v`-end),
  -- head c₀ = (arc's `u`-end); the arc `A : DartArc … (head c₀) (tail c₀)` matches.
  have hc_tail : M.tail c₀ = M.tail c₀ := rfl
  have hc_head : M.head c₀ = M.head c₀ := rfl
  -- index 0 (the chord dart) of the chord∪arc cycle.  `dart 0 = c₀` definitionally.
  have hi0 : (0 : ℕ) < (SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).len :=
    (SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).len_pos
  have hdart0 : (SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).dart ⟨0, hi0⟩ = c₀ := by
    show SimplePrimalCycle.chordArcDart A c₀ ⟨0, hi0⟩ = c₀
    exact SimplePrimalCycle.chordArcDart_zero A c₀
  refine
    { C := SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head
      hsub := ?_
      i₀ := ⟨0, hi0⟩
      hleft := ?_
      hright := ?_ }
  · -- hsub: every cycle edge is the chord or a boundary edge.
    intro e he
    rw [SimplePrimalCycle.mem_edgeSet_iff] at he
    obtain ⟨i, hi⟩ := he
    rw [hi]
    -- edge i = dartEdge (dart i); dart i is either c₀ (i = 0) or an arc dart.
    have hedge_i : (SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).edge i
        = M.dartEdge ((SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).dart i) := rfl
    rw [hedge_i, SimplePrimalCycle.ofDartArc_dart]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · -- chord edge.
      left
      rw [SimplePrimalCycle.chordArcDart_zero]
      exact hedge
    · -- arc dart: lies on the outer cycle, so its edge is a boundary edge.
      right
      rw [SimplePrimalCycle.chordArcDart_succ]
      show M.dartEdge (A.arcDart i') ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]
      exact List.mem_map_of_mem (A.boundary i')
  · -- hleft: faceLeft 0 = dartFace (dart 0) = dartFace c₀ = dartFace (chordDart h).
    show M.dartFace ((SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).dart ⟨0, hi0⟩)
        = M.dartFace (hNT.chordDart h)
    rw [hdart0]
  · -- hright: faceRight 0 = dartFace (α (dart 0)) = dartFace (α c₀) = dartFace (α (chordDart h)).
    show M.dartFace (M.α ((SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).dart ⟨0, hi0⟩))
        = M.dartFace (M.α (hNT.chordDart h))
    rw [hdart0]



/-- **The chord separates, from a chord-cycle datum.**  Composes `ChordCycleData`
with `separates_closed` (the connectivity-gate-discharged separation). -/
theorem separates_of_chord (data : hNT.ChordSplitData u v)
    (cc : hNT.ChordCycleData data.chord) : data.Separates :=
  hNT.separates_closed data cc.C cc.hsub cc.i₀ cc.hleft cc.hright

/-- **The chord separates, unconditionally on the chord-cycle datum** (built
internally). -/
theorem separates_of_chordSplitData (data : hNT.ChordSplitData u v) :
    data.Separates :=
  hNT.separates_of_chord data (hNT.chordCycleData data.chord)

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



/-- If a dart's face is the outer face, its reverse's face is **not** the outer face: an edge
cannot have both of its darts on the simple outer boundary cycle (that would force a length-2
boundary, contradicting `outer_len`). -/
theorem alpha_dartFace_ne_outer_of_outer {e : D}
    (hNT : NearTriangulation M) (he : M.dartFace e = hNT.outerFace) :
    M.dartFace (M.α e) ≠ hNT.outerFace := by
  intro hαe
  -- both `e` and `α e` are boundary darts.
  have he_mem : e ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff e).2 he
  have hαe_mem : M.α e ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff (M.α e)).2 hαe
  -- `φ e` is a boundary dart (same outer face), with `tail (φ e) = head e = tail (α e)`.
  have hφe_mem : M.φ e ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ e) = hNT.outerFace
    rw [M.dartFace_phi]; exact he
  have htail_eq : M.tail (M.φ e) = M.tail (M.α e) := by
    rw [M.tail_phi, M.tail_alpha]
  -- two boundary darts with the same tail are equal: `φ e = α e`.
  have hφα : M.φ e = M.α e :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφe_mem hαe_mem htail_eq
  -- Then `φ (φ e) = φ (α e)`, whose tail is `head (α e) = tail e = tail e`.
  have htail2 : M.tail (M.φ (M.φ e)) = M.tail e := by
    rw [hφα, M.tail_phi, M.head_alpha]
  -- `φ² e` is a boundary dart with the same tail as `e`, hence `φ² e = e`.
  have hφ2_mem : M.φ (M.φ e) ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ (M.φ e)) = hNT.outerFace
    rw [M.dartFace_phi, M.dartFace_phi]; exact he
  have hφ2 : M.φ (M.φ e) = e :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφ2_mem he_mem htail2
  -- So the outer-face orbit has support card 2, i.e. `faceLen outerFace = 2 < 3`.
  have hφ : M.φ e ≠ e := phi_ne_self_of_isSimpleGraph M hNT.simpleGraph e
  have hcard2 : (M.φ.cycleOf e).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [he, hcard2] at hsupport; exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega



/-- **Bridge 2 (`OuterDartArc₁`), conditional on the two planar bridges.**  Clean-3 conditional on
exactly `Separates`, `BoundedFacePartition`, and `SideRegionInterChordEnds` (the latter is Bridge 1,
proved/isolated separately; the prompt sanctions stating Bridge 2 conditional on it). -/
theorem outerDartArc₁_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data) :
    OuterDartArc₁ data := by
  intro e hchord hface htail hhead
  -- The reverse inner face is non-outer.
  have hαe_not_outer : M.dartFace (M.α e) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer hNT hface
  -- Partition it into side₁ or side₂.
  rcases hpart hαe_not_outer with h₁ | h₂
  · exact h₁
  · -- `dartFace (α e) ∈ side₂`: derive `e = chord`, contradiction.
    exfalso
    -- `α e` is a non-chord side₂ face dart.
    have hαe_chord : M.dartEdge (M.α e) ≠ s(u, v) := by
      rw [M.dartEdge_alpha]; exact hchord
    -- both endpoints of `α e` are in `sideRegion₂`.
    obtain ⟨htail₂, hhead₂⟩ :=
      endpoints_mem_sideRegion₂_of_face data hsep hαe_chord h₂
    -- `tail (α e) = head e`, `head (α e) = tail e`.
    rw [M.tail_alpha] at htail₂
    rw [M.head_alpha] at hhead₂
    -- so both endpoints of `e` are in `sideRegion₂`; combine with `sideRegion₁`.
    have htchord : M.tail e = u ∨ M.tail e = v := hinter htail hhead₂
    have hhchord : M.head e = u ∨ M.head e = v := hinter hhead htail₂
    exact hchord (edge_eq_chord_of_endpoints_chordEnds data htchord hhchord)

























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

/-- **`BoundedFacePartition` is UNCONDITIONAL** — the coverage atom is discharged
(`outerDualNumCompTwo_holds`). -/
theorem boundedFacePartition_uncond (data : hNT.ChordSplitData u v) :
    BoundedFacePartition data :=
  boundedFacePartition_via_numComp data (outerDualNumCompTwo_holds hNT)

/-- **`OuterDartArc₁` is UNCONDITIONAL** (given the chord split + `Separates`): both its bridges
(`BoundedFacePartition` from the coverage atom, `SideRegionInterChordEnds` from σ-star) are proven. -/
theorem outerDartArc₁_uncond (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    OuterDartArc₁ data :=
  outerDartArc₁_holds data hsep (boundedFacePartition_uncond data)
    (sideRegionInterChordEnds_holds data hsep)

/-- **The corrected bounded `edge_core` is UNCONDITIONAL** (given the chord split + `Separates`):
both bridges are now proven, so the formerly-residual `edge_core` field of `Side₁StarConfinement`
is dischargeable.  Stated via the landed `edge_core_holds` shape. -/
theorem edge_core_uncond (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (houter : M.dartFace e ≠ hNT.outerFace)
    (htail : M.tail e ∈ sideRegion₁ data) (hhead : M.head e ∈ sideRegion₁ data) :
    M.dartFace e ∈ data.side₁ :=
  edge_core_holds data hsep (boundedFacePartition_uncond data)
    (sideRegionInterChordEnds_holds data hsep) hchord houter htail hhead

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



/-- **The chord-arc bank-orientation datum.**  The second listed boundary arc `path₂` is the
side-2 boundary arc: every strictly-internal vertex of `path₂` lies in the side-2 region.

This is the weakest honest orientation statement the direct `oppArc_star_core` route needs; in
the current `ChordSplitData` layer it is a free input (reversing `data.chord` swaps
`side₁ ↔ side₂` while fixing `path₂`, flipping its truth value), so it is isolated here rather
than faked. -/
structure ChordArcBankOrientation (data : hNT.ChordSplitData u v) : Prop where
  /-- A strictly-internal vertex of the opposite boundary arc `path₂` is in the side-2 region. -/
  path₂_internal_mem_sideRegion₂ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices → w ∈ sideRegion₂ data



/-- **The opposite-arc vertex-star confinement, via the direct route.**  Conditional on the single
bank-orientation datum, every dart `d` tailed at a `path₂`-internal vertex `w` is the chord dart,
or its face is outside `side₁` and it is not a side-1 boundary dart. -/
theorem oppArc_star_core_direct (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hbank : ChordArcBankOrientation data) {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) (d : D) (htail : M.tail d = w) :
    d = data.dart ∨
      (M.dartFace d ∉ data.side₁ ∧
        ¬ (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁)) := by
  by_cases hd : d = data.dart
  · exact Or.inl hd
  · right
    -- `w` lies in the side-2 region (bank datum) and is `≠ u, v` (path₂-internal).
    have hw₂ : w ∈ sideRegion₂ data := hbank.path₂_internal_mem_sideRegion₂ hw
    -- `path₂ : BoundaryPath v u`, so `_ne_start` gives `≠ v` and `_ne_end` gives `≠ u`.
    have hw_ne_v : w ≠ v := data.arc.path₂.internalVertex_ne_start hw
    have hw_ne_u : w ≠ u := data.arc.path₂.internalVertex_ne_end hw
    -- Hence `w ∉ sideRegion₁`: otherwise it is a chord endpoint, contradicting `≠ u, v`.
    have no_sideRegion₁ : w ∉ sideRegion₁ data := by
      intro hw₁
      rcases sideRegionInterChordEnds_holds data hsep hw₁ hw₂ with h | h
      · exact hw_ne_u h
      · exact hw_ne_v h
    refine ⟨?_, ?_⟩
    · -- Conjunct 1: if `dartFace d ∈ side₁`, then `d` is a kept inner side-1 dart, so
      -- `w ∈ sideRegion₁` — contradiction.
      intro hface1
      exact no_sideRegion₁ (mem_sideRegion₁_of_star_side₁ data htail hd hface1)
    · -- Conjunct 2: if `d` is an outer dart with reverse face in `side₁`, it is a kept side-1
      -- boundary dart, so `w ∈ sideRegion₁` — contradiction.
      rintro ⟨hd_outer, hα_side1⟩
      exact no_sideRegion₁ (mem_sideRegion₁_of_star_outerArc₁ data htail hd hd_outer hα_side1)



/-- **`Side₁StarConfinement`, discharged conditional on the single bank-orientation datum.**

* The `edge_core` field is **unconditional** clean-3 (`edge_core_uncond`).
* The `oppArc_star_core` field is discharged via the direct R7 route, conditional **only** on the
  minimal `ChordArcBankOrientation` datum (the one genuinely-free orientation fact; see the module
  header for why it is not derivable from the bare `ChordSplitData`).

This completes the side-1 confinement modulo that single bank-orientation input. -/
theorem side₁StarConfinement_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hbank : ChordArcBankOrientation data) :
    Side₁StarConfinement data where
  edge_core := fun {e} hchord houter htail hhead =>
    edge_core_uncond data hsep hchord houter htail hhead
  oppArc_star_core := fun {w} hw d htail =>
    oppArc_star_core_direct data hsep hbank hw d htail

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

/-- The explicit `List D` of a `DartArc`'s darts, `[arcDart 0, …, arcDart (len-1)]`. -/
def _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.dartList (A : DartArc M C a b) : List D :=
  (List.finRange A.len).map A.arcDart

@[simp] lemma _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.dartList_length
    (A : DartArc M C a b) : A.dartList.length = A.len := by
  simp [DartArc.dartList]

lemma _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.dartList_ne_nil
    (A : DartArc M C a b) : A.dartList ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, DartArc.dartList_length]; exact A.len_pos

lemma _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.dartList_getElem
    (A : DartArc M C a b) (j : ℕ) (hj : j < A.len) :
    A.dartList[j]'(by rw [DartArc.dartList_length]; exact hj) = A.arcDart ⟨j, hj⟩ := by
  simp only [DartArc.dartList, List.getElem_map, List.getElem_finRange]
  congr 1

lemma _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.mem_dartList
    (A : DartArc M C a b) {d : D} (hd : d ∈ A.dartList) :
    ∃ i : Fin A.len, A.arcDart i = d := by
  rw [DartArc.dartList, List.mem_map] at hd
  obtain ⟨i, _, hi⟩ := hd
  exact ⟨i, hi⟩

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

/-- **The bank-route per-dart bridge.**  If `e` is a non-chord boundary dart whose *reverse* face
lies in `side₂`, then `tail e ∈ sideRegion₂`.

Apply `endpoints_mem_sideRegion₂_of_face` to `M.α e`: its face is `dartFace (M.α e) ∈ side₂`, its
edge is non-chord (same edge as `e`), so both its endpoints — in particular `head (M.α e) = tail
e` — lie in `sideRegion₂`. -/
theorem dartRun_tail_mem_sideRegion₂_of_face (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace (M.α e) ∈ data.side₂) :
    M.tail e ∈ sideRegion₂ data := by
  have hchord' : M.dartEdge (M.α e) ≠ s(u, v) := by rwa [M.dartEdge_alpha]
  obtain ⟨_, hhead⟩ := endpoints_mem_sideRegion₂_of_face data hsep hchord' hface
  -- head (α e) = tail e.
  rwa [M.head_alpha] at hhead

/-- Symmetric variant: the *forward* face in `side₂` gives the **head** in `sideRegion₂`. -/
theorem dartRun_head_mem_sideRegion₂_of_face (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace (M.α e) ∈ data.side₂) :
    M.head e ∈ sideRegion₂ data := by
  have hchord' : M.dartEdge (M.α e) ≠ s(u, v) := by rwa [M.dartEdge_alpha]
  obtain ⟨htail, _⟩ := endpoints_mem_sideRegion₂_of_face data hsep hchord' hface
  rwa [M.tail_alpha] at htail

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



/-- **The chord-arc bank-orientation datum (side-2 mirror).**  The first listed boundary arc
`path₁` is the side-1 boundary arc: every strictly-internal vertex of `path₁` lies in the side-1
region.  Symmetric counterpart of `ZinanCh35Side1Confine.ChordArcBankOrientation`'s
`path₂_internal_mem_sideRegion₂`; isolated here rather than faked, for the same reason. -/
structure ChordArcBankOrientation (data : hNT.ChordSplitData u v) : Prop where
  /-- A strictly-internal vertex of the boundary arc `path₁` is in the side-1 region. -/
  path₁_internal_mem_sideRegion₁ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₁.internalVertices → w ∈ sideRegion₁ data



/-- **Both endpoints of a non-chord side-1 face-dart are in `sideRegion₁`.**  Mirror of
`endpoints_mem_sideRegion₂_of_face` with the side roles swapped: `e` is a side-1 face-dart, hence in
`keptSet₁` (it is not the side-1 seam dart `dart`, since that has chord edge), so its tail is in the
region; the `α`-closure of `keptSet₁` puts `head e = tail (α e)` in the region too. -/
theorem endpoints_mem_sideRegion₁_of_face (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace e ∈ data.side₁) :
    M.tail e ∈ sideRegion₁ data ∧ M.head e ∈ sideRegion₁ data := by
  -- `e ≠ dart` (else its edge would be the chord).
  have hne : e ≠ data.dart := by
    intro h; exact hchord (by rw [h]; exact hNT.chordDart_edge data.chord)
  -- `e ∈ sideDarts₁ ⊆ keptSet₁`.
  have hkept : e ∈ data.keptSet₁ := by
    refine ⟨Or.inl hface, ?_⟩
    simp only [Set.mem_singleton_iff]; exact hne
  have htail : M.tail e ∈ sideRegion₁ data :=
    ⟨e, (data.mem_keptDel₁_iff e).2 hkept, rfl⟩
  -- head `e = tail (α e)`; `α e ∈ keptSet₁` by the `α`-closure.
  have hkeptα : M.α e ∈ data.keptSet₁ := (data.mem_keptSet₁_alpha_iff hsep e).2 hkept
  have hhead : M.head e ∈ sideRegion₁ data :=
    ⟨M.α e, (data.mem_keptDel₁_iff (M.α e)).2 hkeptα, rfl⟩
  exact ⟨htail, hhead⟩



/-- **The corrected (bounded) side-2 `edge_core`.**  For a non-chord, bounded dart `e`
(`dartFace e ≠ outerFace`) whose two endpoints are both in `sideRegion₂`, the face of `e` lies in
`side₂`.  Conditional on exactly the two proven side-symmetric bridges
(`BoundedFacePartition` + `SideRegionInterChordEnds`).  Mirror of `edge_core_holds`. -/
theorem edge_core₂_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (houter : M.dartFace e ≠ hNT.outerFace)
    (htail : M.tail e ∈ sideRegion₂ data) (hhead : M.head e ∈ sideRegion₂ data) :
    M.dartFace e ∈ data.side₂ := by
  rcases hpart houter with hside₁ | hside₂
  · -- `dartFace e ∈ side₁`: derive `e = chord`, contradiction.
    exfalso
    obtain ⟨htail₁, hhead₁⟩ := endpoints_mem_sideRegion₁_of_face data hsep hchord hside₁
    -- both endpoints are in both regions ⟹ both are chord ends.
    have htchord : M.tail e = u ∨ M.tail e = v := hinter htail₁ htail
    have hhchord : M.head e = u ∨ M.head e = v := hinter hhead₁ hhead
    exact hchord (edge_eq_chord_of_endpoints_chordEnds data htchord hhchord)
  · exact hside₂



/-- **The side-2 outer-dart route (`OuterDartArc₂`).**  Mirror of `outerDartArc₁_holds`: an outer
dart whose two endpoints are both in `sideRegion₂` has its reverse face in `side₂`.  Conditional on
the two proven side-symmetric bridges. -/
theorem outerDartArc₂_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace e = hNT.outerFace)
    (htail : M.tail e ∈ sideRegion₂ data) (hhead : M.head e ∈ sideRegion₂ data) :
    M.dartFace (M.α e) ∈ data.side₂ := by
  -- The reverse inner face is non-outer.
  have hαe_not_outer : M.dartFace (M.α e) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer hNT hface
  -- Partition it into side₁ or side₂.
  rcases hpart hαe_not_outer with h₁ | h₂
  · -- `dartFace (α e) ∈ side₁`: derive `e = chord`, contradiction.
    exfalso
    -- `α e` is a non-chord side₁ face dart.
    have hαe_chord : M.dartEdge (M.α e) ≠ s(u, v) := by
      rw [M.dartEdge_alpha]; exact hchord
    -- both endpoints of `α e` are in `sideRegion₁`.
    obtain ⟨htail₁, hhead₁⟩ :=
      endpoints_mem_sideRegion₁_of_face data hsep hαe_chord h₁
    -- `tail (α e) = head e`, `head (α e) = tail e`.
    rw [M.tail_alpha] at htail₁
    rw [M.head_alpha] at hhead₁
    -- so both endpoints of `e` are in `sideRegion₁`; combine with `sideRegion₂`.
    have htchord : M.tail e = u ∨ M.tail e = v := hinter hhead₁ htail
    have hhchord : M.head e = u ∨ M.head e = v := hinter htail₁ hhead
    exact hchord (edge_eq_chord_of_endpoints_chordEnds data htchord hhchord)
  · exact h₂



/-- **The side-2 region edge-confinement field, from the two bridges.**  Mirror of
`Side₁SchoenfliesConfinement.edge_confined`: an ambient edge `e` whose two endpoints are both in
`sideRegion₂` is either represented in the side-2 carve (`e ∉ keptDel₂ ∧ α e ∉ keptDel₂`) or is the
chord.  Case-splits on whether `e` is an outer dart: a bounded dart is kept via the bounded
`edge_core₂`; an outer dart via the `outerDartArc₂` route.  Conditional on exactly the two proven
side-symmetric bridges. -/
theorem edge_confined₂_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data) :
    ∀ {e : D},
      M.tail e ∈ sideRegion₂ data →
      M.head e ∈ sideRegion₂ data →
        ((e ∉ data.keptDel₂ ∧ M.α e ∉ data.keptDel₂) ∨ M.dartEdge e = s(u, v)) := by
  intro e htail hhead
  by_cases hchord : M.dartEdge e = s(u, v)
  · exact Or.inr hchord
  · -- non-chord: split on whether `e` is an outer dart.
    left
    -- `e ≠ α dart` (the side-2 seam, else `dartEdge e = dartEdge (α dart) = s(u, v)`).
    have hne : e ≠ M.α data.dart := by
      intro h; exact hchord (by rw [h]; exact alpha_dart_edge data)
    -- In both cases we produce `e ∈ keptSet₂`, then close under `α`.
    have hkept : e ∈ data.keptSet₂ := by
      by_cases hof : M.dartFace e = hNT.outerFace
      · -- outer dart: kept via `outerArc₂` (face = outerFace, reverse face ∈ side₂).
        have hrev : M.dartFace (M.α e) ∈ data.side₂ :=
          outerDartArc₂_holds data hsep hpart hinter hchord hof htail hhead
        refine ⟨Or.inr ⟨hof, hrev⟩, ?_⟩
        simp only [Set.mem_singleton_iff]; exact hne
      · -- bounded dart: the bounded `edge_core₂` gives `dartFace e ∈ side₂`, hence `∈ sideDarts₂`.
        have hface : M.dartFace e ∈ data.side₂ :=
          edge_core₂_holds data hsep hpart hinter hchord hof htail hhead
        refine ⟨Or.inl hface, ?_⟩
        simp only [Set.mem_singleton_iff]; exact hne
    refine ⟨?_, ?_⟩
    · rw [data.mem_keptDel₂_iff]; exact hkept
    · rw [data.mem_keptDel₂_iff]
      exact (data.mem_keptSet₂_alpha_iff hsep e).2 hkept



/-- **The opposite-arc omission, via the direct route.**  Conditional on the symmetric
bank-orientation datum, a strictly-internal vertex of the opposite boundary arc `path₁` is omitted by
side 2 (`w ∉ sideRegion₂ data`).  Mirror of `oppArc_star_core_direct`. -/
theorem oppArcStarSeed₂_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hbank : ChordArcBankOrientation data) {w : M.Vertex}
    (hw : w ∈ data.arc.path₁.internalVertices) :
    w ∉ sideRegion₂ data := by
  intro hw₂
  -- `w` lies in the side-1 region (bank datum) and is `≠ u, v` (path₁-internal).
  have hw₁ : w ∈ sideRegion₁ data := hbank.path₁_internal_mem_sideRegion₁ hw
  -- `path₁ : BoundaryPath u v`, so `_ne_start` gives `≠ u` and `_ne_end` gives `≠ v`.
  have hw_ne_u : w ≠ u := data.arc.path₁.internalVertex_ne_start hw
  have hw_ne_v : w ≠ v := data.arc.path₁.internalVertex_ne_end hw
  -- a vertex in both side regions is a chord end — contradicting `≠ u, v`.
  rcases sideRegionInterChordEnds_holds data hsep hw₁ hw₂ with h | h
  · exact hw_ne_u h
  · exact hw_ne_v h



/-- **`Side₂SchoenfliesConfinementInput`, discharged conditional on the single bank-orientation
datum.**  The mirror of `ZinanCh35Side1Confine.side₁StarConfinement_holds` for the side-2
confinement bundle.

* The `edge_core₂` field is discharged via the two proven side-symmetric bridges
  (`boundedFacePartition_uncond` + `sideRegionInterChordEnds_holds`, both UNCONDITIONAL given the
  chord split + `Separates`), instantiated with the side roles swapped.
* The `oppArcStarSeed₂` field is discharged via the direct route, conditional **only** on the
  minimal `ChordArcBankOrientation` datum (the symmetric mirror of side 1's bank datum).

This completes the side-2 confinement input modulo that single bank-orientation input — the missing
half of the `ChordBranchSupplier`'s chord branch. -/
theorem side₂SchoenfliesConfinementInput_holds (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (hbank : ChordArcBankOrientation data) :
    Side₂SchoenfliesConfinementInput data hsep where
  oppArcStarSeed₂ := fun {w} hw =>
    oppArcStarSeed₂_holds data hsep hbank hw
  edge_core₂ := fun {e} htail hhead =>
    edge_confined₂_holds data hsep (boundedFacePartition_uncond data)
      (sideRegionInterChordEnds_holds data hsep) htail hhead





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

















/-- **The joint arc↔side identification.**  Both boundary arcs bound their own side: every
`path₁`-internal vertex is in `sideRegion₁` and every `path₂`-internal vertex is in `sideRegion₂`.
This is the single discrete-Jordan labelling datum behind *both* confinements. -/
structure ArcSideIdentification (data : hNT.ChordSplitData u v) : Prop where
  /-- `path₁` bounds side 1. -/
  path₁_mem_sideRegion₁ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₁.internalVertices → w ∈ sideRegion₁ data
  /-- `path₂` bounds side 2. -/
  path₂_mem_sideRegion₂ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices → w ∈ sideRegion₂ data





/-- **`Side₁StarConfinement` from the joint arc↔side identification.** -/
theorem side₁StarConfinement_of_arcSide (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hid : ArcSideIdentification data) :
    ZinanCh35Schoenflies.Side₁StarConfinement data :=
  ZinanCh35Side1Confine.side₁StarConfinement_holds data hsep
    ⟨fun hw => hid.path₂_mem_sideRegion₂ hw⟩

/-- **`Side₂SchoenfliesConfinementInput` from the joint arc↔side identification.** -/
theorem side₂SchoenfliesConfinementInput_of_arcSide (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (hid : ArcSideIdentification data) :
    ZinanCh35Side2.Side₂SchoenfliesConfinementInput data hsep :=
  ZinanCh35Side2Confine.side₂SchoenfliesConfinementInput_holds data hsep
    ⟨fun hw => hid.path₁_mem_sideRegion₁ hw⟩

/-- **Both confinements at once.**  Supplying the single arc↔side identification (the bank datum's
honest content) discharges *both* side confinements — exactly the dependency the audit asked about. -/
theorem bothConfinements_of_arcSide (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hid : ArcSideIdentification data) :
    ZinanCh35Schoenflies.Side₁StarConfinement data ∧
      ZinanCh35Side2.Side₂SchoenfliesConfinementInput data hsep :=
  ⟨side₁StarConfinement_of_arcSide data hsep hid,
    side₂SchoenfliesConfinementInput_of_arcSide data hsep hid⟩







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



/-- The dart-arc realizing the forward boundary run between the chord-dart endpoints. -/
noncomputable def fwdArc (data : hNT.ChordSplitData u v) :
    DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart) := by
  classical
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  have hxy_edge : s(M.tail data.dart, M.head data.dart) = s(u, v) := hedge
  have hxy_ne : M.tail data.dart ≠ M.head data.dart := by
    intro hcontra
    have h1 : s(M.head data.dart, M.head data.dart) = s(u, v) := hcontra ▸ hxy_edge
    have huv : u = v := by
      rcases Sym2.eq_iff.mp h1.symm with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact hl.trans hr.symm
      · exact hl.trans hr.symm
    exact data.chord.endpoints_ne huv
  have hx_bv : hNT.outerCycle.IsBoundaryVertex (M.tail data.dart) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · rw [hxu]; exact data.chord.left_boundary
    · rw [hxv]; exact data.chord.right_boundary
  have hy_bv : hNT.outerCycle.IsBoundaryVertex (M.head data.dart) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨_, hyv⟩ | ⟨_, hyu⟩
    · rw [hyv]; exact data.chord.right_boundary
    · rw [hyu]; exact data.chord.left_boundary
  have hnbe : ¬ hNT.outerCycle.IsBoundaryEdge s(M.head data.dart, M.tail data.dart) := by
    rw [show (s(M.head data.dart, M.tail data.dart) : Sym2 M.Vertex)
          = s(M.tail data.dart, M.head data.dart) from Sym2.eq_swap, hxy_edge]
    exact data.chord.not_boundary_edge
  exact (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    (Ne.symm hxy_ne) hy_bv hx_bv hnbe).1

lemma fwdArc_len (data : hNT.ChordSplitData u v) : 2 ≤ (fwdArc data).len := by
  classical
  -- the underlying dartArc has length ≥ 2.
  show 2 ≤ ((hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple _ _ _ _).1).len
  exact (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple _ _ _ _).2

/-- `C₂ = chord ∪ forward run`: the simple primal cycle `ofDartArc (fwdArc) data.dart`. -/
noncomputable def C₂ (data : hNT.ChordSplitData u v) : SimplePrimalCycle M :=
  SimplePrimalCycle.ofDartArc (fwdArc data) data.dart (fwdArc_len data) rfl rfl

/-- Index `0` of `C₂` is the chord dart. -/
lemma C₂_dart_zero (data : hNT.ChordSplitData u v) :
    (C₂ data).dart ⟨0, (C₂ data).len_pos⟩ = data.dart := by
  show SimplePrimalCycle.chordArcDart (fwdArc data) data.dart ⟨0, (C₂ data).len_pos⟩ = data.dart
  exact SimplePrimalCycle.chordArcDart_zero _ _

/-- The chord-incident face `face₂` is the right face of `C₂` at the chord index `0`. -/
lemma C₂_faceRight_zero (data : hNT.ChordSplitData u v) :
    (C₂ data).faceRight ⟨0, (C₂ data).len_pos⟩ = data.face₂ := by
  show M.dartFace (M.α ((C₂ data).dart ⟨0, (C₂ data).len_pos⟩)) = M.dartFace (M.α data.dart)
  rw [C₂_dart_zero]





/-- Every edge of `C₂` is the chord edge `s(u, v)` or a boundary edge of the outer cycle. -/
lemma C₂_edge_chord_or_boundary (data : hNT.ChordSplitData u v) (i : Fin (C₂ data).len) :
    (C₂ data).edge i = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge ((C₂ data).edge i) := by
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  have hedge_i : (C₂ data).edge i = M.dartEdge ((C₂ data).dart i) := rfl
  rw [hedge_i]
  show M.dartEdge (SimplePrimalCycle.chordArcDart (fwdArc data) data.dart i) = s(u, v) ∨
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge (SimplePrimalCycle.chordArcDart (fwdArc data) data.dart i))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · left; rw [SimplePrimalCycle.chordArcDart_zero]; exact hedge
  · right
    rw [SimplePrimalCycle.chordArcDart_succ]
    show M.dartEdge ((fwdArc data).arcDart i') ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem ((fwdArc data).boundary i')

/-- The chord edge `s(u, v)` is in `C₂.edgeSet`. -/
lemma chord_mem_C₂_edgeSet (data : hNT.ChordSplitData u v) :
    (s(u, v) : Sym2 M.Vertex) ∈ (C₂ data).edgeSet := by
  rw [SimplePrimalCycle.mem_edgeSet_iff]
  refine ⟨⟨0, (C₂ data).len_pos⟩, ?_⟩
  have : (C₂ data).edge ⟨0, (C₂ data).len_pos⟩ = M.dartEdge ((C₂ data).dart ⟨0, (C₂ data).len_pos⟩) :=
    rfl
  rw [this, C₂_dart_zero]; exact (hNT.chordDart_edge data.chord).symm



/-- The arc index `(fwdArc.firstIdx).succ` of `C₂`, valid since `C₂.len = fwdArc.len + 1`. -/
noncomputable def arcIdx₀ (data : hNT.ChordSplitData u v) : Fin (C₂ data).len :=
  ((fwdArc data).firstIdx).succ

/-- The `faceLeft` of `C₂` at `arcIdx₀` is the outer face. -/
lemma faceLeft_arcIdx₀ (data : hNT.ChordSplitData u v) :
    (C₂ data).faceLeft (arcIdx₀ data) = hNT.outerFace := by
  show M.dartFace ((C₂ data).dart (arcIdx₀ data)) = hNT.outerFace
  show M.dartFace (SimplePrimalCycle.chordArcDart (fwdArc data) data.dart
      ((fwdArc data).firstIdx).succ) = hNT.outerFace
  rw [SimplePrimalCycle.chordArcDart_succ]
  -- the arc dart lies on the outer cycle, hence its face is the outer face.
  exact (hNT.outerCycle.mem_darts_iff _).mp ((fwdArc data).boundary _)



/-- The bank theorem instance for `C₂`. -/
noncomputable def bankC₂ (data : hNT.ChordSplitData u v) :
    SimpleCycleBankTheorem M (C₂ data) :=
  simpleCycleBankTheorem_holds (C₂ data) hNT.sphere hNT.simpleGraph

/-- **The outer face is not bank-reachable from `face₂` on `C₂`.**  Otherwise, by symmetry,
`outerFace = faceLeft arcIdx₀` would reach `face₂ = faceRight 0`, contradicting `left_right_sep`. -/
lemma not_bankReach_face₂_outerFace (data : hNT.ChordSplitData u v) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) data.face₂ hNT.outerFace := by
  intro hreach
  -- rewrite endpoints into `faceRight 0` / `faceLeft arcIdx₀`.
  have hreach' : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data))
      ((C₂ data).faceRight ⟨0, (C₂ data).len_pos⟩) ((C₂ data).faceLeft (arcIdx₀ data)) := by
    rw [C₂_faceRight_zero, faceLeft_arcIdx₀]; exact hreach
  -- symmetrize to `faceLeft arcIdx₀ ↝ faceRight 0`, contradicting `left_right_sep`.
  have hsym : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data))
      ((C₂ data).faceLeft (arcIdx₀ data)) ((C₂ data).faceRight ⟨0, (C₂ data).len_pos⟩) :=
    Relation.ReflTransGen.symmetric
      (fun _ _ h => dualAvoidsCycleStep_symm (C₂ data) h) hreach'
  exact (bankC₂ data).left_right_sep (arcIdx₀ data) ⟨0, (C₂ data).len_pos⟩ hsym



/-- **A `ChordSplitAdj` step is a `C₂`-avoiding dual step.**  Its edge is non-boundary and non-chord,
hence not in `C₂.edgeSet` (which is contained in chord ∪ boundary edges). -/
lemma chordSplitAdj_imp_dualStep (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M (C₂ data) f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := h
  refine ⟨d, ?_, hdf, hdg⟩
  -- `dartEdge d ∉ C₂.edgeSet`: every C₂ edge is chord or boundary; `dartEdge d` is neither.
  intro hmem
  rw [SimplePrimalCycle.mem_edgeSet_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  rcases C₂_edge_chord_or_boundary data i with hc | hb
  · exact hch (by rw [hi, hc])
  · exact hbe (by rw [hi]; exact hb)

/-- A `ChordSplitAdj`-walk is a `C₂`-avoiding dual walk. -/
lemma chordSplitAdj_reach_imp_dualReach (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chordSplitAdj_imp_dualStep data hstep)

/-- **The bank → `ChordSplitAdj` lift (R8 §E).**  A `C₂`-bank walk from `face₂` lifts to a
`ChordSplitAdj`-walk (i.e. lands inside `side₂`), provided `face₂` cannot bank-reach `outerFace`.
Proved by induction, lifting each step using `not_bankReach_face₂_outerFace`. -/
lemma bankReach_face₂_lifts_to_chordSplitAdj (data : hNT.ChordSplitData u v) {g : M.Face}
    (h : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) data.face₂ g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail f g' hpre hstep ih =>
      -- `ih : face₂ ↝_CSA f`.  Lift the step `f →_bank g'` to `f →_CSA g'`.
      obtain ⟨d, hdedge, hdf, hdg⟩ := hstep
      -- `f` is non-outer: it is CSA-reachable from `face₂ ≠ outerFace`.
      have hface₂_ne : data.face₂ ≠ hNT.outerFace := data.face₂_not_outer
      have hf_ne : f ≠ hNT.outerFace :=
        hNT.side_subset_nonouter hface₂_ne (g := f) ih
      -- the step's edge is non-chord (chord ∈ C₂.edgeSet, this edge ∉).
      have hch : M.dartEdge d ≠ s(u, v) := by
        intro he; exact hdedge (he ▸ chord_mem_C₂_edgeSet data)
      -- the step's edge is non-boundary: else it would reach `outerFace`.
      have hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
        intro hbedge
        rcases ProofsInTheBook.ZinanCh35InnerConn.boundaryEdge_dart_outer hbedge with ho | ho
        · exact hf_ne (hdf ▸ ho)
        · -- `dartFace (α d) = g' = outerFace`; so `face₂ ↝_bank g' = outerFace`.
          have hg'_outer : g' = hNT.outerFace := hdg ▸ ho
          apply not_bankReach_face₂_outerFace data
          -- `face₂ ↝_bank f` (lift of `ih`) then the step to `g' = outerFace`.
          have hbankf : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) data.face₂ f :=
            chordSplitAdj_reach_imp_dualReach data ih
          have : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) data.face₂ g' :=
            hbankf.tail ⟨d, hdedge, hdf, hdg⟩
          rwa [hg'_outer] at this
      -- assemble the CSA step and append.
      exact ih.tail ⟨d, hdf, hdg, hbe, hch⟩



/-- **The forward-run bank-side fact (UNCONDITIONAL).**  For each arc dart of `C₂` (forward `v → u`
run), the bounded reverse face is in `side₂`. -/
theorem fwdArc_reverse_face_mem_side₂ (data : hNT.ChordSplitData u v) (i : Fin (fwdArc data).len) :
    M.dartFace (M.α ((fwdArc data).arcDart i)) ∈ data.side₂ := by
  -- the arc dart is `C₂.dart (i.succ)`; its reverse face is `faceRight (i.succ)`.
  have hi : (i.succ : Fin (C₂ data).len) = i.succ := rfl
  have hface : (C₂ data).faceRight i.succ = M.dartFace (M.α ((fwdArc data).arcDart i)) := by
    show M.dartFace (M.α ((C₂ data).dart i.succ)) = M.dartFace (M.α ((fwdArc data).arcDart i))
    show M.dartFace (M.α (SimplePrimalCycle.chordArcDart (fwdArc data) data.dart i.succ))
        = M.dartFace (M.α ((fwdArc data).arcDart i))
    rw [SimplePrimalCycle.chordArcDart_succ]
  -- `right_bank`: faceRight 0 ↝_bank faceRight (i.succ).
  have hbank : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data))
      data.face₂ ((C₂ data).faceRight i.succ) := by
    rw [← C₂_faceRight_zero data]
    exact (bankC₂ data).right_bank ⟨0, (C₂ data).len_pos⟩ i.succ
  rw [hface] at hbank
  -- lift to ChordSplitAdj = side₂ membership.
  exact bankReach_face₂_lifts_to_chordSplitAdj data hbank

/-- An arc dart of `C₂` (forward run) has a non-chord (boundary) edge. -/
lemma fwdArc_dartEdge_ne_chord (data : hNT.ChordSplitData u v) (i : Fin (fwdArc data).len) :
    M.dartEdge ((fwdArc data).arcDart i) ≠ s(u, v) := by
  intro he
  -- the arc dart lies on the outer cycle, so its edge is a boundary edge; but `s(u,v)` is not.
  apply data.chord.not_boundary_edge
  rw [← he]
  show M.dartEdge ((fwdArc data).arcDart i) ∈ hNT.outerCycle.edges
  rw [hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem ((fwdArc data).boundary i)

/-- **For every forward-run vertex, the tail lies in `sideRegion₂` (UNCONDITIONAL).**  Composes
`fwdArc_reverse_face_mem_side₂` with the landed per-dart bridge
`ZinanCh35ArcDartRun.dartRun_tail_mem_sideRegion₂_of_face`. -/
theorem fwdArc_tail_mem_sideRegion₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (i : Fin (fwdArc data).len) :
    M.tail ((fwdArc data).arcDart i) ∈ sideRegion₂ data :=
  ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.dartRun_tail_mem_sideRegion₂_of_face
    data hsep (fwdArc_dartEdge_ne_chord data i) (fwdArc_reverse_face_mem_side₂ data i)











/-- The dart-arc realizing the `u → v` boundary run (between the reversed chord-dart endpoints). -/
noncomputable def bwdArc (data : hNT.ChordSplitData u v) :
    DartArc M hNT.outerCycle (M.head (M.α data.dart)) (M.tail (M.α data.dart)) := by
  classical
  have hedge : M.dartEdge (M.α data.dart) = s(u, v) := by
    rw [M.dartEdge_alpha]; exact hNT.chordDart_edge data.chord
  have hxy_edge : s(M.tail (M.α data.dart), M.head (M.α data.dart)) = s(u, v) := hedge
  have hxy_ne : M.tail (M.α data.dart) ≠ M.head (M.α data.dart) := by
    intro hcontra
    have h1 : s(M.head (M.α data.dart), M.head (M.α data.dart)) = s(u, v) := hcontra ▸ hxy_edge
    have huv : u = v := by
      rcases Sym2.eq_iff.mp h1.symm with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact hl.trans hr.symm
      · exact hl.trans hr.symm
    exact data.chord.endpoints_ne huv
  have hx_bv : hNT.outerCycle.IsBoundaryVertex (M.tail (M.α data.dart)) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · rw [hxu]; exact data.chord.left_boundary
    · rw [hxv]; exact data.chord.right_boundary
  have hy_bv : hNT.outerCycle.IsBoundaryVertex (M.head (M.α data.dart)) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨_, hyv⟩ | ⟨_, hyu⟩
    · rw [hyv]; exact data.chord.right_boundary
    · rw [hyu]; exact data.chord.left_boundary
  have hnbe : ¬ hNT.outerCycle.IsBoundaryEdge
      s(M.head (M.α data.dart), M.tail (M.α data.dart)) := by
    rw [show (s(M.head (M.α data.dart), M.tail (M.α data.dart)) : Sym2 M.Vertex)
          = s(M.tail (M.α data.dart), M.head (M.α data.dart)) from Sym2.eq_swap, hxy_edge]
    exact data.chord.not_boundary_edge
  exact (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    (Ne.symm hxy_ne) hy_bv hx_bv hnbe).1

lemma bwdArc_len (data : hNT.ChordSplitData u v) : 2 ≤ (bwdArc data).len := by
  classical
  show 2 ≤ ((hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple _ _ _ _).1).len
  exact (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple _ _ _ _).2

/-- `C₁ = chord ∪ (u → v run)`: `ofDartArc (bwdArc) (α data.dart)`. -/
noncomputable def C₁ (data : hNT.ChordSplitData u v) : SimplePrimalCycle M :=
  SimplePrimalCycle.ofDartArc (bwdArc data) (M.α data.dart) (bwdArc_len data) rfl rfl

lemma C₁_dart_zero (data : hNT.ChordSplitData u v) :
    (C₁ data).dart ⟨0, (C₁ data).len_pos⟩ = M.α data.dart := by
  show SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart) ⟨0, (C₁ data).len_pos⟩
      = M.α data.dart
  exact SimplePrimalCycle.chordArcDart_zero _ _

/-- `faceRight 0` of `C₁` is `face₁` (`= dartFace (α (α data.dart)) = dartFace data.dart`). -/
lemma C₁_faceRight_zero (data : hNT.ChordSplitData u v) :
    (C₁ data).faceRight ⟨0, (C₁ data).len_pos⟩ = data.face₁ := by
  show M.dartFace (M.α ((C₁ data).dart ⟨0, (C₁ data).len_pos⟩)) = M.dartFace data.dart
  rw [C₁_dart_zero, M.alpha_alpha]

/-- Every edge of `C₁` is the chord or a boundary edge. -/
lemma C₁_edge_chord_or_boundary (data : hNT.ChordSplitData u v) (i : Fin (C₁ data).len) :
    (C₁ data).edge i = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge ((C₁ data).edge i) := by
  have hedge : M.dartEdge (M.α data.dart) = s(u, v) := by
    rw [M.dartEdge_alpha]; exact hNT.chordDart_edge data.chord
  have hedge_i : (C₁ data).edge i = M.dartEdge ((C₁ data).dart i) := rfl
  rw [hedge_i]
  show M.dartEdge (SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart) i) = s(u, v) ∨
    hNT.outerCycle.IsBoundaryEdge
      (M.dartEdge (SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart) i))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · left; rw [SimplePrimalCycle.chordArcDart_zero]; exact hedge
  · right
    rw [SimplePrimalCycle.chordArcDart_succ]
    show M.dartEdge ((bwdArc data).arcDart i') ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem ((bwdArc data).boundary i')

lemma chord_mem_C₁_edgeSet (data : hNT.ChordSplitData u v) :
    (s(u, v) : Sym2 M.Vertex) ∈ (C₁ data).edgeSet := by
  rw [SimplePrimalCycle.mem_edgeSet_iff]
  refine ⟨⟨0, (C₁ data).len_pos⟩, ?_⟩
  have : (C₁ data).edge ⟨0, (C₁ data).len_pos⟩ = M.dartEdge ((C₁ data).dart ⟨0, (C₁ data).len_pos⟩) :=
    rfl
  rw [this, C₁_dart_zero, M.dartEdge_alpha]; exact (hNT.chordDart_edge data.chord).symm

noncomputable def arcIdx₀C₁ (data : hNT.ChordSplitData u v) : Fin (C₁ data).len :=
  ((bwdArc data).firstIdx).succ

lemma faceLeft_arcIdx₀C₁ (data : hNT.ChordSplitData u v) :
    (C₁ data).faceLeft (arcIdx₀C₁ data) = hNT.outerFace := by
  show M.dartFace ((C₁ data).dart (arcIdx₀C₁ data)) = hNT.outerFace
  show M.dartFace (SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart)
      ((bwdArc data).firstIdx).succ) = hNT.outerFace
  rw [SimplePrimalCycle.chordArcDart_succ]
  exact (hNT.outerCycle.mem_darts_iff _).mp ((bwdArc data).boundary _)

noncomputable def bankC₁ (data : hNT.ChordSplitData u v) :
    SimpleCycleBankTheorem M (C₁ data) :=
  simpleCycleBankTheorem_holds (C₁ data) hNT.sphere hNT.simpleGraph

lemma not_bankReach_face₁_outerFace (data : hNT.ChordSplitData u v) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) data.face₁ hNT.outerFace := by
  intro hreach
  have hreach' : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data))
      ((C₁ data).faceRight ⟨0, (C₁ data).len_pos⟩) ((C₁ data).faceLeft (arcIdx₀C₁ data)) := by
    rw [C₁_faceRight_zero, faceLeft_arcIdx₀C₁]; exact hreach
  have hsym : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data))
      ((C₁ data).faceLeft (arcIdx₀C₁ data)) ((C₁ data).faceRight ⟨0, (C₁ data).len_pos⟩) :=
    Relation.ReflTransGen.symmetric
      (fun _ _ h => dualAvoidsCycleStep_symm (C₁ data) h) hreach'
  exact (bankC₁ data).left_right_sep (arcIdx₀C₁ data) ⟨0, (C₁ data).len_pos⟩ hsym

/-- A `ChordSplitAdj` step is a `C₁`-avoiding dual step. -/
lemma chordSplitAdj_imp_dualStepC₁ (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M (C₁ data) f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := h
  refine ⟨d, ?_, hdf, hdg⟩
  intro hmem
  rw [SimplePrimalCycle.mem_edgeSet_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  rcases C₁_edge_chord_or_boundary data i with hc | hb
  · exact hch (by rw [hi, hc])
  · exact hbe (by rw [hi]; exact hb)

lemma chordSplitAdj_reach_imp_dualReachC₁ (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chordSplitAdj_imp_dualStepC₁ data hstep)

/-- The side-1 bank → `ChordSplitAdj` lift (mirror of `bankReach_face₂_lifts_to_chordSplitAdj`). -/
lemma bankReach_face₁_lifts_to_chordSplitAdj (data : hNT.ChordSplitData u v) {g : M.Face}
    (h : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) data.face₁ g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail f g' hpre hstep ih =>
      obtain ⟨d, hdedge, hdf, hdg⟩ := hstep
      have hface₁_ne : data.face₁ ≠ hNT.outerFace := data.face₁_not_outer
      have hf_ne : f ≠ hNT.outerFace :=
        hNT.side_subset_nonouter hface₁_ne (g := f) ih
      have hch : M.dartEdge d ≠ s(u, v) := by
        intro he; exact hdedge (he ▸ chord_mem_C₁_edgeSet data)
      have hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
        intro hbedge
        rcases ProofsInTheBook.ZinanCh35InnerConn.boundaryEdge_dart_outer hbedge with ho | ho
        · exact hf_ne (hdf ▸ ho)
        · have hg'_outer : g' = hNT.outerFace := hdg ▸ ho
          apply not_bankReach_face₁_outerFace data
          have hbankf : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) data.face₁ f :=
            chordSplitAdj_reach_imp_dualReachC₁ data ih
          have : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) data.face₁ g' :=
            hbankf.tail ⟨d, hdedge, hdf, hdg⟩
          rwa [hg'_outer] at this
      exact ih.tail ⟨d, hdf, hdg, hbe, hch⟩

/-- **The backward-run bank-side fact (UNCONDITIONAL).**  For each arc dart of `C₁` (the `u → v`
run), the bounded reverse face is in `side₁`. -/
theorem bwdArc_reverse_face_mem_side₁ (data : hNT.ChordSplitData u v) (i : Fin (bwdArc data).len) :
    M.dartFace (M.α ((bwdArc data).arcDart i)) ∈ data.side₁ := by
  have hface : (C₁ data).faceRight i.succ = M.dartFace (M.α ((bwdArc data).arcDart i)) := by
    show M.dartFace (M.α (SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart) i.succ))
        = M.dartFace (M.α ((bwdArc data).arcDart i))
    rw [SimplePrimalCycle.chordArcDart_succ]
  have hbank : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data))
      data.face₁ ((C₁ data).faceRight i.succ) := by
    rw [← C₁_faceRight_zero data]
    exact (bankC₁ data).right_bank ⟨0, (C₁ data).len_pos⟩ i.succ
  rw [hface] at hbank
  exact bankReach_face₁_lifts_to_chordSplitAdj data hbank

lemma bwdArc_dartEdge_ne_chord (data : hNT.ChordSplitData u v) (i : Fin (bwdArc data).len) :
    M.dartEdge ((bwdArc data).arcDart i) ≠ s(u, v) := by
  intro he
  apply data.chord.not_boundary_edge
  rw [← he]
  show M.dartEdge ((bwdArc data).arcDart i) ∈ hNT.outerCycle.edges
  rw [hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem ((bwdArc data).boundary i)

















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











/-- Retype a `DartArc`'s endpoints along equalities. -/
noncomputable def daCast {f : M.Face} {C : BoundaryCycle M f} {a a' b b' : M.Vertex}
    (A : DartArc M C a b) (ha : a = a') (hb : b = b') : DartArc M C a' b' := ha ▸ hb ▸ A

@[simp] lemma daCast_len {f : M.Face} {C : BoundaryCycle M f} {a a' b b' : M.Vertex}
    (A : DartArc M C a b) (ha : a = a') (hb : b = b') : (daCast A ha hb).len = A.len := by
  subst ha; subst hb; rfl

lemma daCast_arcDart {f : M.Face} {C : BoundaryCycle M f} {a a' b b' : M.Vertex}
    (A : DartArc M C a b) (ha : a = a') (hb : b = b') (i : Fin (daCast A ha hb).len) :
    M.tail ((daCast A ha hb).arcDart i)
      = M.tail (A.arcDart (Fin.cast (daCast_len A ha hb) i)) := by
  subst ha; subst hb; rfl

/-- The arc-dart of a casted dart-arc equals the original at the cast index. -/
lemma daCast_arcDart_eq {f : M.Face} {C : BoundaryCycle M f} {a a' b b' : M.Vertex}
    (A : DartArc M C a b) (ha : a = a') (hb : b = b') (i : Fin (daCast A ha hb).len) :
    (daCast A ha hb).arcDart i = A.arcDart (Fin.cast (daCast_len A ha hb) i) := by
  subst ha; subst hb; rfl

/-- **The tail of a casted cyclic dart-arc at index `i` is the cyclic-slice tail `darts[(p+i)%L]`.** -/
lemma daCast_cyclic_tail {f : M.Face} (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < C.darts.length) (hp : p < C.darts.length)
    {a' b' : M.Vertex}
    (ha : M.tail (C.darts[p]'hp) = a')
    (hb : M.tail (C.darts[(p + k) % C.darts.length]'(Nat.mod_lt _ (by omega))) = b')
    (i : Fin (daCast (C.cyclicDartArc hC p k hk hkL hp) ha hb).len) :
    M.tail ((daCast (C.cyclicDartArc hC p k hk hkL hp) ha hb).arcDart i)
      = M.tail (C.darts[(p + i.1) % C.darts.length]'(Nat.mod_lt _ (by omega))) := by
  rw [daCast_arcDart, BoundaryCycle.cyclicDartArc_arcDart]; rfl



/-- **The `BoundaryPath` of a dart arc.**  Its vertices are the arc-dart tails followed by the
terminal endpoint `b`; its edges are the arc-dart graph edges.  Simplicity from `tail_nodup`
together with `head_last_ne_tail`. -/
noncomputable def bpOfDartArc {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) : BoundaryPath M a b where
  vertices := A.dartList.map M.tail ++ [b]
  edges := A.dartList.map M.dartEdge
  starts_at := by
    have hne : (A.dartList.map M.tail) ≠ [] := by simp [A.dartList_ne_nil]
    have h0 : 0 < A.dartList.length := by rw [DartArc.dartList_length]; exact A.len_pos
    rw [List.head?_append_of_ne_nil _ hne, List.head?_map, List.head?_eq_getElem?,
      List.getElem?_eq_getElem h0, A.dartList_getElem 0 A.len_pos]
    simp only [Option.map_some]; rw [A.tail_first]
  ends_at := by simp
  simple := by
    rw [List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [DartArc.dartList, List.map_map, List.nodup_map_iff_inj_on (List.nodup_finRange A.len)]
      intro i _ j _ hij; exact A.tail_nodup hij
    · intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      rw [List.mem_map] at hx
      obtain ⟨d, hd, hdt⟩ := hx
      obtain ⟨i, hi⟩ := A.mem_dartList hd
      rw [← hi] at hdt
      exact fun hxb => A.head_last_ne_tail i (hxb ▸ hdt.symm)

@[simp] lemma bpOfDartArc_vertices {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) : (bpOfDartArc A).vertices = A.dartList.map M.tail ++ [b] := rfl



/-- The internal vertices of `bpOfDartArc A` are the tails of the arc darts with index `≥ 1`. -/
lemma bpOfDartArc_internal {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) :
    (bpOfDartArc A).internalVertices = (A.dartList.map M.tail).tail := by
  show (A.dartList.map M.tail ++ [b]).tail.dropLast = (A.dartList.map M.tail).tail
  have hne : (A.dartList.map M.tail) ≠ [] := by simp [A.dartList_ne_nil]
  rw [List.tail_append_of_ne_nil hne, List.dropLast_concat]

/-- Every vertex of `bpOfDartArc A` is a tail of an arc dart, or the terminal endpoint `b`. -/
lemma bpOfDartArc_mem_vertices {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) {w : M.Vertex} (hw : w ∈ (bpOfDartArc A).vertices) :
    (∃ i : Fin A.len, M.tail (A.arcDart i) = w) ∨ w = b := by
  rw [bpOfDartArc_vertices, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | hw
  · left
    rw [List.mem_map] at hw
    obtain ⟨d, hd, hdt⟩ := hw
    obtain ⟨i, hi⟩ := A.mem_dartList hd
    exact ⟨i, hi ▸ hdt⟩
  · right; exact hw

/-- An internal vertex of `bpOfDartArc A` is a tail of an arc dart. -/
lemma bpOfDartArc_internal_tail {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) {w : M.Vertex} (hw : w ∈ (bpOfDartArc A).internalVertices) :
    ∃ i : Fin A.len, M.tail (A.arcDart i) = w := by
  rw [bpOfDartArc_internal] at hw
  have hsub : w ∈ A.dartList.map M.tail := List.tail_subset _ hw
  rw [List.mem_map] at hsub
  obtain ⟨d, hd, hdt⟩ := hsub
  obtain ⟨i, hi⟩ := A.mem_dartList hd
  exact ⟨i, hi ▸ hdt⟩

/-- An arc-dart tail is a boundary vertex (`A`'s darts lie on the cycle). -/
lemma arcDart_tail_mem_vertices {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) (i : Fin A.len) : M.tail (A.arcDart i) ∈ C.vertices := by
  rw [C.vertices_eq]; exact List.mem_map_of_mem (A.boundary i)

/-- Every vertex of `bpOfDartArc A` is a boundary vertex, provided the terminal endpoint `b` is. -/
lemma bpOfDartArc_boundary_vertices {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) (hb : b ∈ C.vertices) {w : M.Vertex}
    (hw : w ∈ (bpOfDartArc A).vertices) : w ∈ C.vertices := by
  rcases bpOfDartArc_mem_vertices A hw with ⟨i, hi⟩ | hwb
  · rw [← hi]; exact arcDart_tail_mem_vertices A i
  · rw [hwb]; exact hb

/-- `bpOfDartArc A` has an internal vertex when `2 ≤ A.len`. -/
lemma bpOfDartArc_hasInternal {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) (hlen : 2 ≤ A.len) : (bpOfDartArc A).HasInternalVertex := by
  rw [BoundaryPath.hasInternalVertex_iff, bpOfDartArc_internal]
  -- (A.dartList.map M.tail).tail ≠ []: dartList has length A.len ≥ 2.
  intro hcontra
  have hlenlist : (A.dartList.map M.tail).length = A.len := by
    rw [List.length_map, DartArc.dartList_length]
  have htl : (A.dartList.map M.tail).tail.length = (A.dartList.map M.tail).length - 1 :=
    List.length_tail
  rw [hcontra] at htl
  simp only [List.length_nil] at htl
  omega



namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}

/-- `C₂[A] = chord ∪ A`, for an arbitrary forward run `A : DartArc (head dart) (tail dart)`. -/
noncomputable def C₂A (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    SimplePrimalCycle M :=
  SimplePrimalCycle.ofDartArc A data.dart hlen rfl rfl

lemma C₂A_dart_zero (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    (C₂A data A hlen).dart ⟨0, (C₂A data A hlen).len_pos⟩ = data.dart := by
  show SimplePrimalCycle.chordArcDart A data.dart ⟨0, (C₂A data A hlen).len_pos⟩ = data.dart
  exact SimplePrimalCycle.chordArcDart_zero _ _

lemma C₂A_faceRight_zero (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    (C₂A data A hlen).faceRight ⟨0, (C₂A data A hlen).len_pos⟩ = data.face₂ := by
  show M.dartFace (M.α ((C₂A data A hlen).dart ⟨0, (C₂A data A hlen).len_pos⟩))
      = M.dartFace (M.α data.dart)
  rw [C₂A_dart_zero]

lemma C₂A_edge_chord_or_boundary (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    (i : Fin (C₂A data A hlen).len) :
    (C₂A data A hlen).edge i = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge ((C₂A data A hlen).edge i) := by
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  show M.dartEdge (SimplePrimalCycle.chordArcDart A data.dart i) = s(u, v) ∨
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge (SimplePrimalCycle.chordArcDart A data.dart i))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · left; rw [SimplePrimalCycle.chordArcDart_zero]; exact hedge
  · right
    rw [SimplePrimalCycle.chordArcDart_succ]
    show M.dartEdge (A.arcDart i') ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem (A.boundary i')

lemma chord_mem_C₂A_edgeSet (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    (s(u, v) : Sym2 M.Vertex) ∈ (C₂A data A hlen).edgeSet := by
  rw [SimplePrimalCycle.mem_edgeSet_iff]
  refine ⟨⟨0, (C₂A data A hlen).len_pos⟩, ?_⟩
  show (s(u, v) : Sym2 M.Vertex) = M.dartEdge ((C₂A data A hlen).dart ⟨0, (C₂A data A hlen).len_pos⟩)
  rw [C₂A_dart_zero]; exact (hNT.chordDart_edge data.chord).symm

noncomputable def arcIdx₀A (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    Fin (C₂A data A hlen).len :=
  (A.firstIdx).succ

lemma faceLeft_arcIdx₀A (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    (C₂A data A hlen).faceLeft (arcIdx₀A data A hlen) = hNT.outerFace := by
  show M.dartFace (SimplePrimalCycle.chordArcDart A data.dart (A.firstIdx).succ) = hNT.outerFace
  rw [SimplePrimalCycle.chordArcDart_succ]
  exact (hNT.outerCycle.mem_darts_iff _).mp (A.boundary _)

noncomputable def bankC₂A (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    SimpleCycleBankTheorem M (C₂A data A hlen) :=
  simpleCycleBankTheorem_holds (C₂A data A hlen) hNT.sphere hNT.simpleGraph

lemma not_bankReach_face₂_outerFaceA (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen)) data.face₂ hNT.outerFace := by
  intro hreach
  have hreach' : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen))
      ((C₂A data A hlen).faceRight ⟨0, (C₂A data A hlen).len_pos⟩)
      ((C₂A data A hlen).faceLeft (arcIdx₀A data A hlen)) := by
    rw [C₂A_faceRight_zero, faceLeft_arcIdx₀A]; exact hreach
  have hsym : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen))
      ((C₂A data A hlen).faceLeft (arcIdx₀A data A hlen))
      ((C₂A data A hlen).faceRight ⟨0, (C₂A data A hlen).len_pos⟩) :=
    Relation.ReflTransGen.symmetric
      (fun _ _ h => dualAvoidsCycleStep_symm (C₂A data A hlen) h) hreach'
  exact (bankC₂A data A hlen).left_right_sep (arcIdx₀A data A hlen)
    ⟨0, (C₂A data A hlen).len_pos⟩ hsym

lemma chordSplitAdj_imp_dualStepA (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    {f g : M.Face} (h : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M (C₂A data A hlen) f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := h
  refine ⟨d, ?_, hdf, hdg⟩
  intro hmem
  rw [SimplePrimalCycle.mem_edgeSet_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  rcases C₂A_edge_chord_or_boundary data A hlen i with hc | hb
  · exact hch (by rw [hi, hc])
  · exact hbe (by rw [hi]; exact hb)

lemma chordSplitAdj_reach_imp_dualReachA (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    {f g : M.Face} (h : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen)) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chordSplitAdj_imp_dualStepA data A hlen hstep)

lemma bankReach_face₂_lifts_to_chordSplitAdjA (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    {g : M.Face}
    (h : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen)) data.face₂ g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail f g' hpre hstep ih =>
      obtain ⟨d, hdedge, hdf, hdg⟩ := hstep
      have hf_ne : f ≠ hNT.outerFace :=
        hNT.side_subset_nonouter data.face₂_not_outer (g := f) ih
      have hch : M.dartEdge d ≠ s(u, v) := by
        intro he; exact hdedge (he ▸ chord_mem_C₂A_edgeSet data A hlen)
      have hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
        intro hbedge
        rcases ProofsInTheBook.ZinanCh35InnerConn.boundaryEdge_dart_outer hbedge with ho | ho
        · exact hf_ne (hdf ▸ ho)
        · have hg'_outer : g' = hNT.outerFace := hdg ▸ ho
          apply not_bankReach_face₂_outerFaceA data A hlen
          have hbankf : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen))
              data.face₂ f := chordSplitAdj_reach_imp_dualReachA data A hlen ih
          have : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen)) data.face₂ g' :=
            hbankf.tail ⟨d, hdedge, hdf, hdg⟩
          rwa [hg'_outer] at this
      exact ih.tail ⟨d, hdf, hdg, hbe, hch⟩

/-- **The reverse-face side-2 fact for an ARBITRARY forward run** (generalizes
`ZinanCh35ArcSide.fwdArc_reverse_face_mem_side₂`).  For each arc dart of a run
`A : DartArc (head dart) (tail dart)`, the bounded reverse face lies in `side₂`. -/
theorem fwdRun_reverse_face_mem_side₂ (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    (i : Fin A.len) :
    M.dartFace (M.α (A.arcDart i)) ∈ data.side₂ := by
  have hface : (C₂A data A hlen).faceRight i.succ = M.dartFace (M.α (A.arcDart i)) := by
    show M.dartFace (M.α (SimplePrimalCycle.chordArcDart A data.dart i.succ))
        = M.dartFace (M.α (A.arcDart i))
    rw [SimplePrimalCycle.chordArcDart_succ]
  have hbank : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen))
      data.face₂ ((C₂A data A hlen).faceRight i.succ) := by
    rw [← C₂A_faceRight_zero data A hlen]
    exact (bankC₂A data A hlen).right_bank ⟨0, (C₂A data A hlen).len_pos⟩ i.succ
  rw [hface] at hbank
  exact bankReach_face₂_lifts_to_chordSplitAdjA data A hlen hbank



/-- `C₁[B] = chord(reversed) ∪ B`, for an arbitrary backward run `B`. -/
noncomputable def C₁B (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    SimplePrimalCycle M :=
  SimplePrimalCycle.ofDartArc B (M.α data.dart) hlen (by rw [M.tail_alpha]) (by rw [M.head_alpha])

lemma C₁B_dart_zero (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    (C₁B data B hlen).dart ⟨0, (C₁B data B hlen).len_pos⟩ = M.α data.dart := by
  show SimplePrimalCycle.chordArcDart B (M.α data.dart) ⟨0, (C₁B data B hlen).len_pos⟩ = M.α data.dart
  exact SimplePrimalCycle.chordArcDart_zero _ _

lemma C₁B_faceRight_zero (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    (C₁B data B hlen).faceRight ⟨0, (C₁B data B hlen).len_pos⟩ = data.face₁ := by
  show M.dartFace (M.α ((C₁B data B hlen).dart ⟨0, (C₁B data B hlen).len_pos⟩)) = M.dartFace data.dart
  rw [C₁B_dart_zero, M.alpha_alpha]

lemma C₁B_edge_chord_or_boundary (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    (i : Fin (C₁B data B hlen).len) :
    (C₁B data B hlen).edge i = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge ((C₁B data B hlen).edge i) := by
  have hedge : M.dartEdge (M.α data.dart) = s(u, v) := by
    rw [M.dartEdge_alpha]; exact hNT.chordDart_edge data.chord
  show M.dartEdge (SimplePrimalCycle.chordArcDart B (M.α data.dart) i) = s(u, v) ∨
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge (SimplePrimalCycle.chordArcDart B (M.α data.dart) i))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · left; rw [SimplePrimalCycle.chordArcDart_zero]; exact hedge
  · right
    rw [SimplePrimalCycle.chordArcDart_succ]
    show M.dartEdge (B.arcDart i') ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem (B.boundary i')

lemma chord_mem_C₁B_edgeSet (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    (s(u, v) : Sym2 M.Vertex) ∈ (C₁B data B hlen).edgeSet := by
  rw [SimplePrimalCycle.mem_edgeSet_iff]
  refine ⟨⟨0, (C₁B data B hlen).len_pos⟩, ?_⟩
  show (s(u, v) : Sym2 M.Vertex) = M.dartEdge ((C₁B data B hlen).dart ⟨0, (C₁B data B hlen).len_pos⟩)
  rw [C₁B_dart_zero, M.dartEdge_alpha]; exact (hNT.chordDart_edge data.chord).symm

noncomputable def arcIdx₀B (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    Fin (C₁B data B hlen).len :=
  (B.firstIdx).succ

lemma faceLeft_arcIdx₀B (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    (C₁B data B hlen).faceLeft (arcIdx₀B data B hlen) = hNT.outerFace := by
  show M.dartFace (SimplePrimalCycle.chordArcDart B (M.α data.dart) (B.firstIdx).succ) = hNT.outerFace
  rw [SimplePrimalCycle.chordArcDart_succ]
  exact (hNT.outerCycle.mem_darts_iff _).mp (B.boundary _)

noncomputable def bankC₁B (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    SimpleCycleBankTheorem M (C₁B data B hlen) :=
  simpleCycleBankTheorem_holds (C₁B data B hlen) hNT.sphere hNT.simpleGraph

lemma not_bankReach_face₁_outerFaceB (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen)) data.face₁ hNT.outerFace := by
  intro hreach
  have hreach' : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen))
      ((C₁B data B hlen).faceRight ⟨0, (C₁B data B hlen).len_pos⟩)
      ((C₁B data B hlen).faceLeft (arcIdx₀B data B hlen)) := by
    rw [C₁B_faceRight_zero, faceLeft_arcIdx₀B]; exact hreach
  have hsym : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen))
      ((C₁B data B hlen).faceLeft (arcIdx₀B data B hlen))
      ((C₁B data B hlen).faceRight ⟨0, (C₁B data B hlen).len_pos⟩) :=
    Relation.ReflTransGen.symmetric
      (fun _ _ h => dualAvoidsCycleStep_symm (C₁B data B hlen) h) hreach'
  exact (bankC₁B data B hlen).left_right_sep (arcIdx₀B data B hlen)
    ⟨0, (C₁B data B hlen).len_pos⟩ hsym

lemma chordSplitAdj_imp_dualStepB (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    {f g : M.Face} (h : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M (C₁B data B hlen) f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := h
  refine ⟨d, ?_, hdf, hdg⟩
  intro hmem
  rw [SimplePrimalCycle.mem_edgeSet_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  rcases C₁B_edge_chord_or_boundary data B hlen i with hc | hb
  · exact hch (by rw [hi, hc])
  · exact hbe (by rw [hi]; exact hb)

lemma chordSplitAdj_reach_imp_dualReachB (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    {f g : M.Face} (h : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen)) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chordSplitAdj_imp_dualStepB data B hlen hstep)

lemma bankReach_face₁_lifts_to_chordSplitAdjB (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    {g : M.Face}
    (h : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen)) data.face₁ g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail f g' hpre hstep ih =>
      obtain ⟨d, hdedge, hdf, hdg⟩ := hstep
      have hf_ne : f ≠ hNT.outerFace :=
        hNT.side_subset_nonouter data.face₁_not_outer (g := f) ih
      have hch : M.dartEdge d ≠ s(u, v) := by
        intro he; exact hdedge (he ▸ chord_mem_C₁B_edgeSet data B hlen)
      have hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
        intro hbedge
        rcases ProofsInTheBook.ZinanCh35InnerConn.boundaryEdge_dart_outer hbedge with ho | ho
        · exact hf_ne (hdf ▸ ho)
        · have hg'_outer : g' = hNT.outerFace := hdg ▸ ho
          apply not_bankReach_face₁_outerFaceB data B hlen
          have hbankf : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen))
              data.face₁ f := chordSplitAdj_reach_imp_dualReachB data B hlen ih
          have : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen)) data.face₁ g' :=
            hbankf.tail ⟨d, hdedge, hdf, hdg⟩
          rwa [hg'_outer] at this
      exact ih.tail ⟨d, hdf, hdg, hbe, hch⟩

/-- **The reverse-face side-1 fact for an ARBITRARY backward run** (generalizes
`ZinanCh35ArcSide.bwdArc_reverse_face_mem_side₁`). -/
theorem bwdRun_reverse_face_mem_side₁ (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    (i : Fin B.len) :
    M.dartFace (M.α (B.arcDart i)) ∈ data.side₁ := by
  have hface : (C₁B data B hlen).faceRight i.succ = M.dartFace (M.α (B.arcDart i)) := by
    show M.dartFace (M.α (SimplePrimalCycle.chordArcDart B (M.α data.dart) i.succ))
        = M.dartFace (M.α (B.arcDart i))
    rw [SimplePrimalCycle.chordArcDart_succ]
  have hbank : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen))
      data.face₁ ((C₁B data B hlen).faceRight i.succ) := by
    rw [← C₁B_faceRight_zero data B hlen]
    exact (bankC₁B data B hlen).right_bank ⟨0, (C₁B data B hlen).len_pos⟩ i.succ
  rw [hface] at hbank
  exact bankReach_face₁_lifts_to_chordSplitAdjB data B hlen hbank

end NearTriangulation



/-- **The two complementary forward cyclic runs cover the cycle.**  From two positions `pf ≠ pt` on
a length-`L` cyclic list, the forward run from `pf` of length `kf = (pt - pf) mod L` and the forward
run from `pt` of length `kb = (pf - pt) mod L` are complementary: `kf, kb ≥ 1`, `kf + kb = L`,
`(pf + kf) mod L = pt`, and every position `q < L` lies in one of the two runs. -/
theorem mod_cover (L pf pt : ℕ) (hLpos : 0 < L) (hpf : pf < L) (hpt : pt < L) (hne : pf ≠ pt)
    (kf kb : ℕ) (hkf_eq : kf = (pt + L - pf) % L) (hkb_eq : kb = (pf + L - pt) % L) :
    1 ≤ kf ∧ 1 ≤ kb ∧ kf + kb = L ∧ (pf + kf) % L = pt ∧
    ∀ q, q < L → (∃ j, j < kf ∧ (pf + j) % L = q) ∨ (∃ j, j < kb ∧ (pt + j) % L = q) := by
  have hkf1 : 1 ≤ kf := by
    rw [hkf_eq]
    rcases Nat.eq_zero_or_pos ((pt + L - pf) % L) with h0 | h0
    · exfalso
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h0
      have hlt : pt + L - pf < 2 * L := by omega
      have hgt : 0 < pt + L - pf := by omega
      have : m = 1 := by nlinarith
      rw [this, Nat.mul_one] at hm; omega
    · exact h0
  have hkb1 : 1 ≤ kb := by
    rw [hkb_eq]
    rcases Nat.eq_zero_or_pos ((pf + L - pt) % L) with h0 | h0
    · exfalso
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h0
      have hlt : pf + L - pt < 2 * L := by omega
      have hgt : 0 < pf + L - pt := by omega
      have : m = 1 := by nlinarith
      rw [this, Nat.mul_one] at hm; omega
    · exact h0
  have hkfval : kf = if pf ≤ pt then pt - pf else pt + L - pf := by
    rw [hkf_eq]; split
    · next h => rw [show pt + L - pf = (pt - pf) + L from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · next h => rw [Nat.mod_eq_of_lt (by omega)]
  have hkbval : kb = if pt ≤ pf then pf - pt else pf + L - pt := by
    rw [hkb_eq]; split
    · next h => rw [show pf + L - pt = (pf - pt) + L from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · next h => rw [Nat.mod_eq_of_lt (by omega)]
  have hsum : kf + kb = L := by rw [hkfval, hkbval]; split <;> split <;> omega
  have hpfkf : (pf + kf) % L = pt := by
    rw [hkf_eq]
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L)]
    rw [← Nat.add_mod]
    have : pf + (pt + L - pf) = pt + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hpt]
  refine ⟨hkf1, hkb1, hsum, hpfkf, ?_⟩
  intro q hq
  set df := (q + L - pf) % L with hdf
  have hdfL : df < L := Nat.mod_lt _ hLpos
  have hpfdf : (pf + df) % L = q := by
    rw [hdf]
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L)]
    rw [← Nat.add_mod]
    have : pf + (q + L - pf) = q + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  by_cases hd : df < kf
  · exact Or.inl ⟨df, hd, hpfdf⟩
  · refine Or.inr ⟨df - kf, by omega, ?_⟩
    calc (pt + (df - kf)) % L = ((pf + kf) % L + (df - kf)) % L := by rw [hpfkf]
      _ = (pf + kf + (df - kf)) % L := by
            rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L), ← Nat.add_mod]
      _ = (pf + df) % L := by rw [show pf + kf + (df - kf) = pf + df from by omega]
      _ = q := hpfdf



namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}

/-- A boundary chord is symmetric in its endpoints. -/
def chord_symm (h : hNT.outerCycle.Chord u v) : hNT.outerCycle.Chord v u where
  endpoints_ne := h.endpoints_ne.symm
  left_boundary := h.right_boundary
  right_boundary := h.left_boundary
  adj := h.adj.symm
  not_boundary_edge := by rw [Sym2.eq_swap]; exact h.not_boundary_edge







/-- Consecutive positions of a chord's endpoints cannot be adjacent: a `1`-step would make the chord
a boundary edge. -/
lemma not_consecutive_of_chord (h : hNT.outerCycle.Chord u v) {p q : ℕ}
    (hp : p < hNT.outerCycle.darts.length) (hq : q < hNT.outerCycle.darts.length)
    (htu : M.tail (hNT.outerCycle.darts[p]'hp) = u)
    (htv : M.tail (hNT.outerCycle.darts[q]'hq) = v)
    (hadj : (p + 1) % hNT.outerCycle.darts.length = q) : False := by
  set C := hNT.outerCycle
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  have hcv := C.consecutive_vertex ⟨p, hp⟩
  have hcyc : (cyclicNext C.normalized.length_pos ⟨p, hp⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext; show (p + 1) % L = q; exact hadj
  rw [hcyc] at hcv
  have hhead : M.head (C.darts[p]'hp) = v := by
    rw [show (C.darts.get ⟨q, hq⟩) = C.darts[q]'hq from rfl,
        show (C.darts.get ⟨p, hp⟩) = C.darts[p]'hp from rfl] at hcv
    rw [← hcv, htv]
  apply h.not_boundary_edge
  show s(u, v) ∈ C.edges
  rw [C.edges_eq, show (s(u, v) : Sym2 M.Vertex) = M.dartEdge (C.darts[p]'hp) from by
    show s(u, v) = s(M.tail _, M.head _); rw [htu, hhead]]
  exact List.mem_map_of_mem (List.getElem_mem hp)



structure NormalizedRuns (h : hNT.outerCycle.Chord u v) where
  /-- The `u → v` boundary run. -/
  arcUV : DartArc M hNT.outerCycle u v
  /-- The `v → u` boundary run. -/
  arcVU : DartArc M hNT.outerCycle v u
  /-- Both runs have length `≥ 2`. -/
  lenUV : 2 ≤ arcUV.len
  lenVU : 2 ≤ arcVU.len
  /-- Every boundary vertex is a tail of one of the two runs, or an endpoint. -/
  covering : ∀ {w : M.Vertex}, hNT.outerCycle.IsBoundaryVertex w →
    (∃ i, M.tail (arcUV.arcDart i) = w) ∨ (∃ i, M.tail (arcVU.arcDart i) = w) ∨ w = u ∨ w = v
  /-- A vertex that is a tail of *both* runs is a chord endpoint. -/
  disjoint : ∀ {w : M.Vertex}, (∃ i, M.tail (arcUV.arcDart i) = w) →
    (∃ i, M.tail (arcVU.arcDart i) = w) → w = u ∨ w = v

/-- **Build the normalized runs from a chord.** -/
noncomputable def normalizedRuns (h : hNT.outerCycle.Chord u v) : NormalizedRuns h := by
  classical
  set C := hNT.outerCycle with hC
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  -- positions of u, v
  have eu0 := (C.exists_pos_of_isBoundaryVertex h.left_boundary).choose_spec
  have ev0 := (C.exists_pos_of_isBoundaryVertex h.right_boundary).choose_spec
  set puF := (C.exists_pos_of_isBoundaryVertex h.left_boundary).choose with hpuF
  set pvF := (C.exists_pos_of_isBoundaryVertex h.right_boundary).choose with hpvF
  set pu := puF.1 with hpuval
  set pv := pvF.1 with hpvval
  have hpu : pu < L := puF.2
  have hpv : pv < L := pvF.2
  have eu : M.tail (C.darts[pu]'hpu) = u := eu0
  have ev : M.tail (C.darts[pv]'hpv) = v := ev0
  have hpune : pu ≠ pv := by
    intro hpe; apply h.endpoints_ne
    rw [← eu, ← ev]
    have : C.darts[pu]'hpu = C.darts[pv]'hpv := getElem_congr rfl hpe hpu
    rw [this]
  -- run lengths
  set kf := (pv + L - pu) % L with hkf
  set kb := (pu + L - pv) % L with hkb
  obtain ⟨hkf1, hkb1, hsum, hpfkf, hcov⟩ := mod_cover L pu pv hLpos hpu hpv hpune kf kb hkf hkb
  -- (pv + kb) % L = pu, from the symmetric mod_cover call
  obtain ⟨_, _, _, hpvkb, _⟩ := mod_cover L pv pu hLpos hpv hpu (Ne.symm hpune) kb kf hkb hkf
  have hkfL : kf < L := by rw [hkf]; exact Nat.mod_lt _ hLpos
  have hkbL : kb < L := by rw [hkb]; exact Nat.mod_lt _ hLpos
  -- kf ≥ 2
  have hkf2 : 2 ≤ kf := by
    rcases Nat.lt_or_ge kf 2 with hlt | hge
    · exfalso
      have hkf1' : kf = 1 := by omega
      apply not_consecutive_of_chord h hpu hpv eu ev
      rw [show (pu + 1) % L = (pu + kf) % L from by rw [hkf1'], hpfkf]
    · exact hge
  have hkb2 : 2 ≤ kb := by
    rcases Nat.lt_or_ge kb 2 with hlt | hge
    · exfalso
      have hkb1' : kb = 1 := by omega
      exact not_consecutive_of_chord (chord_symm h) hpv hpu ev eu
        (by rw [show (pv + 1) % L = (pv + kb) % L from by rw [hkb1'], hpvkb])
    · exact hge
  -- the two raw runs
  set AUV := C.cyclicDartArc hNT.outer_simple pu kf hkf1 hkfL hpu with hAUV
  set AVU := C.cyclicDartArc hNT.outer_simple pv kb hkb1 hkbL hpv with hAVU
  -- endpoint equalities for casting
  have euv2 : M.tail (C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega))) = v := by
    have : C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pv]'hpv := by congr 1
    rw [this]; exact ev
  have evu2 : M.tail (C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega))) = u := by
    have : C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pu]'hpu := by congr 1
    rw [this]; exact eu
  -- arcUV : DartArc u v, arcVU : DartArc v u (via daCast through the raw runs)
  -- We use bpCast-style transport at the DartArc level via subst inside the structure proofs;
  -- here we just record the runs typed as cyclicDartArc and rewrite endpoints by `eu`/`euv2`.
  -- tail characterizations: the casted runs' tails are exactly the cyclic-slice tails.
  have htailUV : ∀ i : Fin (daCast AUV eu euv2).len,
      M.tail ((daCast AUV eu euv2).arcDart i)
        = M.tail (C.darts[(pu + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hNT.outer_simple pu kf hkf1 hkfL hpu eu euv2 i
  have htailVU : ∀ i : Fin (daCast AVU ev evu2).len,
      M.tail ((daCast AVU ev evu2).arcDart i)
        = M.tail (C.darts[(pv + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hNT.outer_simple pv kb hkb1 hkbL hpv ev evu2 i
  have htailUV_fwd : ∀ j : ℕ, (hj : j < kf) →
      ∃ i : Fin (daCast AUV eu euv2).len,
        M.tail ((daCast AUV eu euv2).arcDart i)
          = M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCast AUV eu euv2).len := by rw [daCast_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailUV ⟨j, hjlen⟩⟩
  have htailVU_fwd : ∀ j : ℕ, (hj : j < kb) →
      ∃ i : Fin (daCast AVU ev evu2).len,
        M.tail ((daCast AVU ev evu2).arcDart i)
          = M.tail (C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCast AVU ev evu2).len := by rw [daCast_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailVU ⟨j, hjlen⟩⟩
  have htailUV_bwd : ∀ i : Fin (daCast AUV eu euv2).len,
      ∃ j : ℕ, j < kf ∧
        M.tail ((daCast AUV eu euv2).arcDart i)
          = M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kf := lt_of_lt_of_eq i.2 (daCast_len AUV eu euv2)
    exact ⟨i.1, hi, htailUV i⟩
  have htailVU_bwd : ∀ i : Fin (daCast AVU ev evu2).len,
      ∃ j : ℕ, j < kb ∧
        M.tail ((daCast AVU ev evu2).arcDart i)
          = M.tail (C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kb := lt_of_lt_of_eq i.2 (daCast_len AVU ev evu2)
    exact ⟨i.1, hi, htailVU i⟩
  refine
    { arcUV := daCast AUV eu euv2
      arcVU := daCast AVU ev evu2
      lenUV := ?_
      lenVU := ?_
      covering := ?_
      disjoint := ?_ }
  · rw [daCast_len]; exact hkf2
  · rw [daCast_len]; exact hkb2
  · -- covering
    intro w hw
    -- w is tail of darts[q] for some q < L
    obtain ⟨q, hqt⟩ := C.exists_pos_of_isBoundaryVertex hw
    rcases hcov q.1 q.2 with ⟨j, hj, hjq⟩ | ⟨j, hj, hjq⟩
    · -- w on arcUV (positions pu+j)
      left
      obtain ⟨i, hi⟩ := htailUV_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
    · -- w on arcVU (positions pv+j)
      right; left
      obtain ⟨i, hi⟩ := htailVU_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
  · -- disjoint: a vertex on both runs is u or v
    rintro w ⟨i, hiw⟩ ⟨i', hi'w⟩
    obtain ⟨j, hj, hjeq⟩ := htailUV_bwd i
    obtain ⟨j', hj', hj'eq⟩ := htailVU_bwd i'
    -- tail darts[(pu+j)%L] = w = tail darts[(pv+j')%L]
    have heq : M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)))
        = M.tail (C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega))) := by
      rw [← hjeq, ← hj'eq, hiw, hi'w]
    -- by VertexNodup, the dart positions coincide: (pu+j)%L = (pv+j')%L
    have hmap : (C.darts.map M.tail).Nodup := by
      have := hNT.outer_simple
      rwa [BoundaryCycle.VertexNodup, C.vertices_eq] at this
    have hposeq : (pu + j) % L = (pv + j') % L := by
      have hmem1 : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) ∈ C.darts :=
        List.getElem_mem _
      have hmem2 : C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) ∈ C.darts :=
        List.getElem_mem _
      have hdarts : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))
          = C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) :=
        List.inj_on_of_nodup_map hmap hmem1 hmem2 heq
      exact (C.normalized.nodup.getElem_inj_iff).mp hdarts
    -- positions: pu+j with j<kf and pv+j' with j'<kb, kf+kb=L, complementary ⟹ j=0 or j'=0.
    -- (pu+0)%L=pu↦u, (pv+0)%L=pv↦v. Since ranges are complementary, equality forces a boundary.
    -- We show w ∈ {u,v} by: the only shared position is when one of j,j' is 0.
    -- pu+j ≡ pv+j' (mod L). Using (pv+kb)%L=pu i.e. pv ≡ pu - kb, get j ≡ j' - kb (mod L);
    -- with 0≤j<kf, 0≤j'<kb, kf+kb=L: j' - kb ∈ (-kb, kf-kb] so j ≡ that; the only solution in
    -- [0,kf) is j = j' + kf (impossible unless ...). Cleanest: case j=0 ∨ j'=0.
    by_cases hj0 : j = 0
    · -- w = tail darts[pu] = u
      left
      rw [← hiw, hjeq, hj0]
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hpu]
      exact eu
    · by_cases hj'0 : j' = 0
      · right
        rw [← hi'w, hj'eq, hj'0]
        simp only [Nat.add_zero, Nat.mod_eq_of_lt hpv]
        exact ev
      · -- both j,j' ≥ 1: derive contradiction from complementary ranges
        exfalso
        -- (pu+j) ≡ (pv+j') (mod L), and pv ≡ (pu+kf) (mod L), so j ≡ kf+j' (mod L).
        have hpvmod : pv % L = (pu + kf) % L := by rw [hpfkf, Nat.mod_eq_of_lt hpv]
        -- pu+j ≡ pu+kf+j' (mod L)
        have h2 : Nat.ModEq L pv (pu + kf) := by
          show pv % L = (pu + kf) % L; exact hpvmod
        have hcong : Nat.ModEq L (pu + j) (pu + (kf + j')) := by
          have h1 : Nat.ModEq L (pu + j) (pv + j') := hposeq
          have h3 : Nat.ModEq L (pv + j') (pu + kf + j') := h2.add_right j'
          have h4 : Nat.ModEq L (pu + j) (pu + kf + j') := h1.trans h3
          rwa [show pu + kf + j' = pu + (kf + j') from by ring] at h4
        -- cancel pu: j ≡ kf + j' (mod L)
        have hcong' : Nat.ModEq L j (kf + j') := Nat.ModEq.add_left_cancel' pu hcong
        -- both sides < L; equal
        have hjlt : j < L := by omega
        have hkfj' : kf + j' < L := by omega
        have : j = kf + j' := by
          have hj1 : j % L = j := Nat.mod_eq_of_lt hjlt
          have hj2 : (kf + j') % L = kf + j' := Nat.mod_eq_of_lt hkfj'
          rw [Nat.ModEq, hj1, hj2] at hcong'; exact hcong'
        omega



/-- **The normalized boundary arc-split**: `path₂` is the `v → u` run, `path₁` the `u → v` run. -/
noncomputable def normalizedArcSplit (h : hNT.outerCycle.Chord u v) :
    BoundaryArcSplit M hNT.outerCycle.vertices hNT.outerCycle.edges u v :=
  let R := normalizedRuns h
  { path₁ := bpOfDartArc R.arcUV
    path₂ := bpOfDartArc R.arcVU
    path₁_boundary_vertices := fun {w} hw =>
      bpOfDartArc_boundary_vertices R.arcUV h.right_boundary hw
    path₂_boundary_vertices := fun {w} hw =>
      bpOfDartArc_boundary_vertices R.arcVU h.left_boundary hw
    boundary_vertices_covered := by
      intro w
      constructor
      · intro hw
        rcases R.covering hw with ⟨i, hi⟩ | ⟨i, hi⟩ | hwu | hwv
        · left
          rw [bpOfDartArc_vertices, List.mem_append]
          refine Or.inl ?_
          rw [← hi]
          show M.tail (R.arcUV.arcDart i) ∈ R.arcUV.dartList.map M.tail
          exact List.mem_map_of_mem (by
            show R.arcUV.arcDart i ∈ R.arcUV.dartList
            rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
        · right
          rw [bpOfDartArc_vertices, List.mem_append]
          refine Or.inl ?_
          rw [← hi]
          show M.tail (R.arcVU.arcDart i) ∈ R.arcVU.dartList.map M.tail
          exact List.mem_map_of_mem (by
            show R.arcVU.arcDart i ∈ R.arcVU.dartList
            rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
        · -- w = u: u is the tail of arcUV's first dart.
          left
          rw [bpOfDartArc_vertices, List.mem_append]
          refine Or.inl ?_
          have hu_tail : M.tail (R.arcUV.arcDart R.arcUV.firstIdx) = w :=
            R.arcUV.tail_first.trans hwu.symm
          have hmem : M.tail (R.arcUV.arcDart R.arcUV.firstIdx) ∈ R.arcUV.dartList.map M.tail :=
            List.mem_map_of_mem (by
              rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange _))
          exact hu_tail ▸ hmem
        · -- w = v: v is the terminal endpoint of path₁.
          left
          rw [bpOfDartArc_vertices, List.mem_append]
          exact Or.inr (by rw [hwv]; exact List.mem_singleton_self _)
      · intro hw
        rcases hw with hw | hw
        · exact bpOfDartArc_boundary_vertices R.arcUV h.right_boundary hw
        · exact bpOfDartArc_boundary_vertices R.arcVU h.left_boundary hw
    internally_disjoint := by
      intro w hw1 hw2
      obtain ⟨i, hi⟩ := bpOfDartArc_internal_tail R.arcUV hw1
      obtain ⟨i', hi'⟩ := bpOfDartArc_internal_tail R.arcVU hw2
      -- w ∈ {u, v} by disjoint; but w is internal to path₁, so w ≠ u, w ≠ v.
      have hwuv : w = u ∨ w = v := R.disjoint ⟨i, hi⟩ ⟨i', hi'⟩
      have hwu : w ≠ u := (bpOfDartArc R.arcUV).internalVertex_ne_start hw1
      have hwv : w ≠ v := (bpOfDartArc R.arcUV).internalVertex_ne_end hw1
      rcases hwuv with h' | h'
      · exact hwu h'
      · exact hwv h'
    path₁_internal_of_proper := fun _ => bpOfDartArc_hasInternal R.arcUV R.lenUV
    path₂_internal_of_proper := fun _ => bpOfDartArc_hasInternal R.arcVU R.lenVU }

/-- **The normalized chord-split datum** built from a chord. -/
noncomputable def normalizedChordSplitData (h : hNT.outerCycle.Chord u v) :
    hNT.ChordSplitData u v :=
  { chord := h
    arc := normalizedArcSplit h
    arc₁_internal := bpOfDartArc_hasInternal (normalizedRuns h).arcUV (normalizedRuns h).lenUV
    arc₂_internal := bpOfDartArc_hasInternal (normalizedRuns h).arcVU (normalizedRuns h).lenVU }





/-- **`ArcSideIdentification` for the normalized datum, given the aligned chord-dart orientation.** -/
theorem arcSideIdentification_normalized (h : hNT.outerCycle.Chord u v)
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v) :
    ProofsInTheBook.ZinanCh35BankOrient.ArcSideIdentification (normalizedChordSplitData h) := by
  classical
  set data := normalizedChordSplitData h with hdata
  set R := normalizedRuns h with hR
  refine ⟨?_, ?_⟩
  · -- path₁-internal ⊆ sideRegion₁ (arcUV is the backward run u → v = DartArc (tail dart)(head dart))
    intro w hw
    have hw' : w ∈ (bpOfDartArc R.arcUV).internalVertices := hw
    obtain ⟨i, hi⟩ := bpOfDartArc_internal_tail R.arcUV hw'
    -- arcUV : DartArc u v = DartArc (tail dart)(head dart); reverse faces ∈ side₁.
    have hB : M.dartFace (M.α ((daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (daCast_len R.arcUV htu.symm hhv.symm).symm i))) ∈ data.side₁ :=
      bwdRun_reverse_face_mem_side₁ data (daCast R.arcUV htu.symm hhv.symm) (by rw [daCast_len]; exact R.lenUV) _
    -- the casted dart is the same dart: tail = w, reverse face ∈ side₁.
    have hsame : (daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (daCast_len R.arcUV htu.symm hhv.symm).symm i) = R.arcUV.arcDart i := by
      rw [daCast_arcDart_eq]; congr 1
    rw [hsame] at hB
    have hchord : M.dartEdge (R.arcUV.arcDart i) ≠ s(u, v) := by
      intro he
      apply h.not_boundary_edge
      rw [← he]; show M.dartEdge (R.arcUV.arcDart i) ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]; exact List.mem_map_of_mem (R.arcUV.boundary i)
    have := ProofsInTheBook.ZinanCh35Side2Confine.endpoints_mem_sideRegion₁_of_face data hsep
      (by rw [M.dartEdge_alpha]; exact hchord) hB
    rw [M.head_alpha] at this
    rw [← hi]; exact this.2
  · -- path₂-internal ⊆ sideRegion₂ (arcVU is the forward run v → u = DartArc (head dart)(tail dart))
    intro w hw
    have hw' : w ∈ (bpOfDartArc R.arcVU).internalVertices := hw
    obtain ⟨i, hi⟩ := bpOfDartArc_internal_tail R.arcVU hw'
    have hF : M.dartFace (M.α ((daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (daCast_len R.arcVU hhv.symm htu.symm).symm i))) ∈ data.side₂ :=
      fwdRun_reverse_face_mem_side₂ data (daCast R.arcVU hhv.symm htu.symm) (by rw [daCast_len]; exact R.lenVU) _
    have hsame : (daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (daCast_len R.arcVU hhv.symm htu.symm).symm i) = R.arcVU.arcDart i := by
      rw [daCast_arcDart_eq]; congr 1
    rw [hsame] at hF
    have hchord : M.dartEdge (R.arcVU.arcDart i) ≠ s(u, v) := by
      intro he
      apply h.not_boundary_edge
      rw [← he]; show M.dartEdge (R.arcVU.arcDart i) ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]; exact List.mem_map_of_mem (R.arcVU.boundary i)
    have := ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.dartRun_tail_mem_sideRegion₂_of_face
      data hsep hchord hF
    rw [← hi]; exact this

/-- **Both Chapter-35 confinements for the normalized datum** (aligned chord-dart orientation).
`ArcSideIdentification` is discharged BY CONSTRUCTION — `path₂` *is* the forward `v → u` run, so its
internal vertices are bank-side-2 facts, not a free Jordan input — and routed through
`ZinanCh35BankOrient.bothConfinements_of_arcSide`.  The only remaining hypotheses are the chord-level
`Separates` keystone and the 2-valued chord-dart orientation `tail dart = u`, `head dart = v` (a
finite combinatorial selector on the opaque `chordDart` choice, NOT the discrete-Jordan datum). -/
theorem bothConfinements_normalized (h : hNT.outerCycle.Chord u v)
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v) :
    ProofsInTheBook.ZinanCh35Schoenflies.Side₁StarConfinement (normalizedChordSplitData h) ∧
      ProofsInTheBook.ZinanCh35Side2.Side₂SchoenfliesConfinementInput
        (normalizedChordSplitData h) hsep :=
  ProofsInTheBook.ZinanCh35BankOrient.bothConfinements_of_arcSide (normalizedChordSplitData h) hsep
    (arcSideIdentification_normalized h hsep htu hhv)







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



/-- Side-1 certificate inputs minus the confinement (produced from `Side₁StarConfinement`). -/
structure Side₁InputsNoConf (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α) where
  ci : ContiguousInterval data hsep a₀ a₁ hne
  hshare : ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁
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
  /-- The boundary-incidence residual feeding the outer-dart half of the `edge_confined`
  reduction `Side₁StarConfinement → Side₁SchoenfliesConfinement`. -/
  houter : ProofsInTheBook.ZinanCh35Schoenflies.OuterDartArc₁ data

/-- Side-2 certificate inputs minus the confinement (produced as
`Side₂SchoenfliesConfinementInput` directly). -/
structure Side₂InputsNoConf (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α) where
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



/-- The side-1 `Side₁SchoenfliesConfinementInput` from the star confinement and `OuterDartArc₁`. -/
theorem side₁ConfInput_of_star (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (conf : ProofsInTheBook.ZinanCh35Schoenflies.Side₁StarConfinement data)
    (houter : ProofsInTheBook.ZinanCh35Schoenflies.OuterDartArc₁ data) :
    ProofsInTheBook.ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput data hsep :=
  ProofsInTheBook.ZinanCh35FinalClose.confinementInput_of_schoenflies data hsep
    (ProofsInTheBook.ZinanCh35Schoenflies.vertexStar_confined_of_starConfinement data hsep conf houter)



/-- The side-1 reconstruction `ChordSideReconstruction hNT (sideRegion₁ data) L`, with the
confinement field produced from `Side₁StarConfinement` + `OuterDartArc₁`. -/
noncomputable def side₁Reconstruction_of_noConf (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α) (I : Side₁InputsNoConf data hsep a₀ a₁ hne L)
    (conf : ProofsInTheBook.ZinanCh35Schoenflies.Side₁StarConfinement data) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₁ data) L :=
  ProofsInTheBook.ZinanCh35Cert.side₁Reconstruction_of_certificateInputs data hsep a₀ a₁ hne L
    { ci := I.ci, hshare := I.hshare, hchord := I.hchord, ha₀ := I.ha₀, ha₁ := I.ha₁,
      pₛ := I.pₛ, qₛ := I.qₛ, cpₛ := I.cpₛ, cqₛ := I.cqₛ, hLₛ := I.hLₛ,
      confinement := side₁ConfInput_of_star data hsep conf I.houter }

/-- The side-2 reconstruction `ChordSideReconstruction hNT (sideRegion₂ data) L`, with the
confinement field produced as `Side₂SchoenfliesConfinementInput`. -/
noncomputable def side₂Reconstruction_of_noConf (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α) (I : Side₂InputsNoConf data hsep a₀ a₁ hne L)
    (conf : ProofsInTheBook.ZinanCh35Side2.Side₂SchoenfliesConfinementInput data hsep) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ data) L :=
  ProofsInTheBook.ZinanCh35Side2.side₂Reconstruction_of_certificateInputs data hsep a₀ a₁ hne L
    { hdisk := I.hdisk, hshare := I.hshare, ci := I.ci, hchord := I.hchord, ha₀ := I.ha₀,
      ha₁ := I.ha₁, pₛ := I.pₛ, qₛ := I.qₛ, cpₛ := I.cpₛ, cqₛ := I.cqₛ, hLₛ := I.hLₛ,
      confinement := conf }



/-- Abbreviation for the normalized split datum of a chord. -/
local notation3 "ND " h => ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h

/-- The genuinely-unproduced planar residue of one chord branch (confinements excluded). -/
structure ChordBranchResidualData (h : hNT.outerCycle.Chord u v)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) where
  /-- The chord separation keystone (`face₂ ∉ side₁`).  No unconditional producer. -/
  hsep : (ND h).Separates
  /-- The chord-dart standard orientation (`tail dart = u`). -/
  htu : M.tail (ND h).dart = u
  /-- The chord-dart standard orientation (`head dart = v`). -/
  hhv : M.head (ND h).dart = v
  /-- The `M`-vertex-level chord split regions glue, pinned to the side regions. -/
  regions : ChordSplitRegions hNT u v p q L cp cq
  regions_s₁ : regions.s₁ = sideRegion₁ (ND h)
  regions_s₂ : regions.s₂ = sideRegion₂ (ND h)
  /-- The selected side-1 anchor realizing `u`. -/
  a₁₀ : {d : D // d ∉ (ND h).keptDel₁}
  /-- The selected side-1 anchor realizing `v`. -/
  a₁₁ : {d : D // d ∉ (ND h).keptDel₁}
  ha₁₀ : M.tail a₁₀.1 = u
  ha₁₁ : M.tail a₁₁.1 = v
  hne₁ : a₁₀ ≠ a₁₁
  /-- The side-1 certificate inputs WITHOUT confinement, at the stored anchors. -/
  side₁ : Side₁InputsNoConf (ND h) hsep a₁₀ a₁₁ hne₁ L
  /-- The selected side-2 anchor realizing `u`. -/
  a₂₀ : {d : D // d ∉ (ND h).keptDel₂}
  /-- The selected side-2 anchor realizing `v`. -/
  a₂₁ : {d : D // d ∉ (ND h).keptDel₂}
  ha₂₀ : M.tail a₂₀.1 = u
  ha₂₁ : M.tail a₂₁.1 = v
  hne₂ : a₂₀ ≠ a₂₁
  /-- The side-2 certificate inputs WITHOUT confinement, at the stored anchors and for each
  forced-list coloring whose chord-endpoint colors are distinct. -/
  side₂ : ∀ c₁ : M.Vertex → α, c₁ u ≠ c₁ v →
    Side₂InputsNoConf (ND h) hsep a₂₀ a₂₁ hne₂ (regions.forcedLists c₁ L)
  uv_ne : u ≠ v

/-- **The chord-branch residue from the residual bundle (confinements produced).**  Assembles a
`ChordSplitFinal.ChordBranchResidue hNT u v p q L cp cq` for the standard-orientation chord: the
`regions` glue is taken from the bundle, and the two side reconstructions are built by
`side₁/₂Reconstruction_of_noConf` — consuming the confinements PRODUCED from
`bothConfinements_normalized`, not posited.  The side reconstructions land on
`sideRegion₁/₂ (ND h)` and are transported onto `regions.s₁/s₂` along the pinning equalities. -/
noncomputable def chordBranchResidue_of_residualData {h : hNT.outerCycle.Chord u v}
    {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}
    (R : ChordBranchResidualData h p q L cp cq) :
    ChordBranchResidue hNT u v p q L cp cq := by
  classical
  -- both confinements, produced (not posited) from the normalized arc↔side identification.
  obtain ⟨conf₁, conf₂⟩ :=
    ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.bothConfinements_normalized
      h R.hsep R.htu R.hhv
  have rec₁₀ : ChordSplitNT.ChordSideReconstruction hNT (sideRegion₁ (ND h)) L :=
    side₁Reconstruction_of_noConf (ND h) R.hsep R.a₁₀ R.a₁₁ R.hne₁ L R.side₁ conf₁
  refine
    { regions := R.regions
      uv_ne := R.uv_ne
      R₁ := R.regions_s₁ ▸ rec₁₀
      R₂ := ?_ }
  -- side-2 reconstruction family on `sideRegion₂ (ND h)`, transported to `regions.s₂`,
  -- with the forced lists from `regions`.
  intro c₁ hcuv
  have rec₂₀ : ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ (ND h))
      (R.regions.forcedLists c₁ L) :=
    side₂Reconstruction_of_noConf (ND h) R.hsep R.a₂₀ R.a₂₁ R.hne₂
      (R.regions.forcedLists c₁ L) (R.side₂ c₁ hcuv) conf₂
  exact R.regions_s₂ ▸ rec₂₀



/-- **The uniform residual supplier** — for every near-triangulation with the Thomassen lists and
a chord witness, the per-chord residue bundle (confinements excluded), at whatever endpoint
ordering makes the chord-dart orientation standard.  The supplier returns the standard-oriented
endpoint pair `(u', v')`, the chord `h'` on them, the witnessing orientation equalities, and the
residual data — pushing the (genuine, 2-valued) orientation selection into the planar-residue
layer where the side regions live. -/
structure ChordBranchResidualSupplier (α : Type u) [DecidableEq α] : Type (u + 1) where
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), ThomassenLists hNT p q L cp cq →
      (∃ u v : M.Vertex, hNT.outerCycle.Chord u v) →
        Σ' (u' v' : M.Vertex) (h' : hNT.outerCycle.Chord u' v'),
          ChordBranchResidualData h' p q L cp cq

/-- **The `ChordBranchSupplier`, assembled from the uniform residual supplier.**

Given the uniform residual supplier (the discrete-Jordan content with confinements excluded), the
chord-branch supplier is dischargeable: under a true chord witness, the residual supplier delivers
a standard-oriented chord with its residue bundle, which `chordBranchResidue_of_residualData`
routes into a `ChordBranchResidue` — PRODUCING both confinements from
`bothConfinements_normalized` (not positing them).  The result is the `Σ' u v, ChordBranchResidue`
the supplier owes.

`CONDITIONAL` on `ChordBranchResidualSupplier`; the confinement production and branch-residue
assembly are UNCONDITIONAL. -/
noncomputable def chordBranchSupplier_of_residual
    (S : ChordBranchResidualSupplier α) :
    ProofsInTheBook.ZinanCh35Dichotomy.ChordBranchSupplier α where
  supply := by
    intro D _ _ M hNT p q L cp cq hTL hchord
    obtain ⟨u', v', h', R⟩ := S.supply hNT p q L cp cq hTL hchord
    exact ⟨u', v', chordBranchResidue_of_residualData R⟩









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

/-- The (unconditional) separation of the normalized split datum of a chord. -/
noncomputable abbrev normSep (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData h).Separates :=
  hNT.separates_of_chordSplitData (normalizedChordSplitData h)



/-- **The canonical side-1 anchor `a₀` sits at the chord endpoint `u = tail dart`.** -/
theorem canonicalAnchor₀_tail (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail (side₁Anchor₀ data hsep).1 = M.tail data.dart := by
  have hfix : M.tail (data.sideSigma₁ (side₁Anchor₀ data hsep) : D)
      = M.tail (side₁Anchor₀ data hsep).1 := by
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
      tail_filteredRotation data.keptDel₁ (side₁Anchor₀ data hsep)]
  rw [← hfix, sideSigma₁_side₁Anchor₀ data hsep, keptPhi_face₁Dart₂_tail data hsep]

/-- **The canonical side-1 anchor `a₁` sits at the chord endpoint `v = head dart`.** -/
theorem canonicalAnchor₁_tail (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail (side₁Anchor₁ data hsep).1 = M.head data.dart := by
  have hfix : M.tail (data.sideSigma₁ (side₁Anchor₁ data hsep) : D)
      = M.tail (side₁Anchor₁ data hsep).1 := by
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
      tail_filteredRotation data.keptDel₁ (side₁Anchor₁ data hsep)]
  rw [← hfix, sideSigma₁_side₁Anchor₁ data hsep, face₁Dart₁_tail data]

/-- **The chord endpoint `u = tail dart` lies in the side-1 region.**  Witnessed by the canonical
anchor `a₀` (a kept side-1 dart) whose tail is `u`. -/
theorem tailDart_mem_sideRegion₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail data.dart ∈ sideRegion₁ data :=
  ⟨(side₁Anchor₀ data hsep).1, (side₁Anchor₀ data hsep).2,
    canonicalAnchor₀_tail data hsep⟩

/-- **The chord endpoint `v = head dart` lies in the side-1 region.**  Witnessed by `a₁`. -/
theorem headDart_mem_sideRegion₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.head data.dart ∈ sideRegion₁ data :=
  ⟨(side₁Anchor₁ data hsep).1, (side₁Anchor₁ data hsep).2,
    canonicalAnchor₁_tail data hsep⟩



/-- **The genuinely-unproduced fields of the `M`-vertex-level region glue.**  Everything else
(`overlap`, the side-1 chord-end memberships, `chord_adj`) is produced unconditionally below; these
are exactly the fields with no producer in the checkout: the vertex `cover`, the vertex-level
`edge_confined`, the side-2 chord-end memberships, and the precolored-edge memberships. -/
structure ChordSplitRegionsResidue (data : hNT.ChordSplitData u v)
    (p q : M.Vertex) where
  /-- Vertex cover: every vertex is in side 1 or side 2. -/
  cover : ∀ w : M.Vertex, w ∈ sideRegion₁ data ∨ w ∈ sideRegion₂ data
  /-- Vertex-level edge confinement (the open discrete-Schoenflies item). -/
  edge_confined : ∀ ⦃a b : M.Vertex⦄, M.toSimpleGraph.Adj a b →
    (a ∈ sideRegion₁ data ∧ b ∈ sideRegion₁ data) ∨
    (a ∈ sideRegion₂ data ∧ b ∈ sideRegion₂ data)
  /-- The chord endpoints lie in the side-2 region. -/
  u_s₂ : M.tail data.dart ∈ sideRegion₂ data
  v_s₂ : M.head data.dart ∈ sideRegion₂ data
  /-- The precolored endpoints lie in the side-1 region. -/
  p_s₁ : p ∈ sideRegion₁ data
  q_s₁ : q ∈ sideRegion₁ data

/-- **The full `ChordSplitRegions` from the structural residue.**  The two sides are pinned to
`sideRegion₁ / sideRegion₂`; `overlap`, the side-1 chord-end memberships, and `chord_adj` are
PRODUCED (σ-star intersection / canonical anchors / `chordChoice_adj`) — only the residue's fields
are consumed.  Built for the standard chord-dart orientation `tail dart = u`, `head dart = v`. -/
noncomputable def chordSplitRegions_of_residue
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (htu : M.tail data.dart = u) (hhv : M.head data.dart = v)
    {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}
    (res : ChordSplitRegionsResidue data p q) :
    ChordSplitRegions hNT u v p q L cp cq where
  s₁ := sideRegion₁ data
  s₂ := sideRegion₂ data
  cover := res.cover
  edge_confined := res.edge_confined
  overlap := by
    intro w hw
    rcases sideRegionInterChordEnds_holds data hsep hw.1 hw.2 with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))
  u_s₁ := ⟨(side₁Anchor₀ data hsep).1, (side₁Anchor₀ data hsep).2,
    (canonicalAnchor₀_tail data hsep).trans htu⟩
  v_s₁ := ⟨(side₁Anchor₁ data hsep).1, (side₁Anchor₁ data hsep).2,
    (canonicalAnchor₁_tail data hsep).trans hhv⟩
  u_s₂ := by
    obtain ⟨d, hd, he⟩ := res.u_s₂; exact ⟨d, hd, he.trans htu⟩
  v_s₂ := by
    obtain ⟨d, hd, he⟩ := res.v_s₂; exact ⟨d, hd, he.trans hhv⟩
  p_s₁ := res.p_s₁
  q_s₁ := res.q_s₁
  chord_adj := ProofsInTheBook.ChordContiguous.chordChoice_adj data



















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



/-- **The chord endpoint `v = head dart` lies in `sideRegion₂`.**  The first forward-run arc dart
has tail `v` and lies in `sideRegion₂`. -/
theorem headDart_mem_sideRegion₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.head data.dart ∈ sideRegion₂ data := by
  have h := fwdArc_tail_mem_sideRegion₂ data hsep (fwdArc data).firstIdx
  rwa [(fwdArc data).tail_firstIdx] at h

/-- **The chord endpoint `u = tail dart` lies in `sideRegion₂`.**  The last forward-run arc dart has
head `u`; its reverse face is in `side₂`, so the head-variant bridge places `u` in `sideRegion₂`. -/
theorem tailDart_mem_sideRegion₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail data.dart ∈ sideRegion₂ data := by
  have h :=
    ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.dartRun_head_mem_sideRegion₂_of_face
      data hsep (fwdArc_dartEdge_ne_chord data (fwdArc data).lastIdx)
      (fwdArc_reverse_face_mem_side₂ data (fwdArc data).lastIdx)
  rwa [(fwdArc data).head_lastIdx] at h



/-- **Every vertex is the tail of a non-outer dart.**  Pick any dart `d₀` with `tail d₀ = w`; if its
face is outer, `M.σ d₀` shares the tail (`tail_sigma`) and is non-outer (its face equals
`dartFace (M.α d₀)`, non-outer by `alpha_dartFace_ne_outer_of_outer`). -/
theorem exists_nonouter_dart_tail (w : M.Vertex) :
    ∃ d : D, M.tail d = w ∧ M.dartFace d ≠ hNT.outerFace := by
  obtain ⟨d₀, hd₀⟩ := Quotient.exists_rep w
  have htail₀ : M.tail d₀ = w := hd₀
  by_cases ho : M.dartFace d₀ = hNT.outerFace
  · refine ⟨M.σ d₀, ?_, ?_⟩
    · rw [M.tail_sigma]; exact htail₀
    · rw [ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha d₀]
      exact alpha_dartFace_ne_outer_of_outer hNT ho
  · exact ⟨d₀, htail₀, ho⟩

/-- **The vertex cover** (the `cover` field of `ChordSplitRegions`).  Every `M`-vertex lies in
`sideRegion₁ ∪ sideRegion₂`. -/
theorem cover_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ w : M.Vertex, w ∈ sideRegion₁ data ∨ w ∈ sideRegion₂ data := by
  intro w
  obtain ⟨d, htail, hnonouter⟩ := exists_nonouter_dart_tail (hNT := hNT) w
  rcases boundedFacePartition_uncond data hnonouter with hs₁ | hs₂
  · left
    by_cases hd : d = data.dart
    · subst hd; rw [← htail]; exact tailDart_mem_sideRegion₁ data hsep
    · have hkept : d ∈ data.keptSet₁ := ⟨Or.inl hs₁, by simp only [Set.mem_singleton_iff]; exact hd⟩
      rw [← htail]; exact ⟨d, (data.mem_keptDel₁_iff d).2 hkept, rfl⟩
  · right
    by_cases hd : d = M.α data.dart
    · subst hd; rw [← htail, M.tail_alpha]; exact headDart_mem_sideRegion₂ data hsep
    · have hkept : d ∈ data.keptSet₂ := ⟨Or.inl hs₂, by simp only [Set.mem_singleton_iff]; exact hd⟩
      rw [← htail]; exact ⟨d, (data.mem_keptDel₂_iff d).2 hkept, rfl⟩



/-- A non-outer dart whose two endpoints we wish to confine: `boundedFacePartition` places its face
in `side₁` or `side₂`, and the matching `endpoints_mem_sideRegionₛ_of_face` lemma confines BOTH
endpoints to that side region.  (Non-chord hypothesis needed for the kept-set membership.) -/
theorem nonouter_dart_confined (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hnonouter : M.dartFace e ≠ hNT.outerFace) :
    (M.tail e ∈ sideRegion₁ data ∧ M.head e ∈ sideRegion₁ data) ∨
      (M.tail e ∈ sideRegion₂ data ∧ M.head e ∈ sideRegion₂ data) := by
  rcases boundedFacePartition_uncond data hnonouter with hs₁ | hs₂
  · exact Or.inl (endpoints_mem_sideRegion₁_of_face data hsep hchord hs₁)
  · exact Or.inr (endpoints_mem_sideRegion₂_of_face data hsep hchord hs₂)

/-- **Edge confinement at the level of a single dart's two endpoints.**  Both `tail e` and `head e`
are confined to one common side region: if `e` is the chord they are `u, v ∈ sideRegion₁`; otherwise
the non-outer representative (`e` or `M.α e`) confines both via `nonouter_dart_confined`. -/
theorem dart_endpoints_confined (data : hNT.ChordSplitData u v) (hsep : data.Separates) (e : D) :
    (M.tail e ∈ sideRegion₁ data ∧ M.head e ∈ sideRegion₁ data) ∨
      (M.tail e ∈ sideRegion₂ data ∧ M.head e ∈ sideRegion₂ data) := by
  by_cases hchord : M.dartEdge e = s(u, v)
  · -- chord edge: `{tail e, head e} = {u, v}`, both in `sideRegion₁`.
    left
    have hu₁ : M.tail data.dart ∈ sideRegion₁ data := tailDart_mem_sideRegion₁ data hsep
    have hv₁ : M.head data.dart ∈ sideRegion₁ data := headDart_mem_sideRegion₁ data hsep
    have hdartedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
    have he2 : (s(M.tail e, M.head e) : Sym2 M.Vertex)
        = s(M.tail data.dart, M.head data.dart) := by
      have h1 : (s(M.tail e, M.head e) : Sym2 M.Vertex) = s(u, v) := hchord
      have h2 : (s(M.tail data.dart, M.head data.dart) : Sym2 M.Vertex) = s(u, v) := hdartedge
      rw [h1, h2]
    rcases Sym2.eq_iff.mp he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ hu₁, h2 ▸ hv₁⟩
    · exact ⟨h1 ▸ hv₁, h2 ▸ hu₁⟩
  · -- non-chord: pick the non-outer representative dart of the edge.
    by_cases ho : M.dartFace e = hNT.outerFace
    · have hαnonouter : M.dartFace (M.α e) ≠ hNT.outerFace :=
        alpha_dartFace_ne_outer_of_outer hNT ho
      have hαchord : M.dartEdge (M.α e) ≠ s(u, v) := by rwa [M.dartEdge_alpha]
      rcases nonouter_dart_confined data hsep hαchord hαnonouter with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · rw [M.tail_alpha] at ht; rw [M.head_alpha] at hh; exact Or.inl ⟨hh, ht⟩
      · rw [M.tail_alpha] at ht; rw [M.head_alpha] at hh; exact Or.inr ⟨hh, ht⟩
    · exact nonouter_dart_confined data hsep hchord ho

/-- **The vertex-level edge confinement** (the `edge_confined` field).  A graph edge between two
vertices keeps both inside one side region. -/
theorem edge_confined_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ ⦃a b : M.Vertex⦄, M.toSimpleGraph.Adj a b →
      (a ∈ sideRegion₁ data ∧ b ∈ sideRegion₁ data) ∨
        (a ∈ sideRegion₂ data ∧ b ∈ sideRegion₂ data) := by
  intro a b hab
  obtain ⟨hne, e, hedge⟩ := hab
  -- `dartEdge e = s(a,b)`; so `(tail e = a ∧ head e = b) ∨ (tail e = b ∧ head e = a)`.
  have hedge' : (s(M.tail e, M.head e) : Sym2 M.Vertex) = s(a, b) := hedge
  rcases dart_endpoints_confined data hsep e with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · -- both endpoints of `e` in `sideRegion₁`; transfer to `a, b` by the Sym2 equality.
    left
    rcases Sym2.eq_iff.mp hedge' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ ht, h2 ▸ hh⟩
    · exact ⟨h2 ▸ hh, h1 ▸ ht⟩
  · right
    rcases Sym2.eq_iff.mp hedge' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ ht, h2 ▸ hh⟩
    · exact ⟨h2 ▸ hh, h1 ▸ ht⟩



/-- **The chord-split-regions residue, from the precolored placement alone.**  The four structural
fields are produced unconditionally; the only inputs are the recursion-supplied precolored
memberships `p, q ∈ sideRegion₁`. -/
theorem chordSplitRegionsResidue_of_precolored
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) {p q : M.Vertex}
    (hp : p ∈ sideRegion₁ data) (hq : q ∈ sideRegion₁ data) :
    ChordSplitRegionsResidue data p q where
  cover := cover_holds data hsep
  edge_confined := edge_confined_holds data hsep
  u_s₂ := tailDart_mem_sideRegion₂ data hsep
  v_s₂ := headDart_mem_sideRegion₂ data hsep
  p_s₁ := hp
  q_s₁ := hq



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

/-- **No `1`-step between the two endpoint positions** (the non-boundary-edge
analogue of `not_consecutive_of_chord`).  If `s(u, v)` is not a boundary edge then
the positions `p` (tail `u`) and `q` (tail `v`) cannot be cyclic-consecutive. -/
lemma not_consecutive_of_nonBoundaryEdge (C : BoundaryCycle M f) {u v : M.Vertex}
    (hnbe : ¬ C.IsBoundaryEdge s(u, v)) {p q : ℕ}
    (hp : p < C.darts.length) (hq : q < C.darts.length)
    (htu : M.tail (C.darts[p]'hp) = u)
    (htv : M.tail (C.darts[q]'hq) = v)
    (hadj : (p + 1) % C.darts.length = q) : False := by
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  have hcv := C.consecutive_vertex ⟨p, hp⟩
  have hcyc : (cyclicNext C.normalized.length_pos ⟨p, hp⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext; show (p + 1) % L = q; exact hadj
  rw [hcyc] at hcv
  have hhead : M.head (C.darts[p]'hp) = v := by
    rw [show (C.darts.get ⟨q, hq⟩) = C.darts[q]'hq from rfl,
        show (C.darts.get ⟨p, hp⟩) = C.darts[p]'hp from rfl] at hcv
    rw [← hcv, htv]
  apply hnbe
  show s(u, v) ∈ C.edges
  rw [C.edges_eq, show (s(u, v) : Sym2 M.Vertex) = M.dartEdge (C.darts[p]'hp) from by
    show s(u, v) = s(M.tail _, M.head _); rw [htu, hhead]]
  exact List.mem_map_of_mem (List.getElem_mem hp)

/-- The two complementary boundary runs for a non-boundary-edge pair `u, v`, with
their tail-covering and tail-disjointness of `C.vertices` — the chord-free
analogue of `NormalizedRuns`. -/
structure NonEdgeRuns (C : BoundaryCycle M f) (hC : C.VertexNodup) {u v : M.Vertex}
    (hne : u ≠ v) (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v)
    (hnbe : ¬ C.IsBoundaryEdge s(u, v)) where
  /-- The `u → v` boundary run. -/
  arcUV : DartArc M C u v
  /-- The `v → u` boundary run. -/
  arcVU : DartArc M C v u
  /-- Both runs have length `≥ 2`. -/
  lenUV : 2 ≤ arcUV.len
  lenVU : 2 ≤ arcVU.len
  /-- Every boundary vertex is a tail of one of the two runs, or an endpoint. -/
  covering : ∀ {w : M.Vertex}, C.IsBoundaryVertex w →
    (∃ i, M.tail (arcUV.arcDart i) = w) ∨ (∃ i, M.tail (arcVU.arcDart i) = w) ∨ w = u ∨ w = v
  /-- A vertex that is a tail of *both* runs is an endpoint. -/
  disjoint : ∀ {w : M.Vertex}, (∃ i, M.tail (arcUV.arcDart i) = w) →
    (∃ i, M.tail (arcVU.arcDart i) = w) → w = u ∨ w = v

/-- **Build the complementary runs from the non-boundary-edge data.**  Mirrors
`ZinanCh35Aligned.normalizedRuns`, with `not_consecutive_of_chord` replaced by
`not_consecutive_of_nonBoundaryEdge` and `Chord` fields replaced by the four bare
facts. -/
noncomputable def nonEdgeRuns (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {u v : M.Vertex} (hne : u ≠ v) (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v)
    (hnbe : ¬ C.IsBoundaryEdge s(u, v)) : NonEdgeRuns C hC hne hu hv hnbe := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  -- positions of u, v
  set puF := (C.exists_pos_of_isBoundaryVertex hu).choose with hpuF
  have eu0 := (C.exists_pos_of_isBoundaryVertex hu).choose_spec
  set pvF := (C.exists_pos_of_isBoundaryVertex hv).choose with hpvF
  have ev0 := (C.exists_pos_of_isBoundaryVertex hv).choose_spec
  set pu := puF.1 with hpuval
  set pv := pvF.1 with hpvval
  have hpu : pu < L := puF.2
  have hpv : pv < L := pvF.2
  have eu : M.tail (C.darts[pu]'hpu) = u := eu0
  have ev : M.tail (C.darts[pv]'hpv) = v := ev0
  have hpune : pu ≠ pv := by
    intro hpe; apply hne
    rw [← eu, ← ev]
    have : C.darts[pu]'hpu = C.darts[pv]'hpv := getElem_congr rfl hpe hpu
    rw [this]
  -- run lengths
  set kf := (pv + L - pu) % L with hkf
  set kb := (pu + L - pv) % L with hkb
  obtain ⟨hkf1, hkb1, hsum, hpfkf, hcov⟩ :=
    ZinanCh35Aligned.mod_cover L pu pv hLpos hpu hpv hpune kf kb hkf hkb
  obtain ⟨_, _, _, hpvkb, _⟩ :=
    ZinanCh35Aligned.mod_cover L pv pu hLpos hpv hpu (Ne.symm hpune) kb kf hkb hkf
  have hkfL : kf < L := by rw [hkf]; exact Nat.mod_lt _ hLpos
  have hkbL : kb < L := by rw [hkb]; exact Nat.mod_lt _ hLpos
  -- kf ≥ 2
  have hkf2 : 2 ≤ kf := by
    rcases Nat.lt_or_ge kf 2 with hlt | hge
    · exfalso
      have hkf1' : kf = 1 := by omega
      apply not_consecutive_of_nonBoundaryEdge C hnbe hpu hpv eu ev
      rw [show (pu + 1) % L = (pu + kf) % L from by rw [hkf1'], hpfkf]
    · exact hge
  have hkb2 : 2 ≤ kb := by
    rcases Nat.lt_or_ge kb 2 with hlt | hge
    · exfalso
      have hkb1' : kb = 1 := by omega
      have hnbe' : ¬ C.IsBoundaryEdge s(v, u) := by rw [Sym2.eq_swap]; exact hnbe
      exact not_consecutive_of_nonBoundaryEdge C hnbe' hpv hpu ev eu
        (by rw [show (pv + 1) % L = (pv + kb) % L from by rw [hkb1'], hpvkb])
    · exact hge
  -- the two raw runs
  set AUV := C.cyclicDartArc hC pu kf hkf1 hkfL hpu with hAUV
  set AVU := C.cyclicDartArc hC pv kb hkb1 hkbL hpv with hAVU
  -- endpoint equalities for casting
  have euv2 : M.tail (C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega))) = v := by
    have : C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pv]'hpv := by congr 1
    rw [this]; exact ev
  have evu2 : M.tail (C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega))) = u := by
    have : C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pu]'hpu := by congr 1
    rw [this]; exact eu
  -- tail characterizations of the casted runs
  have htailUV : ∀ i : Fin (daCast AUV eu euv2).len,
      M.tail ((daCast AUV eu euv2).arcDart i)
        = M.tail (C.darts[(pu + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hC pu kf hkf1 hkfL hpu eu euv2 i
  have htailVU : ∀ i : Fin (daCast AVU ev evu2).len,
      M.tail ((daCast AVU ev evu2).arcDart i)
        = M.tail (C.darts[(pv + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hC pv kb hkb1 hkbL hpv ev evu2 i
  have htailUV_fwd : ∀ j : ℕ, (hj : j < kf) →
      ∃ i : Fin (daCast AUV eu euv2).len,
        M.tail ((daCast AUV eu euv2).arcDart i)
          = M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCast AUV eu euv2).len := by rw [daCast_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailUV ⟨j, hjlen⟩⟩
  have htailVU_fwd : ∀ j : ℕ, (hj : j < kb) →
      ∃ i : Fin (daCast AVU ev evu2).len,
        M.tail ((daCast AVU ev evu2).arcDart i)
          = M.tail (C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCast AVU ev evu2).len := by rw [daCast_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailVU ⟨j, hjlen⟩⟩
  have htailUV_bwd : ∀ i : Fin (daCast AUV eu euv2).len,
      ∃ j : ℕ, j < kf ∧
        M.tail ((daCast AUV eu euv2).arcDart i)
          = M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kf := lt_of_lt_of_eq i.2 (daCast_len AUV eu euv2)
    exact ⟨i.1, hi, htailUV i⟩
  have htailVU_bwd : ∀ i : Fin (daCast AVU ev evu2).len,
      ∃ j : ℕ, j < kb ∧
        M.tail ((daCast AVU ev evu2).arcDart i)
          = M.tail (C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kb := lt_of_lt_of_eq i.2 (daCast_len AVU ev evu2)
    exact ⟨i.1, hi, htailVU i⟩
  refine
    { arcUV := daCast AUV eu euv2
      arcVU := daCast AVU ev evu2
      lenUV := ?_
      lenVU := ?_
      covering := ?_
      disjoint := ?_ }
  · rw [daCast_len]; exact hkf2
  · rw [daCast_len]; exact hkb2
  · -- covering
    intro w hw
    obtain ⟨q, hqt⟩ := C.exists_pos_of_isBoundaryVertex hw
    rcases hcov q.1 q.2 with ⟨j, hj, hjq⟩ | ⟨j, hj, hjq⟩
    · left
      obtain ⟨i, hi⟩ := htailUV_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
    · right; left
      obtain ⟨i, hi⟩ := htailVU_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
  · -- disjoint
    rintro w ⟨i, hiw⟩ ⟨i', hi'w⟩
    obtain ⟨j, hj, hjeq⟩ := htailUV_bwd i
    obtain ⟨j', hj', hj'eq⟩ := htailVU_bwd i'
    have heq : M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)))
        = M.tail (C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega))) := by
      rw [← hjeq, ← hj'eq, hiw, hi'w]
    have hmap : (C.darts.map M.tail).Nodup := by
      have := hC
      rwa [BoundaryCycle.VertexNodup, C.vertices_eq] at this
    have hposeq : (pu + j) % L = (pv + j') % L := by
      have hmem1 : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) ∈ C.darts :=
        List.getElem_mem _
      have hmem2 : C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) ∈ C.darts :=
        List.getElem_mem _
      have hdarts : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))
          = C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) :=
        List.inj_on_of_nodup_map hmap hmem1 hmem2 heq
      exact (C.normalized.nodup.getElem_inj_iff).mp hdarts
    by_cases hj0 : j = 0
    · left
      rw [← hiw, hjeq, hj0]
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hpu]
      exact eu
    · by_cases hj'0 : j' = 0
      · right
        rw [← hi'w, hj'eq, hj'0]
        simp only [Nat.add_zero, Nat.mod_eq_of_lt hpv]
        exact ev
      · exfalso
        have hpvmod : pv % L = (pu + kf) % L := by rw [hpfkf, Nat.mod_eq_of_lt hpv]
        have h2 : Nat.ModEq L pv (pu + kf) := by
          show pv % L = (pu + kf) % L; exact hpvmod
        have hcong : Nat.ModEq L (pu + j) (pu + (kf + j')) := by
          have h1 : Nat.ModEq L (pu + j) (pv + j') := hposeq
          have h3 : Nat.ModEq L (pv + j') (pu + kf + j') := h2.add_right j'
          have h4 : Nat.ModEq L (pu + j) (pu + kf + j') := h1.trans h3
          rwa [show pu + kf + j' = pu + (kf + j') from by ring] at h4
        have hcong' : Nat.ModEq L j (kf + j') := Nat.ModEq.add_left_cancel' pu hcong
        have hjlt : j < L := by omega
        have hkfj' : kf + j' < L := by omega
        have : j = kf + j' := by
          have hj1 : j % L = j := Nat.mod_eq_of_lt hjlt
          have hj2 : (kf + j') % L = kf + j' := Nat.mod_eq_of_lt hkfj'
          rw [Nat.ModEq, hj1, hj2] at hcong'; exact hcong'
        omega



end BoundaryCycle





/-- **Piece 2 — the explicit-boundary near-triangulation assembler.**
`outerCycle` is `boundaryCycleOfFace` rooted at `root`; the arc-split certificate
is the genuine Jordan data `arcSplit` (R10 §4: not derivable from `Nodup` for
consecutive pairs — see `boundaryArcSplit_consecutive_unsatisfiable`).  Every other
field is the listed explicit hypothesis. -/
noncomputable def nearTriangulation_of_explicit_boundary_classification
    {DK : Type u} [Fintype DK] [DecidableEq DK] (K : CombMap DK)
    (hsphere : K.IsSphereMap) (hsimple : K.IsSimpleGraph)
    (outerFace : K.Face) (root : DK) (houterOrbit : K.dartFace root = outerFace)
    (houter_simple : ((K.faceDartList root).map K.tail).Nodup)
    (houter_len : 3 ≤ (K.faceDartList root).length)
    (hinner_tri : ∀ f : K.Face, f ≠ outerFace → K.faceLen f = 3) :
    NearTriangulation K where
  sphere := hsphere
  simpleGraph := hsimple
  outerFace := outerFace
  outerCycle :=
    K.boundaryCycleOfFace outerFace
      (K.phi_ne_self_of_isSimpleGraph hsimple root) houterOrbit houter_simple
  outer_simple := houter_simple
  outer_len := houter_len
  inner_tri := hinner_tri














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



/-- `inr 1` is in the support of the side map's `φ` (it is a simple graph, so `φ` is fixed-point
free; or directly `φ (inr 1) = inl (ρ a₀) ≠ inr 1`). -/
lemma inr_one_mem_phi_support :
    (Sum.inr 1 : K ⊕ Fin 2) ∈ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.support := by
  rw [Equiv.Perm.mem_support, freshMap_phi_inr_one β ρ hβinv hβfix hne]
  exact Sum.inl_ne_inr

/-- **`inl (ρ a₀)` is in the `inr 1` face orbit.**  `φ (inr 1) = inl (ρ a₀)`. -/
lemma inl_rho_a0_mem_toList :
    (Sum.inl (ρ a₀) : K ⊕ Fin 2)
      ∈ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 1) := by
  rw [Equiv.Perm.mem_toList_iff]
  refine ⟨⟨1, ?_⟩, inr_one_mem_phi_support β ρ hβinv hβfix hne⟩
  rw [zpow_one, freshMap_phi_inr_one β ρ hβinv hβfix hne]

/-- **`inl (β a₁)` is in the `inr 1` face orbit.**  `φ (inl (β a₁)) = inr 1`, so a single
backward `φ`-step joins them. -/
lemma inl_beta_a1_mem_toList :
    (Sum.inl (β a₁) : K ⊕ Fin 2)
      ∈ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 1) := by
  rw [Equiv.Perm.mem_toList_iff]
  refine ⟨⟨-1, ?_⟩, inr_one_mem_phi_support β ρ hβinv hβfix hne⟩
  rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq,
    freshMap_phi_inl_b1 β ρ hβinv hβfix hne]

/-- `inr 1` is in its own face orbit (the root). -/
lemma inr_one_mem_toList :
    (Sum.inr 1 : K ⊕ Fin 2)
      ∈ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 1) := by
  rw [Equiv.Perm.mem_toList_iff]
  exact ⟨(Equiv.Perm.SameCycle.refl _ _), inr_one_mem_phi_support β ρ hβinv hβfix hne⟩

/-- **The three pinned orbit darts are pairwise distinct** (given `ρ a₀ ≠ β a₁`).  `inr 1` differs
from each `inl _` by the `Sum` tag; the two `inl`-darts differ exactly when `ρ a₀ ≠ β a₁`. -/
lemma three_orbit_darts_distinct (hd : ρ a₀ ≠ β a₁) :
    [(Sum.inr 1 : K ⊕ Fin 2), Sum.inl (ρ a₀), Sum.inl (β a₁)].Nodup := by
  have h01 : (Sum.inr 1 : K ⊕ Fin 2) ≠ Sum.inl (ρ a₀) := Sum.inr_ne_inl
  have h02 : (Sum.inr 1 : K ⊕ Fin 2) ≠ Sum.inl (β a₁) := Sum.inr_ne_inl
  have h12 : (Sum.inl (ρ a₀) : K ⊕ Fin 2) ≠ Sum.inl (β a₁) := by
    intro h; exact hd (Sum.inl.inj h)
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ?_⟩⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    exact ⟨h01, h02⟩
  · simp only [List.mem_singleton]; exact h12
  · simp

/-- **Layer B — the side outer `φ`-orbit has at least three darts** (given `ρ a₀ ≠ β a₁`).
The three pinned members `inr 1`, `inl (ρ a₀)`, `inl (β a₁)` are a `Nodup` sublist of the
`Nodup` orbit list `φ.toList (inr 1)`, so the orbit length is `≥ 3`.  This is the explicit
itinerary count — no genus slack, no Jordan data. -/
lemma freshMap_phi_orbit_three_darts (hd : ρ a₀ ≠ β a₁) :
    3 ≤ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 1)).length := by
  classical
  have hsub : [(Sum.inr 1 : K ⊕ Fin 2), Sum.inl (ρ a₀), Sum.inl (β a₁)]
      ⊆ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 1) := by
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h
    · rw [h]; exact inr_one_mem_toList β ρ hβinv hβfix hne
    · rw [h]; exact inl_rho_a0_mem_toList β ρ hβinv hβfix hne
    · rw [h]; exact inl_beta_a1_mem_toList β ρ hβinv hβfix hne
  have hcard : ([(Sum.inr 1 : K ⊕ Fin 2), Sum.inl (ρ a₀), Sum.inl (β a₁)]).length
      ≤ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 1)).length :=
    (List.subperm_of_subset (three_orbit_darts_distinct β ρ (a₀ := a₀) (a₁ := a₁) hd)
      hsub).length_le
  simpa using hcard

/-- **`outer_len` for the bare fresh map** (given the chord-incidence non-degeneracy).
`faceDartList (inr 1) = φ.toList (inr 1)`, so `freshMap_phi_orbit_three_darts` gives length `≥ 3`. -/
lemma freshMap_outerLen_ge_three (hd : ρ a₀ ≠ β a₁) :
    3 ≤ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).faceDartList (Sum.inr 1)).length := by
  rw [ProofsInTheBook.PlanarMap.CombMap.faceDartList]
  exact freshMap_phi_orbit_three_darts β ρ hβinv hβfix hne hd

end Itinerary



variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The side-1 chord-incidence non-degeneracy.**  The two chord-incident darts at the two
anchors differ: `sideSigma₁ a₀ ≠ sideAlpha₁ a₁`.  (The σ-successor of `a₀` and the α-partner of
`a₁` are distinct darts.)  This is the lone combinatorial residue of the Layer-B `outer_len`
itinerary; it is a `CombMap`-layer dart inequality, not a planar-embedding datum. -/
def Side₁ChordIncidenceNonDegenerate (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) : Prop :=
  data.sideSigma₁ a₀ ≠ data.sideAlpha₁ hsep a₁

/-- **The side-2 chord-incidence non-degeneracy** (the side-2 mirror). -/
def Side₂ChordIncidenceNonDegenerate (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) : Prop :=
  data.sideSigma₂ a₀ ≠ data.sideAlpha₂ hsep a₁

/-- **`outer_len` for `sideMap₁`** from the side-1 non-degeneracy (Layer B specialized). -/
theorem side₁_outerLen_ge_three (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hd : Side₁ChordIncidenceNonDegenerate data hsep a₀ a₁) :
    3 ≤ ((data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1)).length :=
  freshMap_outerLen_ge_three (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne hd













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

/-- **`tail`-equality is `σ`-SameCycle.**  Two darts have the same tail vertex iff they are in
the same `σ`-orbit. -/
lemma tail_eq_iff_sigma_sameCycle (M : CombMap D) (d e : D) :
    M.tail d = M.tail e ↔ M.σ.SameCycle d e := by
  unfold CombMap.tail
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

end Bridge



section FreshTail

variable {K : Type u} [Fintype K] [DecidableEq K]
  (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **Fresh-side `tail`-equality collapses to `ρ`-SameCycle of the anchor projections.**
`(freshMap β ρ … a₀ a₁).tail x = (…).tail y ↔ ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y)`. -/
lemma freshMap_tail_eq_iff_rho_sameCycle (x y : K ⊕ Fin 2) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).tail x = (freshMap β ρ hβinv hβfix a₀ a₁ hne).tail y
      ↔ ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y) := by
  rw [tail_eq_iff_sigma_sameCycle]
  rw [freshMap_sigma β ρ hβinv hβfix a₀ a₁ hne]
  exact freshSigma_sameCycle_iff ρ hne x y

end FreshTail



section SideTail

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The side-1 `tail`-collapse.**  For the side-1 map `S = sideMap₁`, two outer darts have the
same `S`-tail vertex iff their original underlying darts `(proj a₀ a₁ x).1`, `(proj a₀ a₁ y).1`
have the same `M`-tail vertex.

PROVED unconditionally: `freshMap_tail_eq_iff_rho_sameCycle` reduces it to
`sideSigma₁.SameCycle (proj…x) (proj…y)`; `sideSigma₁ = filteredRotation M.σ keptDel₁`, so
`filteredRotation_sameCycle_iff` reduces it to `M.σ.SameCycle (proj…x).1 (proj…y).1`, which is
`M.tail`-equality. -/
lemma sideMap₁_tail_eq_iff_M_tail_proj
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (x y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    (data.sideMap₁ hsep a₀ a₁ hne).tail x = (data.sideMap₁ hsep a₀ a₁ hne).tail y
      ↔ M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 := by
  -- Step A: fresh-side tail ↔ sideSigma₁-SameCycle of the projections.
  rw [show data.sideMap₁ hsep a₀ a₁ hne
        = freshMap (data.sideAlpha₁ hsep) data.sideSigma₁
            (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) a₀ a₁ hne from rfl]
  rw [freshMap_tail_eq_iff_rho_sameCycle (data.sideAlpha₁ hsep) data.sideSigma₁
        (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne x y]
  -- Step B: sideSigma₁-SameCycle ↔ M.σ-SameCycle of the underlying original darts.
  rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl]
  rw [filteredRotation_sameCycle_iff M.σ data.keptDel₁ (proj a₀ a₁ x) (proj a₀ a₁ y)]
  -- Step C: M.σ-SameCycle ↔ M.tail-equality of the underlying original darts.
  rw [tail_eq_iff_sigma_sameCycle]

end SideTail



section Main

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  (hNT : NearTriangulation M) {u v : M.Vertex}







/-- **The single irreducible residual** (R3c-ii core, post-§2): the composite
`x ↦ M.tail (proj a₀ a₁ x).1` is injective on the side-1 outer orbit. -/
def OuterTraceInjOn
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) : Prop :=
  ∀ x ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1),
    ∀ y ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1),
      M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 → x = y



/-- **The side-1 `outer_simple` for arbitrary anchors, given the single residual
`OuterTraceInjOn`.**  PROVED: the §2 tail-collapse turns the orbit `InjOn` of `S.tail` into the
residual, then the residual closes it. -/
theorem side₁_outer_simple_of_orbitTrace
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hresidual : OuterTraceInjOn hNT data hsep a₀ a₁ hne) :
    (((data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1)).map
        (data.sideMap₁ hsep a₀ a₁ hne).tail).Nodup := by
  -- The orbit list is `Nodup` (it is `φ.toList`, a permutation orbit list).
  have hL : ((data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1)).Nodup := by
    rw [ProofsInTheBook.PlanarMap.CombMap.faceDartList]
    exact Equiv.Perm.nodup_toList _ _
  -- `Nodup (map tail l) ↔ InjOn tail l`.
  rw [List.nodup_map_iff_inj_on hL]
  intro x hx y hy htail
  -- §2 collapse: `S.tail x = S.tail y → M.tail (proj…x).1 = M.tail (proj…y).1`.
  have hMtail : M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 :=
    (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne x y).1 htail
  -- the single residual closes `x = y`.
  exact hresidual x hx y hy hMtail



/-- **The canonical-anchor `outer_simple`** matching the `outer_simple` input of
`ZinanCh35Contiguous.contiguousInterval_holds`.  PROVED modulo the single isolated residual
`hresidual := OuterTraceInjOn …` at the canonical anchors.  Plug the conclusion straight into
`contiguousInterval_holds (… outer_simple := side₁_outer_simple_canonical … )`. -/
theorem side₁_outer_simple_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hresidual : OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)) :
    (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).tail).Nodup :=
  side₁_outer_simple_of_orbitTrace hNT data hsep
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
    hresidual

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


theorem face₂_isFaceTriangle (data : hNT.ChordSplitData u v) :
    M.IsFaceTriangle (M.α data.dart) (M.φ (M.α data.dart)) (M.φ (M.φ (M.α data.dart))) :=
  hNT.inner_face_isFaceTriangle (hNT.chordDart_alpha_not_outer data.chord)


theorem face₂_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd1 : M.φ (M.α data.dart) ≠ M.α data.dart) :
    M.φ (M.α data.dart) ∉ data.keptDel₂ := by
  classical
  rw [data.mem_keptDel₂_iff]
  refine ⟨Or.inl ?_, by simpa using hd1⟩
  show M.dartFace (M.φ (M.α data.dart)) ∈ data.side₂
  rw [M.dartFace_phi]; exact data.face₂_mem_side₂

theorem face₂_phi_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd2 : M.φ (M.φ (M.α data.dart)) ≠ M.α data.dart) :
    M.φ (M.φ (M.α data.dart)) ∉ data.keptDel₂ := by
  classical
  rw [data.mem_keptDel₂_iff]
  refine ⟨Or.inl ?_, by simpa using hd2⟩
  show M.dartFace (M.φ (M.φ (M.α data.dart))) ∈ data.side₂
  rw [M.dartFace_phi, M.dartFace_phi]; exact data.face₂_mem_side₂

theorem face₂_kept_darts_distinct (data : hNT.ChordSplitData u v) :
    M.φ (M.α data.dart) ≠ M.φ (M.φ (M.α data.dart)) := by
  intro h
  have heq : M.α data.dart = M.φ (M.α data.dart) := M.φ.injective h
  exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph (M.α data.dart)) heq.symm

theorem face₂_two_kept_darts (data : hNT.ChordSplitData u v) :
    (M.φ (M.α data.dart) ∉ data.keptDel₂) ∧
      (M.φ (M.φ (M.α data.dart)) ∉ data.keptDel₂) ∧
      M.φ (M.α data.dart) ≠ M.φ (M.φ (M.α data.dart)) ∧
      M.dartFace (M.φ (M.α data.dart)) = data.face₂ ∧
      M.dartFace (M.φ (M.φ (M.α data.dart))) = data.face₂ := by
  obtain ⟨_, h12, h20⟩ := face₂_isFaceTriangle data
  have hd1 : M.φ (M.α data.dart) ≠ M.α data.dart := by
    intro he
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph (M.α data.dart)) he
  have hd2 : M.φ (M.φ (M.α data.dart)) ≠ M.α data.dart := by
    intro he
    have hstep : M.φ (M.φ (M.φ (M.α data.dart))) = M.φ (M.α data.dart) := congrArg M.φ he
    have : M.α data.dart = M.φ (M.α data.dart) := h20.symm.trans hstep
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph (M.α data.dart)) this.symm
  refine ⟨face₂_phi_dart_kept data hd1, face₂_phi_phi_dart_kept data hd2,
    face₂_kept_darts_distinct data, ?_, ?_⟩
  · show M.dartFace (M.φ (M.α data.dart)) = M.dartFace (M.α data.dart); rw [M.dartFace_phi]
  · show M.dartFace (M.φ (M.φ (M.α data.dart))) = M.dartFace (M.α data.dart)
    rw [M.dartFace_phi, M.dartFace_phi]


noncomputable def face₂Dart₁ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₂} :=
  ⟨M.φ (M.α data.dart), (face₂_two_kept_darts data).1⟩

noncomputable def face₂Dart₂ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₂} :=
  ⟨M.φ (M.φ (M.α data.dart)), (face₂_two_kept_darts data).2.1⟩

noncomputable def side₂Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₂} :=
  (data.sideSigma₂).symm
    (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₂ data))

noncomputable def side₂Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₂} :=
  (data.sideSigma₂).symm (face₂Dart₁ data)

@[simp] theorem sideSigma₂_side₂Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₂ (side₂Anchor₀ data hsep)
      = keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₂ data) := by
  rw [side₂Anchor₀, Equiv.apply_symm_apply]

@[simp] theorem sideSigma₂_side₂Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₂ (side₂Anchor₁ data hsep) = face₂Dart₁ data := by
  rw [side₂Anchor₁, Equiv.apply_symm_apply]


theorem keptPhi_face₂Dart₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₁ data) = face₂Dart₂ data := by
  classical
  apply Subtype.ext
  show ((data.sideSigma₂ (data.sideAlpha₂ hsep (face₂Dart₁ data))) : D)
    = (face₂Dart₂ data : D)
  have hval : ((data.sideAlpha₂ hsep (face₂Dart₁ data)) : D) = M.α (M.φ (M.α data.dart)) := by
    rw [sideAlpha₂_apply_coe]; rfl
  have hstep : M.σ ((data.sideAlpha₂ hsep (face₂Dart₁ data)) : D)
      = M.φ (M.φ (M.α data.dart)) := by
    rw [hval]
    show M.σ (M.α (M.φ (M.α data.dart))) = (M.σ * M.α) (M.φ (M.α data.dart))
    rw [Equiv.Perm.mul_apply]
  have hkept : M.σ ((data.sideAlpha₂ hsep (face₂Dart₁ data)) : D) ∉ data.keptDel₂ := by
    rw [hstep]; exact (face₂_two_kept_darts data).2.1
  show ((FilteredRotation.filteredRotation M.σ data.keptDel₂
        (data.sideAlpha₂ hsep (face₂Dart₁ data))) : D) = (face₂Dart₂ data : D)
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₂
    (data.sideAlpha₂ hsep (face₂Dart₁ data)) hkept, hstep]
  rfl


theorem keptPhi_sameCycle_d₁_keptPhi_d₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂).SameCycle
      (face₂Dart₁ data)
      (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₂ data)) := by
  rw [Equiv.Perm.sameCycle_apply_right]
  rw [← keptPhi_face₂Dart₁ data hsep]
  exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))


theorem side₂AnchorsShareFace_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep
      (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep) := by
  show (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂).SameCycle
    (data.sideSigma₂ (side₂Anchor₀ data hsep)) (data.sideSigma₂ (side₂Anchor₁ data hsep))
  rw [sideSigma₂_side₂Anchor₀, sideSigma₂_side₂Anchor₁]
  exact (keptPhi_sameCycle_d₁_keptPhi_d₂ data hsep).symm

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



/-- `keptDel₂` is `M.α`-closed (membership is `α`-invariant).  Mirror of
`SubmapPlanar.keptDel₁_sub`. -/
lemma keptDel₂_sub (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, d ∈ data.keptDel₂ ↔ M.α d ∈ data.keptDel₂ := by
  intro d
  have h1 : d ∉ data.keptDel₂ ↔ d ∈ data.keptSet₂ := data.mem_keptDel₂_iff d
  have h2 : M.α d ∉ data.keptDel₂ ↔ M.α d ∈ data.keptSet₂ := data.mem_keptDel₂_iff (M.α d)
  have hkept : M.α d ∈ data.keptSet₂ ↔ d ∈ data.keptSet₂ :=
    data.mem_keptSet₂_alpha_iff hsep d
  classical
  have h1' : d ∈ data.keptDel₂ ↔ ¬ d ∈ data.keptSet₂ := by
    rw [← h1]; exact (not_not).symm
  have h2' : M.α d ∈ data.keptDel₂ ↔ ¬ M.α d ∈ data.keptSet₂ := by
    rw [← h2]; exact (not_not).symm
  rw [h1', h2']
  exact (not_congr hkept).symm

/-- `keptDel₂` is `M.α`-closed.  Mirror of `SubmapPlanar.keptDel₁_closed`. -/
lemma keptDel₂_closed (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, d ∈ data.keptDel₂ → M.α d ∈ data.keptDel₂ :=
  fun d hd => (keptDel₂_sub data hsep d).1 hd

/-- `sideAlpha₂` equals the abstract `keptAlpha` of `keptDel₂`.  Mirror of
`SubmapPlanar.sideAlpha₁_eq_keptAlpha`. -/
lemma sideAlpha₂_eq_keptAlpha (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₂ hsep
      = SubmapPlanar.keptAlpha M data.keptDel₂ (keptDel₂_sub data hsep) := by
  ext d
  rw [data.sideAlpha₂_apply_coe]
  rfl

/-- **The `≥ 2` no-handle half of the side-2 disk fact, discharged structurally.**  If the kept
side-2 map is connected and has a dart, its Euler characteristic is `2`.  Mirror of
`SubmapPlanar.side₁_keptMap_eulerChar_eq_two`. -/
theorem side₂_keptMap_eulerChar_eq_two (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₂})
    (hconn : (sideKeptMap₂ data hsep).Connected) :
    (sideKeptMap₂ data hsep).eulerChar = 2 := by
  refine SubmapPlanar.keptMap_eulerChar_eq_two M data.keptDel₂ (keptDel₂_sub data hsep)
    (keptDel₂_closed data hsep) hNT.sphere (sideKeptMap₂ data hsep) ?_ ?_ d hconn
  · -- `(sideKeptMap₂).σ = sideSigma₂ = filteredRotation M.σ keptDel₂ = deleteSet M.σ keptDel₂`.
    show data.sideSigma₂ = Equiv.Perm.deleteSet M.σ data.keptDel₂
    rfl
  · -- `(sideKeptMap₂).α = sideAlpha₂ = keptAlpha`.
    show data.sideAlpha₂ hsep = SubmapPlanar.keptAlpha M data.keptDel₂ (keptDel₂_sub data hsep)
    exact sideAlpha₂_eq_keptAlpha data hsep

/-- **`Side₂IsDisk` reduces to connectivity of the kept side.**  Mirror of
`SubmapPlanar.side₁IsDisk_of_connected`: the side-2 kept map is a disk (`IsSphereMap`) given the
structural genus-0 certificate iff its kept map is connected. -/
theorem side₂IsDisk_of_connected (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₂})
    (hconn : (sideKeptMap₂ data hsep).Connected) :
    ChordDisk.Side₂IsDisk data hsep :=
  ⟨hconn, side₂_keptMap_eulerChar_eq_two data hsep d hconn⟩



/-- The **raw** dart-step relation at the side-2 chord split.  Mirror of `rawStep₁`. -/
noncomputable def rawStep₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    D → D → Prop :=
  dartStepRel M.σ (rawAlpha M data.keptDel₂ (keptDel₂_closed data hsep))



section RawConnected

/-- The side-2 seam dart `M.α data.dart` is deleted (removed from the side-2 kept set). -/
lemma alphaDart_mem_keptDel₂ (data : hNT.ChordSplitData u v) :
    M.α data.dart ∈ data.keptDel₂ := by
  classical
  by_contra hcontra
  rw [data.mem_keptDel₂_iff] at hcontra
  exact hcontra.2 rfl

/-- A dart whose face lies in side 2 and which is not the side-2 seam dart `M.α data.dart` is
kept.  Mirror of `inner_notMem_keptDel₁`. -/
lemma inner_notMem_keptDel₂ (data : hNT.ChordSplitData u v)
    {c : D} (hf : M.dartFace c ∈ data.side₂) (hne : c ≠ M.α data.dart) :
    c ∉ data.keptDel₂ := by
  rw [data.mem_keptDel₂_iff]
  exact ⟨Or.inl hf, by simpa using hne⟩

/-- An outer-arc dart of side 2 is kept; it is never the side-2 seam dart `M.α data.dart` (whose
face is `face₂ ≠ outerFace`).  Mirror of `outerArc_notMem_keptDel₁`. -/
lemma outerArc_notMem_keptDel₂ (data : hNT.ChordSplitData u v)
    {c : D} (ho : M.dartFace c = hNT.outerFace)
    (hα : M.dartFace (M.α c) ∈ data.side₂) : c ∉ data.keptDel₂ := by
  rw [data.mem_keptDel₂_iff]
  refine ⟨Or.inr ⟨ho, hα⟩, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hc
  apply data.face₂_not_outer
  show M.dartFace (M.α data.dart) = hNT.outerFace
  rw [← hc]; exact ho

/-- `face₂` is a triangle: it is a non-outer face of the near-triangulation.  Mirror of
`ChordSplitData.face₁_isFaceTriangle` for the second chord-incident face. -/
lemma face₂_isFaceTriangle (data : hNT.ChordSplitData u v) :
    M.IsFaceTriangle (M.α data.dart) (M.φ (M.α data.dart)) (M.φ (M.φ (M.α data.dart))) :=
  hNT.inner_face_isFaceTriangle data.face₂_not_outer

/-- The reference kept dart of side 2: `M.φ (M.α data.dart)`, a dart of the triangle `face₂` other
than the (deleted) seam dart.  Mirror of `ref_kept`. -/
lemma ref_kept₂ (data : hNT.ChordSplitData u v) :
    M.φ (M.α data.dart) ∉ data.keptDel₂ := by
  refine inner_notMem_keptDel₂ data ?_ ?_
  · show M.dartFace (M.φ (M.α data.dart)) ∈ data.side₂
    rw [dartFace_phi]; exact data.face₂_mem_side₂
  · exact M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph (M.α data.dart)

/-- **Within-face raw connectivity, away from `face₂`.**  Mirror of `rawE_within_face_ne_face₁`. -/
lemma rawE_within_face_ne_face₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a b : D} (hfa : M.dartFace a ∈ data.side₂)
    (hne : M.dartFace a ≠ data.face₂) (hab : M.φ.SameCycle a b) :
    Relation.EqvGen (rawStep₂ data hsep) a b := by
  refine rawEqvGen_of_face_kept (keptDel₂_closed data hsep)
    (fun c hac => ?_) hab
  have hfeq : M.dartFace c = M.dartFace a := Quotient.sound hac.symm
  have hfc : M.dartFace c ∈ data.side₂ := by rw [hfeq]; exact hfa
  refine inner_notMem_keptDel₂ data hfc ?_
  intro hcd
  apply hne
  rw [← hfeq, hcd]; rfl

/-- The darts of the chord triangle `face₂`: any dart `c` with
`M.φ.SameCycle (M.α data.dart) c` is `M.α data.dart`, `M.φ (M.α data.dart)`, or
`M.φ² (M.α data.dart)`.  Mirror of `face₁_dart_cases` with seam dart `M.α data.dart`. -/
lemma face₂_dart_cases (data : hNT.ChordSplitData u v)
    {c : D} (hsc : M.φ.SameCycle (M.α data.dart) c) :
    c = M.α data.dart ∨ c = M.φ (M.α data.dart) ∨ c = M.φ (M.φ (M.α data.dart)) := by
  classical
  obtain ⟨h1, h2, h3⟩ := face₂_isFaceTriangle data
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  set s := M.α data.dart with hs
  have hcube : (M.φ ^ 3) s = s := by
    have : (M.φ ^ 3) s = M.φ (M.φ (M.φ s)) := by
      simp [pow_succ, Equiv.Perm.mul_apply]
    rw [this, h3]
  have hperiodic : ∀ m : ℕ, (M.φ ^ m) s = (M.φ ^ (m % 3)) s := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, Equiv.Perm.mul_apply]
    set y := (M.φ ^ (m % 3)) s with hy
    have hfix : (M.φ ^ 3) y = y := by
      rw [hy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm, pow_add, Equiv.Perm.mul_apply,
        hcube]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix (m / 3)
  have hmod : c = (M.φ ^ (k % 3)) s := by rw [← hk, hperiodic k]
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (k % 3)
  · left; rw [hmod]; simp
  · right; left; rw [hmod, pow_one]
  · right; right; rw [hmod]; simp [pow_succ, Equiv.Perm.mul_apply]

/-- **Within-`face₂` raw connectivity.**  Any kept dart of `face₂` raw-connects to the reference
dart `M.φ (M.α data.dart)`.  Mirror of `rawE_face₁_to_ref`. -/
lemma rawE_face₂_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a : D} (hfa : M.dartFace a = data.face₂) (hne : a ≠ M.α data.dart) :
    Relation.EqvGen (rawStep₂ data hsep) a (M.φ (M.α data.dart)) := by
  have hsc : M.φ.SameCycle (M.α data.dart) a := by
    have hf : M.dartFace a = M.dartFace (M.α data.dart) := by rw [hfa]; rfl
    exact (Quotient.exact hf).symm
  rcases face₂_dart_cases data hsc with h | h | h
  · exact absurd h hne
  · subst h; exact Relation.EqvGen.refl _
  · subst h
    exact Relation.EqvGen.symm _ _
      (rawEqvGen_phi_step (keptDel₂_closed data hsep) (ref_kept₂ data))

/-- **Any inner kept dart raw-connects to the reference, given its face does.**  Mirror of
`rawE_inner_to_ref`. -/
lemma rawE_inner_to_ref₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a r₀ : D} (hkept : a ∉ data.keptDel₂) (hfa : M.dartFace a ∈ data.side₂)
    (hsamef : M.dartFace a = M.dartFace r₀)
    (hr₀ : Relation.EqvGen (rawStep₂ data hsep) r₀ (M.φ (M.α data.dart))) :
    Relation.EqvGen (rawStep₂ data hsep) a (M.φ (M.α data.dart)) := by
  classical
  by_cases hne : M.dartFace a = data.face₂
  · have had : a ≠ M.α data.dart := fun h => hkept (h ▸ alphaDart_mem_keptDel₂ data)
    exact rawE_face₂_to_ref data hsep hne had
  · have hsc : M.φ.SameCycle a r₀ := Quotient.exact hsamef
    exact Relation.EqvGen.trans _ _ _ (rawE_within_face_ne_face₂ data hsep hfa hne hsc) hr₀

/-- **The chord-split adjacency step is a raw `α`-edge between kept darts.**  Mirror of
`rawE_chordSplitAdj_step`. -/
lemma rawE_chordSplitAdj_step₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {f g : M.Face} (hf : f ∈ data.side₂) (hg : g ∈ data.side₂)
    (hadj : hNT.ChordSplitAdj u v f g) :
    ∃ d : D, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
      d ∉ data.keptDel₂ ∧ M.α d ∉ data.keptDel₂ ∧
      Relation.EqvGen (rawStep₂ data hsep) d (M.α d) := by
  obtain ⟨d, hdf, hdg, _hbe, hch⟩ := hadj
  -- `d ≠ α dart`: its edge is not the chord (else the `ChordSplitAdj` edge would be the chord).
  have hd_ne : d ≠ M.α data.dart := by
    intro h; apply hch
    rw [h, M.dartEdge_alpha]; exact (hNT.chordDart_edge data.chord)
  have hαd_ne : M.α d ≠ M.α data.dart := by
    intro h
    apply hch
    have : M.dartEdge d = M.dartEdge (M.α d) := (M.dartEdge_alpha d).symm
    rw [this, h, M.dartEdge_alpha]; exact (hNT.chordDart_edge data.chord)
  have hd_kept : d ∉ data.keptDel₂ :=
    inner_notMem_keptDel₂ data (by rw [hdf]; exact hf) hd_ne
  have hαd_kept : M.α d ∉ data.keptDel₂ :=
    inner_notMem_keptDel₂ data (by rw [hdg]; exact hg) hαd_ne
  exact ⟨d, hdf, hdg, hd_kept, hαd_kept,
    rawEqvGen_of_alpha (keptDel₂_closed data hsep) hd_kept⟩

/-- **Every inner kept side-2 dart raw-connects to the reference.**  By induction on the
`ChordSplitAdj`-reachability of its face from `face₂`.  Mirror of `rawE_inner_kept_to_ref`. -/
lemma rawE_inner_kept_to_ref₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {g : M.Face} (hg : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ g) :
    ∀ a : D, M.dartFace a = g → a ∉ data.keptDel₂ →
      Relation.EqvGen (rawStep₂ data hsep) a (M.φ (M.α data.dart)) := by
  classical
  induction hg with
  | refl =>
      intro a hfa hkept
      have had : a ≠ M.α data.dart := fun h => hkept (h ▸ alphaDart_mem_keptDel₂ data)
      exact rawE_face₂_to_ref data hsep hfa had
  | @tail f g hfg hstep ih =>
      intro a hfa hkept
      have hf_side : f ∈ data.side₂ := hfg
      have hg_side : g ∈ data.side₂ := data.side₂_closed hf_side hstep
      obtain ⟨d, hdf, hdg, hd_kept, hαd_kept, hd_raw⟩ :=
        rawE_chordSplitAdj_step₂ data hsep hf_side hg_side hstep
      have hd_ref : Relation.EqvGen (rawStep₂ data hsep) d (M.φ (M.α data.dart)) :=
        ih d hdf hd_kept
      have hαd_ref : Relation.EqvGen (rawStep₂ data hsep) (M.α d) (M.φ (M.α data.dart)) :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hd_raw) hd_ref
      exact rawE_inner_to_ref₂ data hsep hkept (by rw [hfa]; exact hg_side)
        (by rw [hfa, hdg]) hαd_ref

/-- **Every kept side-2 dart raw-connects to the reference `M.φ (M.α data.dart)`.**  Mirror of
`rawE_kept_to_ref`. -/
lemma rawE_kept_to_ref₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a : D} (hkept : a ∉ data.keptDel₂) :
    Relation.EqvGen (rawStep₂ data hsep) a (M.φ (M.α data.dart)) := by
  classical
  have ha_in : a ∈ data.keptSet₂ := (data.mem_keptDel₂_iff a).mp hkept
  obtain ⟨haU, _⟩ := ha_in
  rcases haU with hinner | houter
  · have hreach : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ (M.dartFace a) :=
      hinner
    exact rawE_inner_kept_to_ref₂ data hsep hreach a rfl hkept
  · obtain ⟨_haouter, hαinner⟩ := houter
    have hαa_kept : M.α a ∉ data.keptDel₂ := fun h =>
      hkept ((keptDel₂_sub data hsep a).2 h)
    have hreach : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ (M.dartFace (M.α a)) :=
      hαinner
    have hαa_ref : Relation.EqvGen (rawStep₂ data hsep) (M.α a) (M.φ (M.α data.dart)) :=
      rawE_inner_kept_to_ref₂ data hsep hreach (M.α a) rfl hαa_kept
    exact Relation.EqvGen.trans _ _ _
      (rawEqvGen_of_alpha (keptDel₂_closed data hsep) hkept) hαa_ref

/-- **The side-2 kept-side raw-reachability predicate, PROVED.**  Mirror of
`keptSideRawConnected`. -/
theorem keptSideRawConnected₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ x y : {d : D // d ∉ data.keptDel₂},
      Relation.EqvGen (rawStep₂ data hsep) x.1 y.1 := by
  intro x y
  exact Relation.EqvGen.trans _ _ _ (rawE_kept_to_ref₂ data hsep x.2)
    (Relation.EqvGen.symm _ _ (rawE_kept_to_ref₂ data hsep y.2))

end RawConnected



/-- **Raw reachability descends to side-2 kept connectivity.**  Mirror of
`keptSide₁_connected_of_rawConnected`. -/
theorem keptSide₂_connected_of_rawConnected (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (hraw : ∀ x y : {d : D // d ∉ data.keptDel₂},
      Relation.EqvGen (rawStep₂ data hsep) x.1 y.1) :
    (sideKeptMap₂ data hsep).Connected := by
  classical
  set Del := data.keptDel₂ with hDel
  set hsub := keptDel₂_sub data hsep with hhsub
  set hclosed := keptDel₂_closed data hsep with hhclosed
  have hsymm : ∀ a b, SubmapPlanar.keptStepRel M Del hsub a b →
      SubmapPlanar.keptStepRel M Del hsub b a :=
    fun a b h => dartStepRel_symm (SubmapPlanar.keptAlpha_invol M Del hsub) h
  intro a b
  have hrawab : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) a.1 b.1 := hraw a b
  have hkept : Relation.EqvGen (SubmapPlanar.keptStepRel M Del hsub) a b :=
    SubmapPlanar.raw_eqvGen_descends M Del hclosed hsub hrawab
  have hreach : Relation.ReflTransGen (SubmapPlanar.keptStepRel M Del hsub) a b :=
    (eqvGen_iff_reflTransGen hsymm a b).1 hkept
  refine hreach.mono ?_
  intro x y hxy
  rcases hxy with hσ | hα
  · left
    show (sideKeptMap₂ data hsep).σ.SameCycle x y
    show data.sideSigma₂.SameCycle x y
    exact hσ
  · right
    show y = (sideKeptMap₂ data hsep).α x
    show y = data.sideAlpha₂ hsep x
    rw [sideAlpha₂_eq_keptAlpha data hsep]
    exact hα

/-- **The kept side-2 map is connected — UNCONDITIONALLY.**  Mirror of `sideKeptMap₁_connected`. -/
theorem sideKeptMap₂_connected (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (sideKeptMap₂ data hsep).Connected :=
  keptSide₂_connected_of_rawConnected data hsep (keptSideRawConnected₂ data hsep)



/-- **`Side₂IsDisk`, UNCONDITIONAL.**  Side 2 of a chord split of a genus-0 near-triangulation is a
combinatorial disk (`IsSphereMap`) given the chord-split data and the separation `Separates` alone:
the genus-0 / Euler-2 half is the structural genus core (`side₂IsDisk_of_connected`), and the
connectivity half is the proved raw reachability (Sections A0/A).  The required kept dart witness is
`M.φ (M.α data.dart)` (kept by `ref_kept₂`).  Mirror of `side₁IsDisk_unconditional`; discharges
`ZinanCh35Side2.chordSideNearTriangulation₂_of_share`'s `hdisk` field. -/
theorem side₂IsDisk_unconditional (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep :=
  side₂IsDisk_of_connected data hsep ⟨M.φ (M.α data.dart), ref_kept₂ data⟩
    (sideKeptMap₂_connected data hsep)

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























/-- The traced face permutation is unchanged when the two anchors are swapped. -/
theorem tracePhi_swap_anchors {K : Type u} [Fintype K] [DecidableEq K]
    (β ρ : Equiv.Perm K) (a₀ a₁ : K) :
    tracePhi β ρ a₁ a₀ = tracePhi β ρ a₀ a₁ := by
  ext k
  by_cases h0 : β k = a₀
  · simp [tracePhi, Equiv.swap_apply_def, h0]
  · by_cases h1 : β k = a₁
    · simp [tracePhi, Equiv.swap_apply_def, h0, h1]
    · simp [tracePhi, Equiv.swap_apply_def, h0, h1]

/-- Root-`inr 0` version of the fresh-map outer-length itinerary. -/
lemma freshMap_outerLen_zero_ge_three {K : Type u} [Fintype K] [DecidableEq K]
    (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
    {a₀ a₁ : K} (hne : a₀ ≠ a₁) (hd : ρ a₁ ≠ β a₀) :
    3 ≤ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).faceDartList (Sum.inr 0)).length := by
  classical
  have hroot_support :
      (Sum.inr 0 : K ⊕ Fin 2) ∈ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.support := by
    rw [Equiv.Perm.mem_support, freshMap_phi_inr_zero β ρ hβinv hβfix hne]
    exact Sum.inl_ne_inr
  have hroot :
      (Sum.inr 0 : K ⊕ Fin 2)
        ∈ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 0) := by
    rw [Equiv.Perm.mem_toList_iff]
    exact ⟨Equiv.Perm.SameCycle.refl _ _, hroot_support⟩
  have hρ :
      (Sum.inl (ρ a₁) : K ⊕ Fin 2)
        ∈ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 0) := by
    rw [Equiv.Perm.mem_toList_iff]
    refine ⟨⟨1, ?_⟩, hroot_support⟩
    rw [zpow_one, freshMap_phi_inr_zero β ρ hβinv hβfix hne]
  have hβ :
      (Sum.inl (β a₀) : K ⊕ Fin 2)
        ∈ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 0) := by
    rw [Equiv.Perm.mem_toList_iff]
    refine ⟨⟨-1, ?_⟩, hroot_support⟩
    rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq,
      freshMap_phi_inl_b0 β ρ hβinv hβfix hne]
  have hdistinct :
      [(Sum.inr 0 : K ⊕ Fin 2), Sum.inl (ρ a₁), Sum.inl (β a₀)].Nodup := by
    have h01 : (Sum.inr 0 : K ⊕ Fin 2) ≠ Sum.inl (ρ a₁) := Sum.inr_ne_inl
    have h02 : (Sum.inr 0 : K ⊕ Fin 2) ≠ Sum.inl (β a₀) := Sum.inr_ne_inl
    have h12 : (Sum.inl (ρ a₁) : K ⊕ Fin 2) ≠ Sum.inl (β a₀) := by
      intro h; exact hd (Sum.inl.inj h)
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ?_⟩⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      exact ⟨h01, h02⟩
    · simp only [List.mem_singleton]; exact h12
    · simp
  have hsub : [(Sum.inr 0 : K ⊕ Fin 2), Sum.inl (ρ a₁), Sum.inl (β a₀)]
      ⊆ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 0) := by
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h
    · rw [h]; exact hroot
    · rw [h]; exact hρ
    · rw [h]; exact hβ
  have hcard : ([(Sum.inr 0 : K ⊕ Fin 2), Sum.inl (ρ a₁), Sum.inl (β a₀)]).length
      ≤ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.toList (Sum.inr 0)).length :=
    (List.subperm_of_subset hdistinct hsub).length_le
  rw [ProofsInTheBook.PlanarMap.CombMap.faceDartList]
  simpa using hcard





/-- **Chain ⟹ `φ`-successor.**  If two boundary darts `d,e` lie on the same boundary cycle and
their endpoint vertices chain (`M.head d = M.tail e`), then `e` is the `φ`-successor of `d`.  Upgrades
a `DartArc.chain` *vertex* equality to a face-walk *dart* equality, via `consecutive_phi` +
`tail_injective_on_darts`. -/
lemma phi_eq_of_boundary_chain
    {f : M.Face} (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {d e : D} (hd : d ∈ C.darts) (he : e ∈ C.darts)
    (hchain : M.head d = M.tail e) :
    M.φ d = e := by
  classical
  rw [List.mem_iff_getElem] at hd
  obtain ⟨n, hn, hdget⟩ := hd
  set p : Fin C.darts.length := ⟨n, hn⟩ with hp
  have hphi_get : C.darts.get (cyclicNext C.normalized.length_pos p) = M.φ d := by
    have := C.consecutive_phi p
    rw [show C.darts.get p = d by rw [List.get_eq_getElem]; exact hdget] at this
    exact this
  have hphi_mem : M.φ d ∈ C.darts := by
    rw [← hphi_get]; exact List.get_mem _ _
  have htail_phi : M.tail (M.φ d) = M.head d := by
    have hv := C.consecutive_vertex p
    rw [hphi_get, show C.darts.get p = d by rw [List.get_eq_getElem]; exact hdget] at hv
    exact hv
  exact C.tail_injective_on_darts hC hphi_mem he (by rw [htail_phi, hchain])

/-- **`M.head` is injective on boundary-cycle darts** (mirror of `tail_injective_on_darts`).  Via the
`φ`-successor: `head d = tail (φ d)` on the cycle, then `tail`-injectivity + `φ` injective. -/
lemma head_injective_on_darts
    {f : M.Face} (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {d e : D} (hd : d ∈ C.darts) (he : e ∈ C.darts)
    (hhead : M.head d = M.head e) :
    d = e := by
  classical
  rw [List.mem_iff_getElem] at hd he
  obtain ⟨nd, hnd, hdget⟩ := hd
  obtain ⟨ne, hne, heget⟩ := he
  set id : Fin C.darts.length := ⟨nd, hnd⟩ with hid
  set ie : Fin C.darts.length := ⟨ne, hne⟩ with hie
  have hgd : C.darts.get id = d := by rw [List.get_eq_getElem]; exact hdget
  have hge : C.darts.get ie = e := by rw [List.get_eq_getElem]; exact heget
  have hphid : C.darts.get (cyclicNext C.normalized.length_pos id) = M.φ d := by
    have := C.consecutive_phi id; rw [hgd] at this; exact this
  have hphie : C.darts.get (cyclicNext C.normalized.length_pos ie) = M.φ e := by
    have := C.consecutive_phi ie; rw [hge] at this; exact this
  have htphid : M.tail (M.φ d) = M.head d := by
    have hv := C.consecutive_vertex id; rw [hphid, hgd] at hv; exact hv
  have htphie : M.tail (M.φ e) = M.head e := by
    have hv := C.consecutive_vertex ie; rw [hphie, hge] at hv; exact hv
  have hpd_mem : M.φ d ∈ C.darts := by rw [← hphid]; exact List.get_mem _ _
  have hpe_mem : M.φ e ∈ C.darts := by rw [← hphie]; exact List.get_mem _ _
  have hφeq : M.φ d = M.φ e :=
    C.tail_injective_on_darts hC hpd_mem hpe_mem (by rw [htphid, htphie, hhead])
  exact M.φ.injective hφeq

/-- **Directed boundary-arc uniqueness, in coverage form.**  If `A` and `B` are two simple directed
boundary arcs with the same endpoints on the same simple boundary cycle, every dart of `B` occurs
on `A`.  The proof walks from the common first tail; at each step `φ`-successor uniqueness pins the
next dart, and `A.head_last_ne_tail` prevents `B` from walking past `A`'s terminal endpoint. -/
lemma dartArc_dart_mem_of_same_endpoints
    {f : M.Face} (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {a b : M.Vertex} (A B : DartArc M C a b) (i : Fin B.len) :
    ∃ j : Fin A.len, B.arcDart i = A.arcDart j := by
  classical
  have aux : ∀ n : ℕ, (hn : n < B.len) →
      ∃ j : Fin A.len, B.arcDart ⟨n, hn⟩ = A.arcDart j := by
    intro n
    induction n with
    | zero =>
        intro hn
        refine ⟨A.firstIdx, ?_⟩
        apply C.tail_injective_on_darts hC (B.boundary ⟨0, hn⟩) (A.boundary A.firstIdx)
        rw [B.tail_first, A.tail_firstIdx]
    | succ n ih =>
        intro hn
        have hn0 : n < B.len := by omega
        obtain ⟨j, hj⟩ := ih hn0
        have hchainB :
            M.head (B.arcDart ⟨n, hn0⟩) = M.tail (B.arcDart ⟨n + 1, hn⟩) :=
          B.chain ⟨n, hn0⟩ (by simpa using hn)
        by_cases hnext : (j : ℕ) + 1 < A.len
        · refine ⟨⟨j + 1, hnext⟩, ?_⟩
          apply C.tail_injective_on_darts hC (B.boundary ⟨n + 1, hn⟩)
            (A.boundary ⟨j + 1, hnext⟩)
          rw [← hchainB, hj, A.chain j hnext]
        · have hjlast : j = A.lastIdx := by
            apply Fin.ext
            have hjlt := j.isLt
            show (j : ℕ) = A.len - 1
            omega
          have htail_terminal :
              M.tail (B.arcDart ⟨n + 1, hn⟩) = b := by
            rw [← hchainB, hj, hjlast, A.head_lastIdx]
          exact False.elim (B.head_last_ne_tail ⟨n + 1, hn⟩ htail_terminal.symm)
  exact aux i.1 i.2

variable (hNT : NearTriangulation M) {u v : M.Vertex}
variable {a b : M.Vertex}





/-- Kept copy of an arc dart. -/
def arcK (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁) (i : Fin A.len) :
    {d : D // d ∉ data.keptDel₁} :=
  ⟨A.arcDart i, hArcKept i⟩

/-- **The side-1 kept face permutation walks one step along the boundary arc.**
`keptPhi = sideSigma₁ ∘ sideAlpha₁` sends the `i`-th arc dart to the `(i+1)`-th.  Route: the arc's
head→tail `chain` upgrades to the outer-face `φ`-step (`phi_eq_of_boundary_chain`); `sideAlpha₁`
restricts to `M.α`; `M.φ = M.σ ∘ M.α`; the next arc dart is kept, so `filteredRotation` agrees with
`M.σ`. -/
lemma sideSigma₁_alpha_arcDart_eq_next
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    data.sideSigma₁ (data.sideAlpha₁ hsep (arcK hNT data A hArcKept i))
      = arcK hNT data A hArcKept ⟨i + 1, hi⟩ := by
  classical
  have hphi : M.φ (A.arcDart i) = A.arcDart ⟨i + 1, hi⟩ :=
    phi_eq_of_boundary_chain hNT.outerCycle hNT.outer_simple
      (A.boundary i) (A.boundary ⟨i + 1, hi⟩) (A.chain i hi)
  have hαcoe : ((data.sideAlpha₁ hsep (arcK hNT data A hArcKept i)) : D) = M.α (A.arcDart i) := by
    simpa [arcK] using data.sideAlpha₁_apply_coe hsep (arcK hNT data A hArcKept i)
  have hσnext : M.σ ((data.sideAlpha₁ hsep (arcK hNT data A hArcKept i)) : D)
      = A.arcDart ⟨i + 1, hi⟩ := by
    rw [hαcoe]; exact hphi
  have hσ_kept : M.σ ((data.sideAlpha₁ hsep (arcK hNT data A hArcKept i)) : D) ∉ data.keptDel₁ := by
    rw [hσnext]; exact hArcKept ⟨i + 1, hi⟩
  apply Subtype.ext
  rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
    FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₁ _ hσ_kept]
  exact hσnext

/-- **The ordered orbit↔arc classifier** (the one genuine remaining bridge).  For the canonical
side-1 anchors, every dart on the side-1 outer `φ`-orbit `S.faceDartList (inr 1)` is either the
chord root `inr 1` or an `inl`-dart whose underlying dart is one of the boundary dart-arc `A`'s
darts.  The `inl`-part of the orbit IS the `u → v` boundary arc. -/
def CanonicalSide₁OuterArcTrace
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁) : Prop :=
  ∀ x, x ∈ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1) →
    x = Sum.inr 1 ∨ ∃ i : Fin A.len, x = Sum.inl ⟨A.arcDart i, hArcKept i⟩

/-- **`OuterTraceInjOn` for the canonical anchors, from the orbit↔arc classifier.**  The chord
root `inr 1` carries `v` (`canonicalAnchor₁_tail` + the chord orientation `M.head data.dart = v`);
each `inl`-dart carries an arc tail.  `v` is not an arc tail (`A.head_last_ne_tail`), so root vs
arc cannot collide; two arc darts with equal tail are equal (`A.tail_nodup`). -/
theorem canonical_OuterTraceInjOn_of_arcTrace
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hb : M.head data.dart = b)
    (htrace : CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept) :
    OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) := by
  -- The root's projected tail is `b` (the arc terminal).
  have hroot : M.tail (proj (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (Sum.inr 1)).1 = b := by
    rw [proj_inr_one, canonicalAnchor₁_tail data hsep, hb]
  intro x hx y hy htail
  rcases htrace x hx with hxr | ⟨i, hxi⟩ <;> rcases htrace y hy with hyr | ⟨j, hyj⟩
  · -- root, root
    rw [hxr, hyr]
  · -- root, arc j  →  v = M.tail (arc j), impossible
    exfalso
    rw [hxr] at htail
    rw [hyj] at htail
    simp only [proj_inl, hroot] at htail
    exact A.head_last_ne_tail j htail
  · -- arc i, root  →  M.tail (arc i) = v, impossible
    exfalso
    rw [hyr] at htail
    rw [hxi] at htail
    simp only [proj_inl, hroot] at htail
    exact A.head_last_ne_tail i htail.symm
  · -- arc i, arc j  →  tails equal ⟹ i = j
    rw [hxi, hyj]
    rw [hxi, hyj] at htail
    simp only [proj_inl] at htail
    have hij : i = j := A.tail_nodup htail
    rw [hij]

/-- **Orbit membership iff** (canonical anchors).  A dart is on the side-1 outer `φ`-orbit
`S.faceDartList (inr 1)` iff it is the chord root `inr 1` or an `inl`-dart `inl k` with `k` in the
`tracePhi`-orbit of `β a₁`.  The negative case `inr 0` is excluded by the splice-split fact
`side₁_chordPred_notSameCycle_canonical` (the two chord predecessors are NOT `tracePhi`-SameCycle). -/
theorem canonical_side₁_outer_orbit_mem_iff
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (x : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    x ∈ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)
      ↔ x = Sum.inr 1 ∨
        ∃ k : {d : D // d ∉ data.keptDel₁}, x = Sum.inl k ∧
          (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
              (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
            ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) k := by
  classical
  -- shorthands
  set a₀ := side₁Anchor₀ data hsep with ha₀
  set a₁ := side₁Anchor₁ data hsep with ha₁
  set hne := side₁Anchors_ne data hsep with hhne
  set β := data.sideAlpha₁ hsep with hβ
  set ρ := data.sideSigma₁ with hρ
  have hinv : β * β = 1 := data.sideAlpha₁_involutive hsep
  have hfix : ∀ k, β k ≠ k := data.sideAlpha₁_no_fixed hsep
  -- the side map IS the fresh map.
  have hSeq : data.sideMap₁ hsep a₀ a₁ hne = freshMap β ρ hinv hfix a₀ a₁ hne := rfl
  -- the splice-split: ¬ τ.SameCycle (β a₁) (β a₀).
  have hsplit : ¬ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) (β a₀) := by
    intro h
    exact side₁_chordPred_notSameCycle_canonical data hsep h.symm
  -- root in the support of φ.
  have hroot_support :
      (Sum.inr 1 : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2)
        ∈ (freshMap β ρ hinv hfix a₀ a₁ hne).φ.support := by
    rw [Equiv.Perm.mem_support, freshMap_phi_inr_one β ρ hinv hfix hne]
    exact Sum.inl_ne_inr
  rw [hSeq, CombMap.faceDartList]
  constructor
  · intro hx
    rw [Equiv.Perm.mem_toList_iff] at hx
    obtain ⟨hcyc, _⟩ := hx
    -- transport the φ-SameCycle (inr 1 → x) to a tracePhi-SameCycle of faceProjs.
    have hτ : (tracePhi β ρ a₀ a₁).SameCycle (β a₁) (faceProj β a₀ a₁ x) := by
      have h := (freshFace_sameCycle_iff β ρ hinv hfix hne (Sum.inr 1) x).1 hcyc
      simpa [faceProj_inr_one] using h
    cases x with
    | inl k =>
        right
        exact ⟨k, rfl, by simpa [faceProj_inl] using hτ⟩
    | inr j =>
        fin_cases j
        · -- inr 0, excluded by the splice-split fact
          exact absurd (by simpa [faceProj_inr_zero] using hτ) hsplit
        · left; rfl
  · intro hx
    rw [Equiv.Perm.mem_toList_iff]
    refine ⟨?_, hroot_support⟩
    rcases hx with hroot | ⟨k, hxk, hk⟩
    · rw [hroot]
    · rw [hxk]
      refine (freshFace_sameCycle_iff β ρ hinv hfix hne (Sum.inr 1) (Sum.inl k)).2 ?_
      simpa [faceProj_inl, faceProj_inr_one] using hk

/-- **The canonical `tracePhi` orbit through `β a₁` is exactly the kept copies of the `u → v`
boundary dart-arc `A`** (the genuine remaining bridge — proved separately).  Packaged as a `Prop`
so the classifier follows mechanically. -/
structure CanonicalTracePhiArc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁) : Prop where
  mem_iff : ∀ k : {d : D // d ∉ data.keptDel₁},
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) k
    ↔ ∃ i : Fin A.len, k = ⟨A.arcDart i, hArcKept i⟩

/-- **The classifier from the `tracePhi`-orbit ↔ arc identification.**  Combines the membership iff
(`canonical_side₁_outer_orbit_mem_iff`) with `CanonicalTracePhiArc`: an orbit dart is `inr 1` or
`inl k`; in the latter case `k`'s `tracePhi`-membership pins it to an arc dart. -/
theorem canonical_arcTrace_of_tracePhiArc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hTA : CanonicalTracePhiArc hNT data hsep A hArcKept) :
    CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept := by
  intro x hx
  rcases (canonical_side₁_outer_orbit_mem_iff hNT data hsep x).1 hx with hroot | ⟨k, hxk, hτ⟩
  · exact Or.inl hroot
  · rcases (hTA.mem_iff k).1 hτ with ⟨i, hk⟩
    exact Or.inr ⟨i, by rw [hxk, hk]⟩



/-- `arcK` is injective (its underlying darts have distinct tails). -/
lemma arcK_injective (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    {i j : Fin A.len} (h : arcK hNT data A hArcKept i = arcK hNT data A hArcKept j) :
    i = j := by
  apply A.tail_nodup
  show M.tail (A.arcDart i) = M.tail (A.arcDart j)
  have hd : A.arcDart i = A.arcDart j := by
    have := congrArg Subtype.val h; simpa [arcK] using this
  rw [hd]

/-- **`tracePhi` walks one step along the arc** (interior step).  Uses `tracePhi_other` (the two
chord-predecessor exceptions `β a₀, β a₁` are avoided) + the kept-σ walk. -/
lemma tracePhi_arc_step
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hlast : data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
    (hnot_beta_a₀ : ∀ i : Fin A.len,
      arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep))
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
        (arcK hNT data A hArcKept i)
      = arcK hNT data A hArcKept ⟨i + 1, hi⟩ := by
  classical
  have hβinv : data.sideAlpha₁ hsep * data.sideAlpha₁ hsep = 1 := data.sideAlpha₁_involutive hsep
  have hinv2 : ∀ x, data.sideAlpha₁ hsep (data.sideAlpha₁ hsep x) = x := by
    intro x; rw [← Equiv.Perm.mul_apply, hβinv, Equiv.Perm.one_apply]
  -- β (arcK i) ≠ ρ-anchor-predecessors a₀, a₁
  have hnot0 : data.sideAlpha₁ hsep (arcK hNT data A hArcKept i) ≠ side₁Anchor₀ data hsep := by
    intro h
    apply hnot_beta_a₀ i
    have h2 := congrArg (data.sideAlpha₁ hsep) h
    rw [hinv2] at h2
    exact h2
  have hnot1 : data.sideAlpha₁ hsep (arcK hNT data A hArcKept i) ≠ side₁Anchor₁ data hsep := by
    intro h
    have h2 := congrArg (data.sideAlpha₁ hsep) h
    rw [hinv2] at h2
    rw [hlast] at h2
    have hieq : i = (⟨A.len - 1, by have := A.len_pos; omega⟩ : Fin A.len) :=
      arcK_injective hNT data A hArcKept h2
    have hi2 : (i : ℕ) = A.len - 1 := by rw [hieq]
    omega
  rw [tracePhi_other (data.sideAlpha₁ hsep) data.sideSigma₁ (side₁Anchor₀ data hsep)
    (side₁Anchor₁ data hsep) hnot0 hnot1]
  exact sideSigma₁_alpha_arcDart_eq_next hNT data hsep A hArcKept i hi

/-- **`tracePhi` wraps from the last arc dart back to the first** (the splice step `β a₁ ↦ ρ a₀`). -/
lemma tracePhi_arc_wrap
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hfirst : data.sideSigma₁ (side₁Anchor₀ data hsep)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩)
    (hlast : data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩ := by
  rw [← hlast, tracePhi_b1 (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)]
  exact hfirst

/-- From the last arc dart, every `tracePhi`-iterate stays within the arc. -/
lemma tracePhi_iterate_last_mem_arc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
          (arcK hNT data A hArcKept i) = arcK hNT data A hArcKept ⟨i + 1, hi⟩)
    (hwrap : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩)
    (n : ℕ) :
    ∃ i : Fin A.len,
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))^[n]
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
        = arcK hNT data A hArcKept i := by
  classical
  induction n with
  | zero => exact ⟨⟨A.len - 1, by have := A.len_pos; omega⟩, rfl⟩
  | succ n ih =>
      rcases ih with ⟨i, hi_eq⟩
      rw [Function.iterate_succ_apply', hi_eq]
      by_cases hlt : (i : ℕ) + 1 < A.len
      · exact ⟨⟨i + 1, hlt⟩, hstep i hlt⟩
      · have hi_last : i = (⟨A.len - 1, by have := A.len_pos; omega⟩ : Fin A.len) := by
          apply Fin.ext
          show (i : ℕ) = A.len - 1
          have h1 := i.isLt
          have h2 : ¬ ((i : ℕ) + 1 < A.len) := hlt
          omega
        rw [hi_last]; exact ⟨⟨0, A.len_pos⟩, hwrap⟩

/-- Every arc dart is `tracePhi`-SameCycle to the last arc dart (walk first→i, wrap last→first). -/
lemma tracePhi_sameCycle_last_arc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
          (arcK hNT data A hArcKept i) = arcK hNT data A hArcKept ⟨i + 1, hi⟩)
    (hwrap : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩)
    (i : Fin A.len) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      (arcK hNT data A hArcKept i) := by
  classical
  set τ := tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) with hτdef
  -- first reachable from last in one step (wrap)
  have hlast_first : τ.SameCycle (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      (arcK hNT data A hArcKept ⟨0, A.len_pos⟩) := ⟨1, by rw [zpow_one]; exact hwrap⟩
  -- from first, reach index n by walking n steps
  have hfrom_first : ∀ n : ℕ, ∀ hn : n < A.len,
      τ.SameCycle (arcK hNT data A hArcKept ⟨0, A.len_pos⟩) (arcK hNT data A hArcKept ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro hn; exact Equiv.Perm.SameCycle.refl _ _
    | succ m ih =>
        intro hn
        have hm : m < A.len := by omega
        have hmstep : (m : ℕ) + 1 < A.len := by
          simpa using hn
        refine (ih hm).trans ?_
        refine ⟨1, ?_⟩
        rw [zpow_one]
        have := hstep ⟨m, hm⟩ (by simpa using hmstep)
        -- arcK ⟨m,hm⟩ → arcK ⟨m+1, _⟩ = arcK ⟨n, hn⟩
        simpa using this
  exact hlast_first.trans (hfrom_first i.1 i.2)

/-- **`CanonicalTracePhiArc` from the step/wrap/endpoint data.**  Given the interior step, the wrap,
the two endpoint alignments, and the `β a₀`-exclusion, the `tracePhi`-orbit of `β a₁` is exactly the
arc darts. -/
theorem canonicalTracePhiArc_of_steps
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hfirst : data.sideSigma₁ (side₁Anchor₀ data hsep)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩)
    (hlast : data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
    (hnot_beta_a₀ : ∀ i : Fin A.len,
      arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep)) :
    CanonicalTracePhiArc hNT data hsep A hArcKept := by
  classical
  have hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
          (arcK hNT data A hArcKept i) = arcK hNT data A hArcKept ⟨i + 1, hi⟩ :=
    fun i hi => tracePhi_arc_step hNT data hsep A hArcKept hlast hnot_beta_a₀ i hi
  have hwrap := tracePhi_arc_wrap hNT data hsep A hArcKept hfirst hlast
  refine ⟨fun k => ?_⟩
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := hk.exists_nat_pow_eq
    have hn' : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))^[n]
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩) = k := by
      rw [Equiv.Perm.coe_pow] at hn
      rw [← hlast]; exact hn
    obtain ⟨i, hi⟩ := tracePhi_iterate_last_mem_arc hNT data hsep A hArcKept hstep hwrap n
    exact ⟨i, hn'.symm.trans hi⟩
  · rintro ⟨i, rfl⟩
    have hsc := tracePhi_sameCycle_last_arc hNT data hsep A hArcKept hstep hwrap i
    rw [hlast]; exact hsc





/-- **`hnot_beta_a₀`** (self-contained): `β a₀ = sideAlpha₁ (side₁Anchor₀) = face₁Dart₂`, an inner
chord-triangle dart whose face is `face₁ ≠ outerFace`; so it is none of the boundary arc darts. -/
lemma hnot_beta_a₀_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (i : Fin A.len) :
    arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep) := by
  intro h
  have ha₀ : side₁Anchor₀ data hsep = data.sideAlpha₁ hsep (face₁Dart₂ data) := by
    apply data.sideSigma₁.injective
    rw [sideSigma₁_side₁Anchor₀ data hsep]
    rfl
  have hinv2 : ∀ x, data.sideAlpha₁ hsep (data.sideAlpha₁ hsep x) = x := by
    intro x
    rw [← Equiv.Perm.mul_apply, data.sideAlpha₁_involutive hsep, Equiv.Perm.one_apply]
  have hβa₀ : data.sideAlpha₁ hsep (side₁Anchor₀ data hsep) = face₁Dart₂ data := by
    rw [ha₀]; exact hinv2 _
  -- arcK i = β a₀ (from h), so the arc dart's face = the inner chord face₁, but it is outerFace.
  have houter : M.dartFace ((data.sideAlpha₁ hsep (side₁Anchor₀ data hsep)) : D) = hNT.outerFace := by
    rw [← congrArg Subtype.val h]
    exact (hNT.outerCycle.mem_darts_iff _).mp (A.boundary i)
  have hinner : M.dartFace ((data.sideAlpha₁ hsep (side₁Anchor₀ data hsep)) : D) = data.face₁ := by
    rw [hβa₀]
    show M.dartFace (M.φ (M.φ data.dart)) = M.dartFace data.dart
    rw [M.dartFace_phi, M.dartFace_phi]
  exact data.face₁_not_outer (hinner.symm.trans houter)

/-- **`hArcKept` for the side-1 arc `bwdArc`, UNCONDITIONAL.**  Each `bwdArc` dart's `α`-reverse
face is in `side₁` (`bwdArc_reverse_face_mem_side₁`), so it lies in `outerArc₁ ⊆ keptSet₁`; it is
not the chord dart (`bwdArc_dartEdge_ne_chord`).  No orientation / region hypothesis. -/
lemma bwdArc_arcDart_notMem_keptDel₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (i : Fin (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).len) :
    (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i ∉ data.keptDel₁ := by
  classical
  have hbmem : (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i ∈ hNT.outerCycle.darts :=
    (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary i
  have hface : M.dartFace ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i)
      = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff _).mp hbmem
  have hconf : M.dartFace (M.α ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i))
      ∈ data.side₁ :=
    ProofsInTheBook.ZinanCh35ArcSide.bwdArc_reverse_face_mem_side₁ data i
  have hne : (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i ≠ data.dart := by
    intro he
    apply ProofsInTheBook.ZinanCh35ArcSide.bwdArc_dartEdge_ne_chord data i
    rw [he]; exact hNT.chordDart_edge data.chord
  rw [data.mem_keptDel₁_iff]
  exact ⟨Or.inr ⟨hface, hconf⟩, by simpa using hne⟩



/-- Boundary membership of a kept dart from `dartFace ∉ side₁`. -/
lemma kept_mem_outerCycle_of_face_not_side₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁})
    (hface : M.dartFace (k : D) ∉ data.side₁) :
    (k : D) ∈ hNT.outerCycle.darts := by
  classical
  have hkept : (k : D) ∈ data.keptSet₁ := (data.mem_keptDel₁_iff _).1 k.2
  have hmem : (k : D) ∈ data.sideDarts₁ ∪ data.outerArc₁ := hkept.1
  rcases hmem with hsd | hoa
  · -- ∈ sideDarts₁ = {d | dartFace d ∈ side₁} contradicts hface
    exact absurd hsd hface
  · -- ∈ outerArc₁ ⟹ dartFace = outerFace ⟹ boundary
    exact (hNT.outerCycle.mem_darts_iff _).2 hoa.1



/-- **The lone remaining residue**: the canonical splice darts `ρ a₀`, `β a₁` are boundary darts
(equivalently, they are the first/last darts of the side-1 arc `bwdArc`).  This is the vertex-star →
boundary endpoint alignment — NOT derivable from the arc/orbit machinery (which is all proved). -/
structure CanonicalBwdArcEndpointAlignment
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop where
  ρa₀_boundary : ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts
  βa₁_boundary : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts

/-- `ρ a₀ = bwdArc's first dart` (from `ρ a₀` boundary; both have tail `M.tail data.dart`). -/
lemma sideSigma₁_anchor₀_eq_bwdArc_first
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hρa₀ : ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideSigma₁ (side₁Anchor₀ data hsep)
      = ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx,
          bwdArc_arcDart_notMem_keptDel₁ hNT data hsep _⟩ := by
  apply Subtype.ext
  apply hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hρa₀
    ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary _)
  have hL : M.tail ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) = M.tail data.dart := by
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
      ProofsInTheBook.ChordSigmaContig.tail_filteredRotation data.keptDel₁ (side₁Anchor₀ data hsep)]
    exact canonicalAnchor₀_tail data hsep
  have hR : M.tail ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx) = M.tail data.dart := by
    rw [(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).tail_firstIdx, M.head_alpha]
  rw [hL, hR]

/-- `β a₁ = bwdArc's last dart` (from `β a₁` boundary; both have head `M.head data.dart`). -/
lemma sideAlpha₁_anchor₁_eq_bwdArc_last
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hβa₁ : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx,
          bwdArc_arcDart_notMem_keptDel₁ hNT data hsep _⟩ := by
  apply Subtype.ext
  apply head_injective_on_darts hNT.outerCycle hNT.outer_simple hβa₁
    ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary _)
  have hL : M.head ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) = M.head data.dart := by
    have hαcoe : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D)
        = M.α (side₁Anchor₁ data hsep).1 := by
      simpa using data.sideAlpha₁_apply_coe hsep (side₁Anchor₁ data hsep)
    rw [hαcoe, M.head_alpha, canonicalAnchor₁_tail data hsep]
  have hR : M.head ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx) = M.head data.dart := by
    rw [(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).head_lastIdx, M.tail_alpha]
  rw [hL, hR]



/-- **First endpoint:** `ρ a₀` (the σ-successor of the canonical anchor `a₀`) is the first arc dart.
Both have tail `u`; `tail_injective_on_darts` pins them equal. -/
lemma canonical_trace_start_eq_first_arc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (ha : M.tail data.dart = a)
    (hρa₀_boundary : ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideSigma₁ (side₁Anchor₀ data hsep) = arcK hNT data A hArcKept ⟨0, A.len_pos⟩ := by
  apply Subtype.ext
  apply hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hρa₀_boundary
    (A.boundary ⟨0, A.len_pos⟩)
  have hfix : M.tail ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D)
      = M.tail (side₁Anchor₀ data hsep).1 := by
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
      ProofsInTheBook.ChordSigmaContig.tail_filteredRotation data.keptDel₁
        (side₁Anchor₀ data hsep)]
  rw [hfix, canonicalAnchor₀_tail data hsep, ha]
  exact A.tail_first.symm

/-- **Last endpoint:** `β a₁` (the α-partner of the canonical anchor `a₁`) is the last arc dart.
Both have head `v`; `head_injective_on_darts` pins them equal. -/
lemma canonical_trace_root_eq_last_arc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hb : M.head data.dart = b)
    (hβa₁_boundary :
      ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩ := by
  apply Subtype.ext
  apply head_injective_on_darts hNT.outerCycle hNT.outer_simple hβa₁_boundary
    (A.boundary ⟨A.len - 1, by have := A.len_pos; omega⟩)
  have hαcoe : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D)
      = M.α (side₁Anchor₁ data hsep).1 := by
    simpa using data.sideAlpha₁_apply_coe hsep (side₁Anchor₁ data hsep)
  rw [hαcoe, M.head_alpha, canonicalAnchor₁_tail data hsep, hb]
  exact A.head_last.symm

/-- **The residue, sharpened to two face-facts.**  `CanonicalBwdArcEndpointAlignment` follows from
the canonical splice darts' faces not lying in `side₁` (the genuine cyclic-order content: the
kept-σ step off the chord triangle exits the side-1 faces onto the outer boundary). -/
theorem canonicalBwdArcEndpointAlignment_of_faces
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hρ : M.dartFace ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∉ data.side₁)
    (hβ : M.dartFace ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∉ data.side₁) :
    CanonicalBwdArcEndpointAlignment hNT data hsep :=
  ⟨kept_mem_outerCycle_of_face_not_side₁ hNT data hsep _ hρ,
   kept_mem_outerCycle_of_face_not_side₁ hNT data hsep _ hβ⟩

/-- **`OuterTraceInjOn` for the canonical anchors, reduced to the genuine external facts.**  Ties
the whole chain: endpoint alignment → `canonicalTracePhiArc_of_steps` → classifier → reduction. -/
theorem canonical_OuterTraceInjOn_of_alignment
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (H : CanonicalBwdArcEndpointAlignment hNT data hsep) :
    OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) := by
  set A := ProofsInTheBook.ZinanCh35ArcSide.bwdArc data with hA
  -- A : DartArc M outerCycle (M.head (M.α data.dart)) (M.tail (M.α data.dart))
  have hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁ :=
    fun i => bwdArc_arcDart_notMem_keptDel₁ hNT data hsep i
  -- endpoint relations (no orientation needed; bwdArc's endpoints are the chord dart's tail/head)
  have ha : M.tail data.dart = M.head (M.α data.dart) := (M.head_alpha data.dart).symm
  have hb : M.head data.dart = M.tail (M.α data.dart) := (M.tail_alpha data.dart).symm
  have hfirst := canonical_trace_start_eq_first_arc hNT data hsep A hArcKept ha H.ρa₀_boundary
  have hlast := canonical_trace_root_eq_last_arc hNT data hsep A hArcKept hb H.βa₁_boundary
  have hnot : ∀ i : Fin A.len,
      arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep) :=
    fun i => hnot_beta_a₀_canonical hNT data hsep A hArcKept i
  have hTA := canonicalTracePhiArc_of_steps hNT data hsep A hArcKept hfirst hlast hnot
  have htrace := canonical_arcTrace_of_tracePhiArc hNT data hsep A hArcKept hTA
  exact canonical_OuterTraceInjOn_of_arcTrace hNT data hsep A hArcKept hb htrace

/-- A side-1 dart different from the chord dart is a kept side-1 dart. -/
 lemma keptSet₁_of_side₁_ne_dart
    (data : hNT.ChordSplitData u v) {d : D}
    (hside : M.dartFace d ∈ data.side₁) (hne : d ≠ data.dart) :
    d ∈ data.keptSet₁ := by
  exact ⟨Or.inl hside, by simpa using hne⟩

/-- The inverse `σ`-power stays in the same vertex star. -/
 lemma tail_pow_sigma_inv (n : ℕ) (d : D) :
    M.tail ((M.σ⁻¹ ^ n) d) = M.tail d := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    calc
      M.tail (M.σ⁻¹ ((M.σ⁻¹ ^ n) d))
          = M.tail (M.σ (M.σ⁻¹ ((M.σ⁻¹ ^ n) d))) := (M.tail_sigma _).symm
      _ = M.tail ((M.σ⁻¹ ^ n) d) := by simp
      _ = M.tail d := ih

/-- The first inverse-`σ` step from `face₁Dart₁` is the deleted chord reverse. -/
 lemma face₁Dart₁_inv_firstOutside_ge_two
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    2 ≤ Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₁ (face₁Dart₁ data) := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₁
      (face₁Dart₁ data) :=
    Equiv.Perm.DeleteSet.firstOutside_pos M.σ⁻¹ data.keptDel₁ _
  have heq1 : Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₁
      (face₁Dart₁ data) = 1 := by omega
  have hnot := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ⁻¹ data.keptDel₁
    (face₁Dart₁ data)
  rw [heq1, pow_one] at hnot
  have hstep : M.σ⁻¹ ((face₁Dart₁ data : {d : D // d ∉ data.keptDel₁}) : D)
      = M.α data.dart := by
    show M.σ⁻¹ (M.φ data.dart) = M.α data.dart
    apply M.σ.injective
    calc
      M.σ (M.σ⁻¹ (M.φ data.dart)) = M.φ data.dart :=
        Equiv.apply_symm_apply M.σ (M.φ data.dart)
      _ = M.σ (M.α data.dart) := by
        show M.φ data.dart = (M.σ * M.α) data.dart
        rfl
  have hdeleted : M.α data.dart ∈ data.keptDel₁ := by
    by_contra hαdel
    exact data.alphaDart_notMem_keptSet₁ hsep ((data.mem_keptDel₁_iff _).1 hαdel)
  exact hnot (by rwa [hstep])

/-- First endpoint face fact: the kept `σ`-successor of `a₀` is not a side-1 dart. -/
theorem face_ρa₀_not_side₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.dartFace ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∉ data.side₁ := by
  classical
  intro htarget
  set x : {d : D // d ∉ data.keptDel₁} :=
    data.sideAlpha₁ hsep (face₁Dart₂ data) with hx
  set n := Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁ x with hn
  set p : D := (M.σ ^ (n - 1)) x.1 with hp
  have hn_ge : 2 ≤ n := by
    rw [hn]
    exact ProofsInTheBook.ChordBigonWrap.sideSigma₁_sideAlpha₁_firstOutside_ge_two data hsep
  have hp_deleted : p ∈ data.keptDel₁ := by
    by_contra hp_not
    have hmin := Equiv.Perm.DeleteSet.firstOutside_min M.σ data.keptDel₁ x
      (m := n - 1) (by rw [hn]; omega)
    exact hmin ⟨by omega, by simpa [p] using hp_not⟩
  have htarget_coe :
      ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) = (M.σ ^ n) x.1 := by
    rw [sideSigma₁_side₁Anchor₀ data hsep]
    change ((data.sideSigma₁ (data.sideAlpha₁ hsep (face₁Dart₂ data))) : D)
        = (M.σ ^ n) x.1
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl]
    rw [FilteredRotation.filteredRotation_apply_coe]
  have htarget_side_pow : M.dartFace ((M.σ ^ n) x.1) ∈ data.side₁ := by
    rw [htarget_coe] at htarget
    exact htarget
  have hσp : M.σ p = (M.σ ^ n) x.1 := by
    rw [hp]
    have hs : n - 1 + 1 = n := by omega
    rw [← hs, pow_succ']
    rfl
  have hαp_side : M.dartFace (M.α p) ∈ data.side₁ := by
    rw [← ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M) p]
    rw [hσp]
    exact htarget_side_pow
  have hp_ne_dart : p ≠ data.dart := by
    intro hpd
    have hface₂_side : data.face₂ ∈ data.side₁ := by
      have : M.dartFace (M.α data.dart) ∈ data.side₁ := by
        rwa [hpd] at hαp_side
      simpa [ChordSplitData.face₂] using this
    exact hsep hface₂_side
  have hx_coe : (x : D) = M.α (M.φ (M.φ data.dart)) := by
    rw [hx, data.sideAlpha₁_apply_coe hsep]
    rfl
  have hp_tail : M.tail p = M.tail data.dart := by
    rw [hp, ProofsInTheBook.ChordSigmaContig.tail_pow_sigma, hx_coe,
      ProofsInTheBook.ChordSigmaContig.tail_alpha_phiSq_dart data]
  have hp_ne_alpha_dart : p ≠ M.α data.dart := by
    intro hpα
    have htail_eq : M.tail data.dart = M.head data.dart := by
      rw [← hp_tail, hpα, M.tail_alpha]
    exact ProofsInTheBook.ChordSigmaContig.u_ne_v data htail_eq
  have hp_kept : p ∈ data.keptSet₁ := by
    by_cases hp_outer : M.dartFace p = hNT.outerFace
    · exact ⟨Or.inr ⟨hp_outer, hαp_side⟩, by simpa using hp_ne_dart⟩
    · have hp_not_boundary : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge p) := by
        intro hbe
        rcases data.boundaryEdge_dart_outer hbe with hpout | hαout
        · exact hp_outer hpout
        · exact data.side₁_subset_nonouter hαp_side hαout
      have hp_not_chord : M.dartEdge p ≠ s(u, v) := by
        intro hch
        rcases data.chord_edge_darts hch with hpd | hpα
        · exact hp_ne_dart hpd
        · exact hp_ne_alpha_dart hpα
      have hp_side : M.dartFace p ∈ data.side₁ := by
        have hα_edge_not_boundary :
            ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge (M.α p)) := by
          intro hbe
          exact hp_not_boundary (by rwa [M.dartEdge_alpha] at hbe)
        have hα_edge_not_chord : M.dartEdge (M.α p) ≠ s(u, v) := by
          intro hch
          exact hp_not_chord (by rwa [M.dartEdge_alpha] at hch)
        have := data.alpha_mem_side₁_of_interior (e := M.α p) hαp_side
          hα_edge_not_boundary hα_edge_not_chord
        rwa [M.alpha_alpha] at this
      exact keptSet₁_of_side₁_ne_dart hNT data hp_side hp_ne_dart
  have hp_not_deleted : p ∉ data.keptDel₁ := (data.mem_keptDel₁_iff p).2 hp_kept
  exact hp_not_deleted hp_deleted

/-- Second endpoint face fact: the edge-reverse of `a₁` is not a side-1 dart. -/
theorem face_βa₁_not_side₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.dartFace ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∉ data.side₁ := by
  classical
  intro hβside
  set x : {d : D // d ∉ data.keptDel₁} := face₁Dart₁ data with hx
  set n := Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₁ x with hn
  set p : D := (M.σ⁻¹ ^ (n - 1)) x.1 with hp
  have hn_ge : 2 ≤ n := by
    rw [hn, hx]
    exact face₁Dart₁_inv_firstOutside_ge_two hNT data hsep
  have hp_deleted : p ∈ data.keptDel₁ := by
    by_contra hp_not
    have hmin := Equiv.Perm.DeleteSet.firstOutside_min M.σ⁻¹ data.keptDel₁ x
      (m := n - 1) (by rw [hn]; omega)
    exact hmin ⟨by omega, by simpa [p] using hp_not⟩
  have ha₁_coe : ((side₁Anchor₁ data hsep) : D) = (M.σ⁻¹ ^ n) x.1 := by
    rw [side₁Anchor₁]
    change ((Equiv.Perm.DeleteSet.deleteSetFun M.σ⁻¹ data.keptDel₁
        (face₁Dart₁ data)) : D) = (M.σ⁻¹ ^ n) x.1
    rw [Equiv.Perm.DeleteSet.deleteSetFun_coe]
  have hσa₁ : M.σ ((side₁Anchor₁ data hsep : {d : D // d ∉ data.keptDel₁}) : D) = p := by
    rw [ha₁_coe, hp]
    have hs : n - 1 + 1 = n := by omega
    have hpow : (M.σ⁻¹ ^ n) x.1 = M.σ⁻¹ ((M.σ⁻¹ ^ (n - 1)) x.1) := by
      rw [← hs, pow_succ']
      rfl
    rw [hpow]
    simp
  have hβcoe : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D)
      = M.α ((side₁Anchor₁ data hsep : {d : D // d ∉ data.keptDel₁}) : D) := by
    rw [data.sideAlpha₁_apply_coe hsep]
  have hp_side : M.dartFace p ∈ data.side₁ := by
    rw [← hσa₁]
    rw [ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M)]
    rwa [← hβcoe]
  have hp_tail : M.tail p = M.head data.dart := by
    rw [hp, tail_pow_sigma_inv, hx]
    exact ProofsInTheBook.ChordSigmaContig.face₁Dart₁_tail data
  have hp_ne_dart : p ≠ data.dart := by
    intro hpd
    have htail_eq : M.tail data.dart = M.head data.dart := by
      rw [← hp_tail, hpd]
    exact ProofsInTheBook.ChordSigmaContig.u_ne_v data htail_eq
  have hp_not_deleted : p ∉ data.keptDel₁ :=
    (data.mem_keptDel₁_iff p).2 (keptSet₁_of_side₁_ne_dart hNT data hp_side hp_ne_dart)
  exact hp_not_deleted hp_deleted

/-- Canonical endpoint alignment with the two cyclic-order face facts discharged. -/
theorem canonicalBwdArcEndpointAlignment_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    CanonicalBwdArcEndpointAlignment hNT data hsep :=
  canonicalBwdArcEndpointAlignment_of_faces hNT data hsep
    (face_ρa₀_not_side₁ hNT data hsep)
    (face_βa₁_not_side₁ hNT data hsep)

/-- Unconditional `OuterTraceInjOn` for the canonical anchors. -/
theorem canonical_OuterTraceInjOn_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) :=
  canonical_OuterTraceInjOn_of_alignment hNT data hsep
    (canonicalBwdArcEndpointAlignment_uncond hNT data hsep)

/-- Unconditional `tracePhi` orbit ↔ canonical side-1 boundary arc identification. -/
theorem canonicalTracePhiArc_bwdArc_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    CanonicalTracePhiArc hNT data hsep
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data)
      (fun i => bwdArc_arcDart_notMem_keptDel₁ hNT data hsep i) := by
  classical
  set A := ProofsInTheBook.ZinanCh35ArcSide.bwdArc data
  set hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁ :=
    fun i => bwdArc_arcDart_notMem_keptDel₁ hNT data hsep i
  have H := canonicalBwdArcEndpointAlignment_uncond hNT data hsep
  have hfirst :
      data.sideSigma₁ (side₁Anchor₀ data hsep) =
        arcK hNT data A hArcKept ⟨0, A.len_pos⟩ := by
    simpa [A, hArcKept, arcK] using
      sideSigma₁_anchor₀_eq_bwdArc_first hNT data hsep H.ρa₀_boundary
  have hlast :
      data.sideAlpha₁ hsep (side₁Anchor₁ data hsep) =
        arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩ := by
    simpa [A, hArcKept, arcK, DartArc.lastIdx] using
      sideAlpha₁_anchor₁_eq_bwdArc_last hNT data hsep H.βa₁_boundary
  have hnot : ∀ i : Fin A.len,
      arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep) :=
    fun i => hnot_beta_a₀_canonical hNT data hsep A hArcKept i
  exact canonicalTracePhiArc_of_steps hNT data hsep A hArcKept hfirst hlast hnot

/-- Every canonical side-1 outer-arc dart is one of the `bwdArc` darts. -/
theorem outerArc₁_mem_bwdArc_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) {d : D}
    (hdouter : d ∈ data.outerArc₁) :
    ∃ i : Fin (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).len,
      d = (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i := by
  classical
  set C := hNT.outerCycle
  have hdmem : d ∈ C.darts := by
    exact (C.mem_darts_iff d).2 hdouter.1
  have hne : M.tail data.dart ≠ M.head data.dart :=
    ProofsInTheBook.ChordSigmaContig.u_ne_v data
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  have hxy_edge : s(M.tail data.dart, M.head data.dart) = s(u, v) := hedge
  have htail_bv : C.IsBoundaryVertex (M.tail data.dart) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · rw [hxu]; exact data.chord.left_boundary
    · rw [hxv]; exact data.chord.right_boundary
  have hhead_bv : C.IsBoundaryVertex (M.head data.dart) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨_, hyv⟩ | ⟨_, hyu⟩
    · rw [hyv]; exact data.chord.right_boundary
    · rw [hyu]; exact data.chord.left_boundary
  have hnbe : ¬ C.IsBoundaryEdge s(M.tail data.dart, M.head data.dart) := by
    rw [hxy_edge]; exact data.chord.not_boundary_edge
  let R := ProofsInTheBook.ZinanCh35BoundaryAssembler.BoundaryCycle.nonEdgeRuns
    C hNT.outer_simple hne htail_bv hhead_bv hnbe
  have hboundaryVertex : C.IsBoundaryVertex (M.tail d) := by
    rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq]
    exact List.mem_map_of_mem hdmem
  have hdisj : Disjoint data.side₁ data.side₂ := by
    simpa [NearTriangulation.SidesDisjoint] using
      (separates_iff_sidesDisjoint data).1 hsep
  rcases R.covering hboundaryVertex with hUV | hVU | htail | hhead
  · obtain ⟨i, hi⟩ := hUV
    have hd_eq : d = R.arcUV.arcDart i := by
      apply C.tail_injective_on_darts hNT.outer_simple hdmem (R.arcUV.boundary i)
      exact hi.symm
    let A := ProofsInTheBook.ZinanCh35Aligned.daCast
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data)
      (M.head_alpha data.dart) (M.tail_alpha data.dart)
    obtain ⟨j, hj⟩ := dartArc_dart_mem_of_same_endpoints C hNT.outer_simple A R.arcUV i
    refine ⟨Fin.cast
      (ProofsInTheBook.ZinanCh35Aligned.daCast_len
        (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data)
        (M.head_alpha data.dart) (M.tail_alpha data.dart)) j, ?_⟩
    have hcast := ProofsInTheBook.ZinanCh35Aligned.daCast_arcDart_eq
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data)
      (M.head_alpha data.dart) (M.tail_alpha data.dart) j
    exact hd_eq.trans (hj.trans hcast)
  · obtain ⟨i, hi⟩ := hVU
    have hd_eq : d = R.arcVU.arcDart i := by
      apply C.tail_injective_on_darts hNT.outer_simple hdmem (R.arcVU.boundary i)
      exact hi.symm
    have hside₂ : M.dartFace (M.α d) ∈ data.side₂ := by
      rw [hd_eq]
      exact ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.fwdRun_reverse_face_mem_side₂ data
        R.arcVU R.lenVU i
    rw [Set.disjoint_left] at hdisj
    exact False.elim (hdisj hdouter.2 hside₂)
  · refine ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx, ?_⟩
    apply C.tail_injective_on_darts hNT.outer_simple hdmem
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary _)
    rw [htail, (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).tail_firstIdx, M.head_alpha]
  · have hd_eq : d = R.arcVU.arcDart R.arcVU.firstIdx := by
      apply C.tail_injective_on_darts hNT.outer_simple hdmem (R.arcVU.boundary R.arcVU.firstIdx)
      rw [hhead, R.arcVU.tail_firstIdx]
    have hside₂ : M.dartFace (M.α d) ∈ data.side₂ := by
      rw [hd_eq]
      exact ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.fwdRun_reverse_face_mem_side₂ data
        R.arcVU R.lenVU R.arcVU.firstIdx
    rw [Set.disjoint_left] at hdisj
    exact False.elim (hdisj hdouter.2 hside₂)

/-- **The side-1 `outer_simple` keystone, UNCONDITIONAL** (canonical anchors).  Feeds the closed
`OuterTraceInjOn` into `side₁_outer_simple_canonical`.  This is exactly the `outer_simple` field
`ZinanCh35Contiguous.contiguousInterval_holds` consumes — no longer a residue. -/
theorem side₁_outer_simple_canonical_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).tail).Nodup :=
  side₁_outer_simple_canonical hNT data hsep (canonical_OuterTraceInjOn_uncond hNT data hsep)

/-- **Canonical chord-incidence non-degeneracy.**  The two chord-incidence darts consumed by
the Layer-B `outer_len` itinerary are the first and last darts of `bwdArc`; the arc has length at
least two, so tail-injectivity keeps those endpoints distinct. -/
theorem side₁ChordIncidenceNonDegenerate_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ZinanCh35Contiguous.Side₁ChordIncidenceNonDegenerate data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) := by
  classical
  intro h
  have H := canonicalBwdArcEndpointAlignment_uncond hNT data hsep
  have hfirst :
      data.sideSigma₁ (side₁Anchor₀ data hsep)
        = ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
            (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx,
          bwdArc_arcDart_notMem_keptDel₁ hNT data hsep _⟩ :=
    sideSigma₁_anchor₀_eq_bwdArc_first hNT data hsep H.ρa₀_boundary
  have hlast :
      data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
        = ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
            (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx,
          bwdArc_arcDart_notMem_keptDel₁ hNT data hsep _⟩ :=
    sideAlpha₁_anchor₁_eq_bwdArc_last hNT data hsep H.βa₁_boundary
  have htail_eq :
      M.tail ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx)
        = M.tail ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx) := by
    have hval := congrArg Subtype.val h
    rw [hfirst, hlast] at hval
    exact congrArg M.tail hval
  have hidx :
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx
        = (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx :=
    (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).tail_nodup htail_eq
  have hidx_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx : ℕ)
        = ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx : ℕ) :=
    congrArg Fin.val hidx
  have hlen_ge : 2 ≤ (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).len :=
    ProofsInTheBook.ZinanCh35ArcSide.bwdArc_len data
  have hlast_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx : ℕ)
        = (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).len - 1 := rfl
  have hfirst_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx : ℕ) = 0 := rfl
  omega

/-- Translate a side-map dart-edge equality to the corresponding unordered pair of projected
ambient endpoints.  This is the local bridge used for side-map simplicity. -/
 lemma sideMap₁_dartEdge_eq_to_M_proj_edge
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    {x y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2}
    (h : (data.sideMap₁ hsep a₀ a₁ hne).dartEdge x
        = (data.sideMap₁ hsep a₀ a₁ hne).dartEdge y) :
    s(M.tail (proj a₀ a₁ x).1,
        M.tail (proj a₀ a₁ (freshAlpha (data.sideAlpha₁ hsep) x)).1)
      =
    s(M.tail (proj a₀ a₁ y).1,
        M.tail (proj a₀ a₁ (freshAlpha (data.sideAlpha₁ hsep) y)).1) := by
  classical
  unfold CombMap.dartEdge at h
  rcases Sym2.eq_iff.1 h with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have htM := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne x y).1 ht
    have hhTail :
        (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) x)
          = (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) y) := by
      simpa [CombMap.head] using hh
    have hhM := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne
      (freshAlpha (data.sideAlpha₁ hsep) x) (freshAlpha (data.sideAlpha₁ hsep) y)).1 hhTail
    exact Sym2.eq_iff.2 (Or.inl ⟨htM, hhM⟩)
  · have htTail :
        (data.sideMap₁ hsep a₀ a₁ hne).tail x
          = (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) y) := by
      simpa [CombMap.head] using ht
    have htM := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne x
      (freshAlpha (data.sideAlpha₁ hsep) y)).1 htTail
    have hhTail :
        (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) x)
          = (data.sideMap₁ hsep a₀ a₁ hne).tail y := by
      simpa [CombMap.head] using hh
    have hhM := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne
      (freshAlpha (data.sideAlpha₁ hsep) x) y).1 hhTail
    exact Sym2.eq_iff.2 (Or.inr ⟨htM, hhM⟩)

/-- The chord dart and its reverse are not side-1 kept darts. -/
 lemma no_kept_dart_on_chord_edge
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (x : {d : D // d ∉ data.keptDel₁})
    (hxedge : M.dartEdge x.1 = M.dartEdge data.dart) : False := by
  have hchord : M.dartEdge x.1 = s(u, v) := by
    exact hxedge.trans (hNT.chordDart_edge data.chord)
  rcases data.chord_edge_darts hchord with hx | hx
  · exact x.2 (hx ▸ ProofsInTheBook.ChordFaceFinal.dart_mem_keptDel₁ data)
  · have hαdel : M.α data.dart ∈ data.keptDel₁ := by
      by_contra hnot
      exact data.alphaDart_notMem_keptSet₁ hsep ((data.mem_keptDel₁_iff _).1 hnot)
    exact x.2 (hx ▸ hαdel)

/-- **Side-map simplicity for the canonical side-1 anchors.**  The kept-kept cases inherit
simplicity from `M`; the fresh-fresh cases are the new chord edge; the mixed cases would put a kept
dart on the original chord edge, impossible because both chord darts are deleted from side 1. -/
theorem sideMap₁_isSimpleGraph_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).IsSimpleGraph := by
  classical
  let a₀ : {d : D // d ∉ data.keptDel₁} := side₁Anchor₀ data hsep
  let a₁ : {d : D // d ∉ data.keptDel₁} := side₁Anchor₁ data hsep
  let hne : a₀ ≠ a₁ := side₁Anchors_ne data hsep
  change (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph
  have ha₀ : M.tail a₀.1 = M.tail data.dart := by
    dsimp [a₀]
    exact canonicalAnchor₀_tail data hsep
  have ha₁ : M.tail a₁.1 = M.head data.dart := by
    dsimp [a₁]
    exact canonicalAnchor₁_tail data hsep
  have hαdart_del : M.α data.dart ∈ data.keptDel₁ := by
    by_contra hnot
    exact data.alphaDart_notMem_keptSet₁ hsep ((data.mem_keptDel₁_iff _).1 hnot)
  refine ⟨?_, ?_⟩
  · intro x hloop
    have htail :
        (data.sideMap₁ hsep a₀ a₁ hne).tail x
          = (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) x) := by
      simpa [CombMap.head] using hloop
    have hMtail := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne x
      (freshAlpha (data.sideAlpha₁ hsep) x)).1 htail
    cases x with
    | inl k =>
        apply hNT.simpleGraph.no_loop k.1
        simpa [freshAlpha_inl, data.sideAlpha₁_apply_coe hsep, M.tail_alpha] using hMtail
    | inr j =>
        fin_cases j
        · have huv : M.tail data.dart = M.head data.dart := by
            simpa [freshAlpha_inr, proj, ha₀, ha₁] using hMtail
          exact ProofsInTheBook.ChordSigmaContig.u_ne_v data huv
        · have hvu : M.head data.dart = M.tail data.dart := by
            simpa [freshAlpha_inr, proj, ha₀, ha₁] using hMtail
          exact ProofsInTheBook.ChordSigmaContig.u_ne_v data hvu.symm
  · intro x y hxy
    have hMedge := sideMap₁_dartEdge_eq_to_M_proj_edge hNT data hsep a₀ a₁ hne hxy
    cases x with
    | inl kx =>
        cases y with
        | inl ky =>
            have hM : M.dartEdge kx.1 = M.dartEdge ky.1 := by
              simpa [CombMap.dartEdge, freshAlpha_inl, data.sideAlpha₁_apply_coe hsep,
                M.tail_alpha] using hMedge
            have hsc : M.α.SameCycle kx.1 ky.1 := hNT.simpleGraph.no_parallel hM
            rcases (M.alpha_sameCycle_iff kx.1 ky.1).mp hsc with hsame | halpha
            · have hky : ky = kx := Subtype.ext hsame
              rw [hky]
            · have hky : ky = data.sideAlpha₁ hsep kx := by
                apply Subtype.ext
                rw [data.sideAlpha₁_apply_coe hsep]
                exact halpha
              refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₁ hsep) (Sum.inl kx) = Sum.inl ky
              rw [freshAlpha_inl, hky]
        | inr jy =>
            fin_cases jy
            · have hxedge : M.dartEdge kx.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₁_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁] using hMedge
              exact False.elim (no_kept_dart_on_chord_edge hNT data hsep kx hxedge)
            · have hxedge : M.dartEdge kx.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₁_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁,
                  Sym2.eq_swap] using hMedge
              exact False.elim (no_kept_dart_on_chord_edge hNT data hsep kx hxedge)
    | inr jx =>
        cases y with
        | inl ky =>
            fin_cases jx
            · have hyedge : M.dartEdge ky.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₁_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁,
                  Sym2.eq_swap] using hMedge.symm
              exact False.elim (no_kept_dart_on_chord_edge hNT data hsep ky hyedge)
            · have hyedge : M.dartEdge ky.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₁_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁,
                  Sym2.eq_swap] using hMedge.symm
              exact False.elim (no_kept_dart_on_chord_edge hNT data hsep ky hyedge)
        | inr jy =>
            fin_cases jx <;> fin_cases jy
            · exact Equiv.Perm.SameCycle.refl _ _
            · refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₁ hsep) (Sum.inr 0) = Sum.inr 1
              rw [freshAlpha_inr]
              rfl
            · refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₁ hsep) (Sum.inr 1) = Sum.inr 0
              rw [freshAlpha_inr]
              rfl
            · exact Equiv.Perm.SameCycle.refl _ _



/-- The side-2 `face₂` mirror of `tail_alpha_phiSq_dart`: the dart
`α (φ² (α dart))` lives at the tail vertex of `α dart`. -/
lemma tail_alpha_phiSq_alphaDart (data : hNT.ChordSplitData u v) :
    M.tail (M.α (M.φ (M.φ (M.α data.dart)))) = M.tail (M.α data.dart) := by
  have h : M.σ (M.α (M.φ (M.φ (M.α data.dart)))) = M.α data.dart := by
    obtain ⟨_, _, h20⟩ := face₂_isFaceTriangle data
    change M.φ (M.φ (M.φ (M.α data.dart))) = M.α data.dart
    exact h20
  calc
    M.tail (M.α (M.φ (M.φ (M.α data.dart))))
        = M.tail (M.σ (M.α (M.φ (M.φ (M.α data.dart))))) := (M.tail_sigma _).symm
    _ = M.tail (M.α data.dart) := by rw [h]

/-- The filtered side-2 successor of `face₂Dart₂` lands at the vertex of `α dart`,
i.e. at the chord endpoint `head dart`. -/
theorem keptPhi_face₂Dart₂_tail
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail ((keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₂ data) :
        {d : D // d ∉ data.keptDel₂}) : D)
      = M.tail (M.α data.dart) := by
  show M.tail ((data.sideSigma₂ (data.sideAlpha₂ hsep (face₂Dart₂ data)) :
      {d : D // d ∉ data.keptDel₂}) : D) = M.tail (M.α data.dart)
  rw [show data.sideSigma₂ = FilteredRotation.filteredRotation M.σ data.keptDel₂ from rfl,
    ProofsInTheBook.ChordSigmaContig.tail_filteredRotation data.keptDel₂
      (data.sideAlpha₂ hsep (face₂Dart₂ data))]
  rw [sideAlpha₂_apply_coe]
  show M.tail (M.α (M.φ (M.φ (M.α data.dart)))) = M.tail (M.α data.dart)
  exact tail_alpha_phiSq_alphaDart hNT data

/-- `face₂Dart₁ = φ (α dart)` lives at the head vertex of `α dart`,
i.e. at the chord endpoint `tail dart`. -/
theorem face₂Dart₁_tail (data : hNT.ChordSplitData u v) :
    M.tail ((face₂Dart₁ data : {d : D // d ∉ data.keptDel₂}) : D)
      = M.head (M.α data.dart) := by
  show M.tail (M.φ (M.α data.dart)) = M.head (M.α data.dart)
  exact M.tail_phi (M.α data.dart)

/-- The canonical side-2 anchor `a₀` sits at the chord endpoint `head dart`. -/
theorem canonicalSide₂Anchor₀_tail
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail (side₂Anchor₀ data hsep).1 = M.head data.dart := by
  have hfix : M.tail (data.sideSigma₂ (side₂Anchor₀ data hsep) : D)
      = M.tail (side₂Anchor₀ data hsep).1 := by
    rw [show data.sideSigma₂ = FilteredRotation.filteredRotation M.σ data.keptDel₂ from rfl,
      ProofsInTheBook.ChordSigmaContig.tail_filteredRotation data.keptDel₂
        (side₂Anchor₀ data hsep)]
  rw [← hfix, sideSigma₂_side₂Anchor₀ data hsep, keptPhi_face₂Dart₂_tail hNT data hsep,
    M.tail_alpha]

/-- The canonical side-2 anchor `a₁` sits at the chord endpoint `tail dart`. -/
theorem canonicalSide₂Anchor₁_tail
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail (side₂Anchor₁ data hsep).1 = M.tail data.dart := by
  have hfix : M.tail (data.sideSigma₂ (side₂Anchor₁ data hsep) : D)
      = M.tail (side₂Anchor₁ data hsep).1 := by
    rw [show data.sideSigma₂ = FilteredRotation.filteredRotation M.σ data.keptDel₂ from rfl,
      ProofsInTheBook.ChordSigmaContig.tail_filteredRotation data.keptDel₂
        (side₂Anchor₁ data hsep)]
  rw [← hfix, sideSigma₂_side₂Anchor₁ data hsep, face₂Dart₁_tail hNT data, M.head_alpha]

/-- The canonical side-2 anchors are distinct. -/
theorem side₂Anchors_ne (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    side₂Anchor₀ data hsep ≠ side₂Anchor₁ data hsep := by
  intro h
  have htail : M.tail (side₂Anchor₀ data hsep).1 = M.tail (side₂Anchor₁ data hsep).1 :=
    congrArg (fun x : {d : D // d ∉ data.keptDel₂} => M.tail x.1) h
  rw [canonicalSide₂Anchor₀_tail hNT data hsep, canonicalSide₂Anchor₁_tail hNT data hsep] at htail
  exact ProofsInTheBook.ChordSigmaContig.u_ne_v data htail.symm



/-- Side-2 mirror of `sideMap₁_tail_eq_iff_M_tail_proj`. -/
lemma sideMap₂_tail_eq_iff_M_tail_proj
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (x y : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) :
    (data.sideMap₂ hsep a₀ a₁ hne).tail x = (data.sideMap₂ hsep a₀ a₁ hne).tail y
      ↔ M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 := by
  rw [show data.sideMap₂ hsep a₀ a₁ hne
        = freshMap (data.sideAlpha₂ hsep) data.sideSigma₂
            (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) a₀ a₁ hne from rfl]
  rw [freshMap_tail_eq_iff_rho_sameCycle (data.sideAlpha₂ hsep) data.sideSigma₂
        (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) hne x y]
  rw [show data.sideSigma₂ = FilteredRotation.filteredRotation M.σ data.keptDel₂ from rfl]
  rw [filteredRotation_sameCycle_iff M.σ data.keptDel₂ (proj a₀ a₁ x) (proj a₀ a₁ y)]
  rw [tail_eq_iff_sigma_sameCycle]

 lemma sideMap₂_dartEdge_eq_to_M_proj_edge
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    {x y : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2}
    (h : (data.sideMap₂ hsep a₀ a₁ hne).dartEdge x
        = (data.sideMap₂ hsep a₀ a₁ hne).dartEdge y) :
    s(M.tail (proj a₀ a₁ x).1,
        M.tail (proj a₀ a₁ (freshAlpha (data.sideAlpha₂ hsep) x)).1)
      =
    s(M.tail (proj a₀ a₁ y).1,
        M.tail (proj a₀ a₁ (freshAlpha (data.sideAlpha₂ hsep) y)).1) := by
  classical
  unfold CombMap.dartEdge at h
  rcases Sym2.eq_iff.1 h with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have htM := (sideMap₂_tail_eq_iff_M_tail_proj hNT data hsep a₀ a₁ hne x y).1 ht
    have hhTail :
        (data.sideMap₂ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₂ hsep) x)
          = (data.sideMap₂ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₂ hsep) y) := by
      simpa [CombMap.head] using hh
    have hhM := (sideMap₂_tail_eq_iff_M_tail_proj hNT data hsep a₀ a₁ hne
      (freshAlpha (data.sideAlpha₂ hsep) x) (freshAlpha (data.sideAlpha₂ hsep) y)).1 hhTail
    exact Sym2.eq_iff.2 (Or.inl ⟨htM, hhM⟩)
  · have htTail :
        (data.sideMap₂ hsep a₀ a₁ hne).tail x
          = (data.sideMap₂ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₂ hsep) y) := by
      simpa [CombMap.head] using ht
    have htM := (sideMap₂_tail_eq_iff_M_tail_proj hNT data hsep a₀ a₁ hne x
      (freshAlpha (data.sideAlpha₂ hsep) y)).1 htTail
    have hhTail :
        (data.sideMap₂ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₂ hsep) x)
          = (data.sideMap₂ hsep a₀ a₁ hne).tail y := by
      simpa [CombMap.head] using hh
    have hhM := (sideMap₂_tail_eq_iff_M_tail_proj hNT data hsep a₀ a₁ hne
      (freshAlpha (data.sideAlpha₂ hsep) x) y).1 hhTail
    exact Sym2.eq_iff.2 (Or.inr ⟨htM, hhM⟩)

/-- The chord dart and its reverse are not side-2 kept darts. -/
 lemma no_kept_dart_on_chord_edge₂
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (x : {d : D // d ∉ data.keptDel₂})
    (hxedge : M.dartEdge x.1 = M.dartEdge data.dart) : False := by
  have hchord : M.dartEdge x.1 = s(u, v) := by
    exact hxedge.trans (hNT.chordDart_edge data.chord)
  rcases data.chord_edge_darts hchord with hx | hx
  · have hdart_del : data.dart ∈ data.keptDel₂ := by
      by_contra hnot
      exact data.dart_notMem_keptSet₂ hsep ((data.mem_keptDel₂_iff _).1 hnot)
    exact x.2 (hx ▸ hdart_del)
  · have hαdart_del : M.α data.dart ∈ data.keptDel₂ := by
      by_contra hnot
      rw [data.mem_keptDel₂_iff] at hnot
      exact hnot.2 rfl
    exact x.2 (hx ▸ hαdart_del)



/-- **Side-map simplicity for the swapped canonical side-2 anchors.** -/
theorem sideMap₂_isSimpleGraph_canonical_swapped
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).IsSimpleGraph := by
  classical
  let a₀ : {d : D // d ∉ data.keptDel₂} := side₂Anchor₁ data hsep
  let a₁ : {d : D // d ∉ data.keptDel₂} := side₂Anchor₀ data hsep
  let hne : a₀ ≠ a₁ := (side₂Anchors_ne hNT data hsep).symm
  change (data.sideMap₂ hsep a₀ a₁ hne).IsSimpleGraph
  have ha₀ : M.tail a₀.1 = M.tail data.dart := by
    dsimp [a₀]
    exact canonicalSide₂Anchor₁_tail hNT data hsep
  have ha₁ : M.tail a₁.1 = M.head data.dart := by
    dsimp [a₁]
    exact canonicalSide₂Anchor₀_tail hNT data hsep
  refine ⟨?_, ?_⟩
  · intro x hloop
    have htail :
        (data.sideMap₂ hsep a₀ a₁ hne).tail x
          = (data.sideMap₂ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₂ hsep) x) := by
      simpa [CombMap.head] using hloop
    have hMtail := (sideMap₂_tail_eq_iff_M_tail_proj hNT data hsep a₀ a₁ hne x
      (freshAlpha (data.sideAlpha₂ hsep) x)).1 htail
    cases x with
    | inl k =>
        apply hNT.simpleGraph.no_loop k.1
        simpa [freshAlpha_inl, data.sideAlpha₂_apply_coe hsep, M.tail_alpha] using hMtail
    | inr j =>
        fin_cases j
        · have huv : M.tail data.dart = M.head data.dart := by
            simpa [freshAlpha_inr, proj, ha₀, ha₁] using hMtail
          exact ProofsInTheBook.ChordSigmaContig.u_ne_v data huv
        · have hvu : M.head data.dart = M.tail data.dart := by
            simpa [freshAlpha_inr, proj, ha₀, ha₁] using hMtail
          exact ProofsInTheBook.ChordSigmaContig.u_ne_v data hvu.symm
  · intro x y hxy
    have hMedge := sideMap₂_dartEdge_eq_to_M_proj_edge hNT data hsep a₀ a₁ hne hxy
    cases x with
    | inl kx =>
        cases y with
        | inl ky =>
            have hM : M.dartEdge kx.1 = M.dartEdge ky.1 := by
              simpa [CombMap.dartEdge, freshAlpha_inl, data.sideAlpha₂_apply_coe hsep,
                M.tail_alpha] using hMedge
            have hsc : M.α.SameCycle kx.1 ky.1 := hNT.simpleGraph.no_parallel hM
            rcases (M.alpha_sameCycle_iff kx.1 ky.1).mp hsc with hsame | halpha
            · have hky : ky = kx := Subtype.ext hsame
              rw [hky]
            · have hky : ky = data.sideAlpha₂ hsep kx := by
                apply Subtype.ext
                rw [data.sideAlpha₂_apply_coe hsep]
                exact halpha
              refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₂ hsep) (Sum.inl kx) = Sum.inl ky
              rw [freshAlpha_inl, hky]
        | inr jy =>
            fin_cases jy
            · have hxedge : M.dartEdge kx.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₂_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁] using hMedge
              exact False.elim (no_kept_dart_on_chord_edge₂ hNT data hsep kx hxedge)
            · have hxedge : M.dartEdge kx.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₂_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁,
                  Sym2.eq_swap] using hMedge
              exact False.elim (no_kept_dart_on_chord_edge₂ hNT data hsep kx hxedge)
    | inr jx =>
        cases y with
        | inl ky =>
            fin_cases jx
            · have hyedge : M.dartEdge ky.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₂_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁] using hMedge.symm
              exact False.elim (no_kept_dart_on_chord_edge₂ hNT data hsep ky hyedge)
            · have hyedge : M.dartEdge ky.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₂_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁,
                  Sym2.eq_swap] using hMedge.symm
              exact False.elim (no_kept_dart_on_chord_edge₂ hNT data hsep ky hyedge)
        | inr jy =>
            fin_cases jx <;> fin_cases jy
            · exact Equiv.Perm.SameCycle.refl _ _
            · refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₂ hsep) (Sum.inr 0) = Sum.inr 1
              rw [freshAlpha_inr]
              rfl
            · refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₂ hsep) (Sum.inr 1) = Sum.inr 0
              rw [freshAlpha_inr]
              rfl
            · exact Equiv.Perm.SameCycle.refl _ _

/-- **`hArcKept` for the side-2 arc `fwdArc`, UNCONDITIONAL.**  Each `fwdArc` dart's
`α`-reverse face is in `side₂`, so it lies in `outerArc₂ ⊆ keptSet₂`; it is not the side-2 seam
dart `α dart` because its edge is not the chord. -/
lemma fwdArc_arcDart_notMem_keptDel₂
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (i : Fin (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).len) :
    (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i ∉ data.keptDel₂ := by
  classical
  have hfmem : (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i ∈ hNT.outerCycle.darts :=
    (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).boundary i
  have hface : M.dartFace ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i)
      = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff _).mp hfmem
  have hconf : M.dartFace (M.α ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i))
      ∈ data.side₂ :=
    ProofsInTheBook.ZinanCh35ArcSide.fwdArc_reverse_face_mem_side₂ data i
  have hne : (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i ≠ M.α data.dart := by
    intro he
    apply ProofsInTheBook.ZinanCh35ArcSide.fwdArc_dartEdge_ne_chord data i
    rw [he, M.dartEdge_alpha]
    exact hNT.chordDart_edge data.chord
  rw [data.mem_keptDel₂_iff]
  exact ⟨Or.inr ⟨hface, hconf⟩, by simpa using hne⟩

/-- `ρ₂ a₀` is the first dart of the canonical side-2 forward boundary arc. -/
lemma sideSigma₂_anchor₀_eq_fwdArc_first
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hρa₀ : ((data.sideSigma₂ (side₂Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideSigma₂ (side₂Anchor₀ data hsep)
      = ⟨(ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).firstIdx,
          fwdArc_arcDart_notMem_keptDel₂ hNT data hsep _⟩ := by
  apply Subtype.ext
  apply hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hρa₀
    ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).boundary _)
  have hL : M.tail ((data.sideSigma₂ (side₂Anchor₀ data hsep)) : D) = M.head data.dart := by
    rw [show data.sideSigma₂ = FilteredRotation.filteredRotation M.σ data.keptDel₂ from rfl,
      ProofsInTheBook.ChordSigmaContig.tail_filteredRotation data.keptDel₂ (side₂Anchor₀ data hsep)]
    exact canonicalSide₂Anchor₀_tail hNT data hsep
  have hR : M.tail ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart
      (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).firstIdx) = M.head data.dart :=
    (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).tail_firstIdx
  rw [hL, hR]

/-- `β₂ a₁` is the last dart of the canonical side-2 forward boundary arc. -/
lemma sideAlpha₂_anchor₁_eq_fwdArc_last
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hβa₁ : ((data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)
      = ⟨(ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).lastIdx,
          fwdArc_arcDart_notMem_keptDel₂ hNT data hsep _⟩ := by
  apply Subtype.ext
  apply head_injective_on_darts hNT.outerCycle hNT.outer_simple hβa₁
    ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).boundary _)
  have hL : M.head ((data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)) : D) = M.tail data.dart := by
    have hαcoe : ((data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)) : D)
        = M.α (side₂Anchor₁ data hsep).1 := by
      simpa using data.sideAlpha₂_apply_coe hsep (side₂Anchor₁ data hsep)
    rw [hαcoe, M.head_alpha, canonicalSide₂Anchor₁_tail hNT data hsep]
  have hR : M.head ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart
      (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).lastIdx) = M.tail data.dart :=
    (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).head_lastIdx
  rw [hL, hR]

/-- **Canonical side-2 chord-incidence non-degeneracy.** -/
theorem side₂ChordIncidenceNonDegenerate_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hρa₀ : ((data.sideSigma₂ (side₂Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts)
    (hβa₁ : ((data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    ProofsInTheBook.ZinanCh35Contiguous.Side₂ChordIncidenceNonDegenerate data hsep
      (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep) := by
  classical
  intro h
  have hfirst :
      data.sideSigma₂ (side₂Anchor₀ data hsep)
        = ⟨(ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart
            (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).firstIdx,
          fwdArc_arcDart_notMem_keptDel₂ hNT data hsep _⟩ :=
    sideSigma₂_anchor₀_eq_fwdArc_first hNT data hsep hρa₀
  have hlast :
      data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)
        = ⟨(ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart
            (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).lastIdx,
          fwdArc_arcDart_notMem_keptDel₂ hNT data hsep _⟩ :=
    sideAlpha₂_anchor₁_eq_fwdArc_last hNT data hsep hβa₁
  have htail_eq :
      M.tail ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).firstIdx)
        = M.tail ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).lastIdx) := by
    have hval := congrArg Subtype.val h
    rw [hfirst, hlast] at hval
    exact congrArg M.tail hval
  have hidx :
      (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).firstIdx
        = (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).lastIdx :=
    (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).tail_nodup htail_eq
  have hidx_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).firstIdx : ℕ)
        = ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).lastIdx : ℕ) :=
    congrArg Fin.val hidx
  have hlen_ge : 2 ≤ (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).len :=
    ProofsInTheBook.ZinanCh35ArcSide.fwdArc_len data
  have hlast_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).lastIdx : ℕ)
        = (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).len - 1 := rfl
  have hfirst_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).firstIdx : ℕ) = 0 := rfl
  omega

/-- **The canonical side-2 chord predecessors are not `tracePhi`-SameCycle.** -/
theorem side₂_chordPred_notSameCycle_canonical
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ¬ (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₂ hsep) (side₂Anchor₀ data hsep))
      ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) := by
  classical
  set β := data.sideAlpha₂ hsep with hβ
  set ρ := data.sideSigma₂ with hρ
  set a₀ := side₂Anchor₀ data hsep with ha₀
  set a₁ := side₂Anchor₁ data hsep with ha₁
  have hshare : (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁) := by
    have h := side₂AnchorsShareFace_canonical data hsep
    simpa [hβ, hρ, ha₀, ha₁, ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace, keptPhi]
      using h
  have hne : ρ a₀ ≠ ρ a₁ := ρa₀_ne_ρa₁ ρ (side₂Anchors_ne hNT data hsep)
  have hsplit : ¬ (tracePhi β ρ a₀ a₁).SameCycle (ρ a₀) (ρ a₁) := by
    rw [show tracePhi β ρ a₀ a₁ = Equiv.swap (ρ a₀) (ρ a₁) * keptPhi β ρ from rfl]
    exact notSameCycle_swap_mul_left_of_sameCycle (keptPhi β ρ) hne hshare
  intro hsc
  apply hsplit
  have hb0 : tracePhi β ρ a₀ a₁ (β a₀) = ρ a₁ :=
    tracePhi_b0 β ρ (data.sideAlpha₂_involutive hsep) a₀ a₁
  have hb1 : tracePhi β ρ a₀ a₁ (β a₁) = ρ a₀ :=
    tracePhi_b1 β ρ (data.sideAlpha₂_involutive hsep) a₀ a₁
  have hstep : (tracePhi β ρ a₀ a₁).SameCycle
      (tracePhi β ρ a₀ a₁ (β a₀)) (tracePhi β ρ a₀ a₁ (β a₁)) :=
    hsc.apply_left.apply_right
  rw [hb0, hb1] at hstep
  exact hstep.symm

/-- Kept side-2 copy of an arc dart. -/
def arcK₂ (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂) (i : Fin A.len) :
    {d : D // d ∉ data.keptDel₂} :=
  ⟨A.arcDart i, hArcKept i⟩

/-- The side-2 kept face permutation walks one step along a kept boundary arc. -/
lemma sideSigma₂_alpha_arcDart_eq_next
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂)
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    data.sideSigma₂ (data.sideAlpha₂ hsep (arcK₂ hNT data A hArcKept i))
      = arcK₂ hNT data A hArcKept ⟨i + 1, hi⟩ := by
  classical
  have hphi : M.φ (A.arcDart i) = A.arcDart ⟨i + 1, hi⟩ :=
    phi_eq_of_boundary_chain hNT.outerCycle hNT.outer_simple
      (A.boundary i) (A.boundary ⟨i + 1, hi⟩) (A.chain i hi)
  have hαcoe : ((data.sideAlpha₂ hsep (arcK₂ hNT data A hArcKept i)) : D)
      = M.α (A.arcDart i) := by
    simpa [arcK₂] using data.sideAlpha₂_apply_coe hsep (arcK₂ hNT data A hArcKept i)
  have hσnext : M.σ ((data.sideAlpha₂ hsep (arcK₂ hNT data A hArcKept i)) : D)
      = A.arcDart ⟨i + 1, hi⟩ := by
    rw [hαcoe]; exact hphi
  have hσ_kept : M.σ ((data.sideAlpha₂ hsep (arcK₂ hNT data A hArcKept i)) : D)
      ∉ data.keptDel₂ := by
    rw [hσnext]; exact hArcKept ⟨i + 1, hi⟩
  apply Subtype.ext
  rw [show data.sideSigma₂ = FilteredRotation.filteredRotation M.σ data.keptDel₂ from rfl,
    FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₂ _ hσ_kept]
  exact hσnext

/-- `arcK₂` is injective along a dart arc. -/
lemma arcK₂_injective (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂)
    {i j : Fin A.len} (h : arcK₂ hNT data A hArcKept i = arcK₂ hNT data A hArcKept j) :
    i = j := by
  apply A.tail_nodup
  show M.tail (A.arcDart i) = M.tail (A.arcDart j)
  have hd : A.arcDart i = A.arcDart j := by
    have := congrArg Subtype.val h; simpa [arcK₂] using this
  rw [hd]





/-- Side-2 `tracePhi` orbit through `β₂ a₁` is exactly the kept copies of `A`. -/
structure CanonicalTracePhiArc₂
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂) : Prop where
  mem_iff : ∀ k : {d : D // d ∉ data.keptDel₂},
    (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k
    ↔ ∃ i : Fin A.len, k = ⟨A.arcDart i, hArcKept i⟩









/-- Side-2 `tracePhi` walks one step along the arc. -/
lemma tracePhi₂_arc_step
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂)
    (hlast : data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)
      = arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
    (hnot_beta_a₀ : ∀ i : Fin A.len,
      arcK₂ hNT data A hArcKept i ≠ data.sideAlpha₂ hsep (side₂Anchor₀ data hsep))
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))
        (arcK₂ hNT data A hArcKept i)
      = arcK₂ hNT data A hArcKept ⟨i + 1, hi⟩ := by
  classical
  have hβinv : data.sideAlpha₂ hsep * data.sideAlpha₂ hsep = 1 := data.sideAlpha₂_involutive hsep
  have hinv2 : ∀ x, data.sideAlpha₂ hsep (data.sideAlpha₂ hsep x) = x := by
    intro x; rw [← Equiv.Perm.mul_apply, hβinv, Equiv.Perm.one_apply]
  have hnot0 : data.sideAlpha₂ hsep (arcK₂ hNT data A hArcKept i) ≠ side₂Anchor₀ data hsep := by
    intro h
    apply hnot_beta_a₀ i
    have h2 := congrArg (data.sideAlpha₂ hsep) h
    rw [hinv2] at h2
    exact h2
  have hnot1 : data.sideAlpha₂ hsep (arcK₂ hNT data A hArcKept i) ≠ side₂Anchor₁ data hsep := by
    intro h
    have h2 := congrArg (data.sideAlpha₂ hsep) h
    rw [hinv2] at h2
    rw [hlast] at h2
    have hieq : i = (⟨A.len - 1, by have := A.len_pos; omega⟩ : Fin A.len) :=
      arcK₂_injective hNT data A hArcKept h2
    have hi2 : (i : ℕ) = A.len - 1 := by rw [hieq]
    omega
  rw [tracePhi_other (data.sideAlpha₂ hsep) data.sideSigma₂ (side₂Anchor₀ data hsep)
    (side₂Anchor₁ data hsep) hnot0 hnot1]
  exact sideSigma₂_alpha_arcDart_eq_next hNT data hsep A hArcKept i hi

/-- Side-2 `tracePhi` wraps from the last arc dart back to the first. -/
lemma tracePhi₂_arc_wrap
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂)
    (hfirst : data.sideSigma₂ (side₂Anchor₀ data hsep)
      = arcK₂ hNT data A hArcKept ⟨0, A.len_pos⟩)
    (hlast : data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)
      = arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩) :
    (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))
        (arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK₂ hNT data A hArcKept ⟨0, A.len_pos⟩ := by
  rw [← hlast, tracePhi_b1 (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)]
  exact hfirst

lemma tracePhi₂_iterate_last_mem_arc
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂)
    (hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))
          (arcK₂ hNT data A hArcKept i) = arcK₂ hNT data A hArcKept ⟨i + 1, hi⟩)
    (hwrap : (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))
        (arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK₂ hNT data A hArcKept ⟨0, A.len_pos⟩)
    (n : ℕ) :
    ∃ i : Fin A.len,
      (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))^[n]
        (arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
        = arcK₂ hNT data A hArcKept i := by
  classical
  induction n with
  | zero => exact ⟨⟨A.len - 1, by have := A.len_pos; omega⟩, rfl⟩
  | succ n ih =>
      rcases ih with ⟨i, hi_eq⟩
      rw [Function.iterate_succ_apply', hi_eq]
      by_cases hlt : (i : ℕ) + 1 < A.len
      · exact ⟨⟨i + 1, hlt⟩, hstep i hlt⟩
      · have hi_last : i = (⟨A.len - 1, by have := A.len_pos; omega⟩ : Fin A.len) := by
          apply Fin.ext
          show (i : ℕ) = A.len - 1
          have h1 := i.isLt
          have h2 : ¬ ((i : ℕ) + 1 < A.len) := hlt
          omega
        rw [hi_last]; exact ⟨⟨0, A.len_pos⟩, hwrap⟩

lemma tracePhi₂_sameCycle_last_arc
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂)
    (hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))
          (arcK₂ hNT data A hArcKept i) = arcK₂ hNT data A hArcKept ⟨i + 1, hi⟩)
    (hwrap : (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))
        (arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK₂ hNT data A hArcKept ⟨0, A.len_pos⟩)
    (i : Fin A.len) :
    (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
      (arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      (arcK₂ hNT data A hArcKept i) := by
  classical
  set τ := tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
    (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep) with hτdef
  have hlast_first : τ.SameCycle (arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      (arcK₂ hNT data A hArcKept ⟨0, A.len_pos⟩) := ⟨1, by rw [zpow_one]; exact hwrap⟩
  have hfrom_first : ∀ n : ℕ, ∀ hn : n < A.len,
      τ.SameCycle (arcK₂ hNT data A hArcKept ⟨0, A.len_pos⟩) (arcK₂ hNT data A hArcKept ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro hn; exact Equiv.Perm.SameCycle.refl _ _
    | succ m ih =>
        intro hn
        have hm : m < A.len := by omega
        have hmstep : (m : ℕ) + 1 < A.len := by simpa using hn
        refine (ih hm).trans ?_
        refine ⟨1, ?_⟩
        rw [zpow_one]
        have := hstep ⟨m, hm⟩ (by simpa using hmstep)
        simpa using this
  exact hlast_first.trans (hfrom_first i.1 i.2)

/-- Side-2 `CanonicalTracePhiArc₂` from endpoint/step data. -/
theorem canonicalTracePhiArc₂_of_steps
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂)
    (hfirst : data.sideSigma₂ (side₂Anchor₀ data hsep)
      = arcK₂ hNT data A hArcKept ⟨0, A.len_pos⟩)
    (hlast : data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)
      = arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
    (hnot_beta_a₀ : ∀ i : Fin A.len,
      arcK₂ hNT data A hArcKept i ≠ data.sideAlpha₂ hsep (side₂Anchor₀ data hsep)) :
    CanonicalTracePhiArc₂ hNT data hsep A hArcKept := by
  classical
  have hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))
          (arcK₂ hNT data A hArcKept i) = arcK₂ hNT data A hArcKept ⟨i + 1, hi⟩ :=
    fun i hi => tracePhi₂_arc_step hNT data hsep A hArcKept hlast hnot_beta_a₀ i hi
  have hwrap := tracePhi₂_arc_wrap hNT data hsep A hArcKept hfirst hlast
  refine ⟨fun k => ?_⟩
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := hk.exists_nat_pow_eq
    have hn' : (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))^[n]
        (arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩) = k := by
      rw [Equiv.Perm.coe_pow] at hn
      rw [← hlast]; exact hn
    obtain ⟨i, hi⟩ := tracePhi₂_iterate_last_mem_arc hNT data hsep A hArcKept hstep hwrap n
    exact ⟨i, hn'.symm.trans hi⟩
  · rintro ⟨i, rfl⟩
    have hsc := tracePhi₂_sameCycle_last_arc hNT data hsep A hArcKept hstep hwrap i
    rw [hlast]; exact hsc

/-- For side 2, `β₂ a₀ = face₂Dart₂`, so no outer boundary arc dart can equal it. -/
lemma hnot_beta₂_a₀_canonical
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂)
    (i : Fin A.len) :
    arcK₂ hNT data A hArcKept i ≠ data.sideAlpha₂ hsep (side₂Anchor₀ data hsep) := by
  intro h
  have ha₀ : side₂Anchor₀ data hsep = data.sideAlpha₂ hsep (face₂Dart₂ data) := by
    apply data.sideSigma₂.injective
    rw [sideSigma₂_side₂Anchor₀ data hsep]
    rfl
  have hinv2 : ∀ x, data.sideAlpha₂ hsep (data.sideAlpha₂ hsep x) = x := by
    intro x
    rw [← Equiv.Perm.mul_apply, data.sideAlpha₂_involutive hsep, Equiv.Perm.one_apply]
  have hβa₀ : data.sideAlpha₂ hsep (side₂Anchor₀ data hsep) = face₂Dart₂ data := by
    rw [ha₀]; exact hinv2 _
  have houter : M.dartFace ((data.sideAlpha₂ hsep (side₂Anchor₀ data hsep)) : D)
      = hNT.outerFace := by
    rw [← congrArg Subtype.val h]
    exact (hNT.outerCycle.mem_darts_iff _).mp (A.boundary i)
  have hinner : M.dartFace ((data.sideAlpha₂ hsep (side₂Anchor₀ data hsep)) : D)
      = data.face₂ := by
    rw [hβa₀]
    show M.dartFace (M.φ (M.φ (M.α data.dart))) = M.dartFace (M.α data.dart)
    rw [M.dartFace_phi, M.dartFace_phi]
  exact data.face₂_not_outer (hinner.symm.trans houter)

/-- Side-2 `tracePhi` orbit ↔ canonical `fwdArc`, under the two endpoint boundary facts. -/
theorem canonicalTracePhiArc₂_fwdArc_of_alignment
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hρa₀ : ((data.sideSigma₂ (side₂Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts)
    (hβa₁ : ((data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    CanonicalTracePhiArc₂ hNT data hsep
      (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data)
      (fun i => fwdArc_arcDart_notMem_keptDel₂ hNT data hsep i) := by
  classical
  set A := ProofsInTheBook.ZinanCh35ArcSide.fwdArc data
  set hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂ :=
    fun i => fwdArc_arcDart_notMem_keptDel₂ hNT data hsep i
  have hfirst :
      data.sideSigma₂ (side₂Anchor₀ data hsep) =
        arcK₂ hNT data A hArcKept ⟨0, A.len_pos⟩ := by
    simpa [A, hArcKept, arcK₂] using
      sideSigma₂_anchor₀_eq_fwdArc_first hNT data hsep hρa₀
  have hlast :
      data.sideAlpha₂ hsep (side₂Anchor₁ data hsep) =
        arcK₂ hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩ := by
    simpa [A, hArcKept, arcK₂, DartArc.lastIdx] using
      sideAlpha₂_anchor₁_eq_fwdArc_last hNT data hsep hβa₁
  have hnot : ∀ i : Fin A.len,
      arcK₂ hNT data A hArcKept i ≠ data.sideAlpha₂ hsep (side₂Anchor₀ data hsep) :=
    fun i => hnot_beta₂_a₀_canonical hNT data hsep A hArcKept i
  exact canonicalTracePhiArc₂_of_steps hNT data hsep A hArcKept hfirst hlast hnot





/-- Boundary membership of a side-2 kept dart from `dartFace ∉ side₂`. -/
lemma kept_mem_outerCycle_of_face_not_side₂
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂})
    (hface : M.dartFace (k : D) ∉ data.side₂) :
    (k : D) ∈ hNT.outerCycle.darts := by
  classical
  have hkept : (k : D) ∈ data.keptSet₂ := (data.mem_keptDel₂_iff _).1 k.2
  have hmem : (k : D) ∈ data.sideDarts₂ ∪ data.outerArc₂ := hkept.1
  rcases hmem with hsd | hoa
  · exact absurd hsd hface
  · exact (hNT.outerCycle.mem_darts_iff _).2 hoa.1

 lemma keptSet₂_of_side₂_ne_alphaDart
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) {d : D}
    (hside : M.dartFace d ∈ data.side₂) (hne : d ≠ M.α data.dart) :
    d ∈ data.keptSet₂ := by
  exact ⟨Or.inl hside, by simpa using hne⟩

/-- The first `σ` step from `sideAlpha₂ face₂Dart₂` hits the deleted side-2 seam `α dart`. -/
 lemma sideSigma₂_sideAlpha₂_firstOutside_ge_two
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    2 ≤ Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₂
      (data.sideAlpha₂ hsep (face₂Dart₂ data)) := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₂
      (data.sideAlpha₂ hsep (face₂Dart₂ data)) :=
    Equiv.Perm.DeleteSet.firstOutside_pos M.σ data.keptDel₂ _
  have heq1 : Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₂
      (data.sideAlpha₂ hsep (face₂Dart₂ data)) = 1 := by omega
  have hnot := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ data.keptDel₂
    (data.sideAlpha₂ hsep (face₂Dart₂ data))
  rw [heq1, pow_one] at hnot
  have hstep : M.σ ((data.sideAlpha₂ hsep (face₂Dart₂ data)) : D) = M.α data.dart := by
    rw [data.sideAlpha₂_apply_coe hsep]
    obtain ⟨_, _, h20⟩ := face₂_isFaceTriangle data
    change M.φ (M.φ (M.φ (M.α data.dart))) = M.α data.dart
    exact h20
  have hdeleted : M.α data.dart ∈ data.keptDel₂ := by
    by_contra hnotdel
    rw [data.mem_keptDel₂_iff] at hnotdel
    exact hnotdel.2 rfl
  exact hnot (by rwa [hstep])

/-- The first inverse-`σ` step from `face₂Dart₁` is the deleted chord dart `dart`. -/
 lemma face₂Dart₁_inv_firstOutside_ge_two
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    2 ≤ Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₂ (face₂Dart₁ data) := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₂
      (face₂Dart₁ data) :=
    Equiv.Perm.DeleteSet.firstOutside_pos M.σ⁻¹ data.keptDel₂ _
  have heq1 : Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₂
      (face₂Dart₁ data) = 1 := by omega
  have hnot := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ⁻¹ data.keptDel₂
    (face₂Dart₁ data)
  rw [heq1, pow_one] at hnot
  have hstep : M.σ⁻¹ ((face₂Dart₁ data : {d : D // d ∉ data.keptDel₂}) : D)
      = data.dart := by
    show M.σ⁻¹ (M.φ (M.α data.dart)) = data.dart
    apply M.σ.injective
    calc
      M.σ (M.σ⁻¹ (M.φ (M.α data.dart))) = M.φ (M.α data.dart) :=
        Equiv.apply_symm_apply M.σ (M.φ (M.α data.dart))
      _ = M.σ data.dart := by
        change (M.σ * M.α) (M.α data.dart) = M.σ data.dart
        rw [Equiv.Perm.mul_apply, M.alpha_alpha]
  have hdeleted : data.dart ∈ data.keptDel₂ := by
    by_contra hnotdel
    exact data.dart_notMem_keptSet₂ hsep ((data.mem_keptDel₂_iff _).1 hnotdel)
  exact hnot (by rwa [hstep])

/-- First side-2 endpoint face fact: the kept `σ`-successor of `a₀` is not a side-2 dart. -/
theorem face_ρ₂a₀_not_side₂
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.dartFace ((data.sideSigma₂ (side₂Anchor₀ data hsep)) : D) ∉ data.side₂ := by
  classical
  intro htarget
  set x : {d : D // d ∉ data.keptDel₂} :=
    data.sideAlpha₂ hsep (face₂Dart₂ data) with hx
  set n := Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₂ x with hn
  set p : D := (M.σ ^ (n - 1)) x.1 with hp
  have hn_ge : 2 ≤ n := by
    rw [hn, hx]
    exact sideSigma₂_sideAlpha₂_firstOutside_ge_two hNT data hsep
  have hp_deleted : p ∈ data.keptDel₂ := by
    by_contra hp_not
    have hmin := Equiv.Perm.DeleteSet.firstOutside_min M.σ data.keptDel₂ x
      (m := n - 1) (by rw [hn]; omega)
    exact hmin ⟨by omega, by simpa [p] using hp_not⟩
  have htarget_coe :
      ((data.sideSigma₂ (side₂Anchor₀ data hsep)) : D) = (M.σ ^ n) x.1 := by
    rw [sideSigma₂_side₂Anchor₀ data hsep]
    change ((data.sideSigma₂ (data.sideAlpha₂ hsep (face₂Dart₂ data))) : D)
        = (M.σ ^ n) x.1
    rw [show data.sideSigma₂ = FilteredRotation.filteredRotation M.σ data.keptDel₂ from rfl]
    rw [FilteredRotation.filteredRotation_apply_coe]
  have htarget_side_pow : M.dartFace ((M.σ ^ n) x.1) ∈ data.side₂ := by
    rw [htarget_coe] at htarget
    exact htarget
  have hσp : M.σ p = (M.σ ^ n) x.1 := by
    rw [hp]
    have hs : n - 1 + 1 = n := by omega
    rw [← hs, pow_succ']
    rfl
  have hαp_side : M.dartFace (M.α p) ∈ data.side₂ := by
    rw [← ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M) p]
    rw [hσp]
    exact htarget_side_pow
  have hp_ne_alpha_dart : p ≠ M.α data.dart := by
    intro hpα
    have hface₁_side : data.face₁ ∈ data.side₂ := by
      have : M.dartFace (M.α p) ∈ data.side₂ := hαp_side
      rw [hpα, M.alpha_alpha] at this
      simpa [ChordSplitData.face₁] using this
    exact data.separates_symm hsep hface₁_side
  have hx_coe : (x : D) = M.α (M.φ (M.φ (M.α data.dart))) := by
    rw [hx, data.sideAlpha₂_apply_coe hsep]
    rfl
  have hp_tail : M.tail p = M.head data.dart := by
    rw [hp, ProofsInTheBook.ChordSigmaContig.tail_pow_sigma, hx_coe,
      tail_alpha_phiSq_alphaDart hNT data, M.tail_alpha]
  have hp_ne_dart : p ≠ data.dart := by
    intro hpd
    have htail_eq : M.tail data.dart = M.head data.dart := by
      rw [← hp_tail, hpd]
    exact ProofsInTheBook.ChordSigmaContig.u_ne_v data htail_eq
  have hp_kept : p ∈ data.keptSet₂ := by
    by_cases hp_outer : M.dartFace p = hNT.outerFace
    · exact ⟨Or.inr ⟨hp_outer, hαp_side⟩, by simpa using hp_ne_alpha_dart⟩
    · have hp_not_boundary : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge p) := by
        intro hbe
        rcases data.boundaryEdge_dart_outer hbe with hpout | hαout
        · exact hp_outer hpout
        · exact data.side₂_subset_nonouter hαp_side hαout
      have hp_not_chord : M.dartEdge p ≠ s(u, v) := by
        intro hch
        rcases data.chord_edge_darts hch with hpd | hpα
        · exact hp_ne_dart hpd
        · exact hp_ne_alpha_dart hpα
      have hp_side : M.dartFace p ∈ data.side₂ := by
        have hα_edge_not_boundary :
            ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge (M.α p)) := by
          intro hbe
          exact hp_not_boundary (by rwa [M.dartEdge_alpha] at hbe)
        have hα_edge_not_chord : M.dartEdge (M.α p) ≠ s(u, v) := by
          intro hch
          exact hp_not_chord (by rwa [M.dartEdge_alpha] at hch)
        have := data.alpha_mem_side₂_of_interior (e := M.α p) hαp_side
          hα_edge_not_boundary hα_edge_not_chord
        rwa [M.alpha_alpha] at this
      exact keptSet₂_of_side₂_ne_alphaDart hNT data hp_side hp_ne_alpha_dart
  have hp_not_deleted : p ∉ data.keptDel₂ := (data.mem_keptDel₂_iff p).2 hp_kept
  exact hp_not_deleted hp_deleted

/-- Second side-2 endpoint face fact: the edge-reverse of `a₁` is not a side-2 dart. -/
theorem face_β₂a₁_not_side₂
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.dartFace ((data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)) : D) ∉ data.side₂ := by
  classical
  intro hβside
  set x : {d : D // d ∉ data.keptDel₂} := face₂Dart₁ data with hx
  set n := Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₂ x with hn
  set p : D := (M.σ⁻¹ ^ (n - 1)) x.1 with hp
  have hn_ge : 2 ≤ n := by
    rw [hn, hx]
    exact face₂Dart₁_inv_firstOutside_ge_two hNT data hsep
  have hp_deleted : p ∈ data.keptDel₂ := by
    by_contra hp_not
    have hmin := Equiv.Perm.DeleteSet.firstOutside_min M.σ⁻¹ data.keptDel₂ x
      (m := n - 1) (by rw [hn]; omega)
    exact hmin ⟨by omega, by simpa [p] using hp_not⟩
  have ha₁_coe : ((side₂Anchor₁ data hsep) : D) = (M.σ⁻¹ ^ n) x.1 := by
    rw [side₂Anchor₁]
    change ((Equiv.Perm.DeleteSet.deleteSetFun M.σ⁻¹ data.keptDel₂
        (face₂Dart₁ data)) : D) = (M.σ⁻¹ ^ n) x.1
    rw [Equiv.Perm.DeleteSet.deleteSetFun_coe]
  have hσa₁ : M.σ ((side₂Anchor₁ data hsep : {d : D // d ∉ data.keptDel₂}) : D) = p := by
    rw [ha₁_coe, hp]
    have hs : n - 1 + 1 = n := by omega
    have hpow : (M.σ⁻¹ ^ n) x.1 = M.σ⁻¹ ((M.σ⁻¹ ^ (n - 1)) x.1) := by
      rw [← hs, pow_succ']
      rfl
    rw [hpow]
    simp
  have hβcoe : ((data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)) : D)
      = M.α ((side₂Anchor₁ data hsep : {d : D // d ∉ data.keptDel₂}) : D) := by
    rw [data.sideAlpha₂_apply_coe hsep]
  have hp_side : M.dartFace p ∈ data.side₂ := by
    rw [← hσa₁]
    rw [ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M)]
    rwa [← hβcoe]
  have hp_tail : M.tail p = M.tail data.dart := by
    rw [hp, tail_pow_sigma_inv, hx]
    rw [face₂Dart₁_tail hNT data, M.head_alpha]
  have hp_ne_alpha_dart : p ≠ M.α data.dart := by
    intro hpα
    have htail_eq : M.tail data.dart = M.head data.dart := by
      rw [← hp_tail, hpα, M.tail_alpha]
    exact ProofsInTheBook.ChordSigmaContig.u_ne_v data htail_eq
  have hp_not_deleted : p ∉ data.keptDel₂ :=
    (data.mem_keptDel₂_iff p).2 (keptSet₂_of_side₂_ne_alphaDart hNT data hp_side hp_ne_alpha_dart)
  exact hp_not_deleted hp_deleted

/-- Canonical side-2 endpoint boundary alignment with the two cyclic-order face facts discharged. -/
theorem side₂EndpointBoundaryAlignment_uncond
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ((data.sideSigma₂ (side₂Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts ∧
    ((data.sideAlpha₂ hsep (side₂Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts :=
  ⟨kept_mem_outerCycle_of_face_not_side₂ hNT data hsep _
      (face_ρ₂a₀_not_side₂ hNT data hsep),
   kept_mem_outerCycle_of_face_not_side₂ hNT data hsep _
      (face_β₂a₁_not_side₂ hNT data hsep)⟩





/-- Canonical side-2 share-face fact for the swapped endpoint order. -/
theorem side₂AnchorsShareFace_canonical_swapped
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) := by
  exact (side₂AnchorsShareFace_canonical data hsep).symm

/-- Unconditional side-2 sphere-map fact for the swapped canonical anchors. -/
theorem side₂_isSphereMap_canonical_swapped_uncond
    (hNT : NearTriangulation M) {u v : M.Vertex}
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).IsSphereMap :=
  ProofsInTheBook.ChordDisk.side₂_isSphereMap_of_disk
    data hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
    (ProofsInTheBook.ChordSideClose.side₂IsDisk_unconditional data hsep)
    (side₂AnchorsShareFace_canonical_swapped (hNT := hNT) data hsep)









/-- Conversely, any kept-`inl` representative whose original `M`-face is `face₁` lands on the
canonical touched side face. -/
theorem face₁_rep_touched_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁})
    (hface₁ : M.dartFace k.1 = data.face₁) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
      =
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) := by
  classical
  have hsc : M.φ.SameCycle data.dart k.1 := by
    have hf : M.dartFace k.1 = M.dartFace data.dart := by
      rw [hface₁]; rfl
    exact (Quotient.exact hf).symm
  rcases ProofsInTheBook.ChordSideClose.face₁_dart_cases data hsc with hk | hk | hk
  · exact False.elim (k.2 (hk ▸ ProofsInTheBook.ChordFaceFinal.dart_mem_keptDel₁ data))
  · have hk' : k = face₁Dart₁ data := by
      apply Subtype.ext
      exact hk
    rw [hk']
  · have hk' : k = face₁Dart₂ data := by
      apply Subtype.ext
      exact hk
    rw [hk']
    exact (ProofsInTheBook.ChordBoundaryOrbit.sideFace_inl_eq_iff_tracePhi
      (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
      (side₁Anchors_ne data hsep) (face₁Dart₂ data) (face₁Dart₁ data)).2
      ⟨1, by rw [zpow_one, side₁Anchors_trace21 data hsep]⟩

/-- The canonical one-fresh indicator for the touched `face₁` side face, stated without the
old `Side₁OuterTraceData` bundle. -/
theorem side₁Anchors_oneFresh_canonical_direct
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
          (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
          (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) then 1 else 0)) = 1 := by
  classical
  have hfirst : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        (face₁Dart₁ data) ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) :=
    (ProofsInTheBook.ZinanCh35Hclass.side₁_betaA0_sameCycle_face₁Dart₁ data hsep).symm
  have hsecond : ¬ (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        (face₁Dart₁ data) ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) := by
    intro hsc
    have hface : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))
        = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).dartFace
            (Sum.inl ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep))) :=
      (ProofsInTheBook.ChordBoundaryOrbit.sideFace_inl_eq_iff_tracePhi
        (data.sideAlpha₁ hsep) data.sideSigma₁
        (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
        (side₁Anchors_ne data hsep) _ _).2 hsc
    have hb1 : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace
            (Sum.inl ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)))
        = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) :=
      (ProofsInTheBook.ChordBoundaryOrbit.chordDart_face_eq_b1
        (data.sideAlpha₁ hsep) data.sideSigma₁
        (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
        (side₁Anchors_ne data hsep)).symm
    exact side₁_face₁_not_outer_canonical data hsep (hface.trans hb1)
  rw [if_pos hfirst, if_neg hsecond]

/-- The touched side face is a triangle, directly from the canonical `face₁` two-cycle and
one-fresh count. -/
theorem side₁_touched_faceLen_three_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceLen
      ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))) = 3 := by
  classical
  let S := data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)
  let f₀ : S.Face := S.dartFace (Sum.inl (face₁Dart₁ data))
  have htri := ProofsInTheBook.ChordAnchor.face₁_sideTriangle_ofFace₁Cycle
    data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep) f₀
    (side₁Anchors_trace12 data hsep) (side₁Anchors_trace21 data hsep)
    rfl (side₁Anchors_oneFresh_canonical_direct hNT data hsep)
  obtain ⟨k, hkf, hlen⟩ := htri
  exact by simpa [S, f₀, hkf] using hlen

/-- The remaining direct-`inner_tri` residue after the touched face is handled by count:
every other non-outer side face has a splice-untouched side-1 representative avoiding `face₁`. -/
def CanonicalSide₁NonTouchedInnerClassifier
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop :=
  let S := data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)
  ∀ f : S.Face,
    f ≠ S.dartFace (Sum.inr 1) →
    f ≠ S.dartFace (Sum.inl (face₁Dart₁ data)) →
      ∃ k : {d : D // d ∉ data.keptDel₁},
        S.dartFace (Sum.inl k) = f ∧
        M.dartFace k.1 ∈ data.side₁ ∧
        M.dartFace k.1 ≠ data.face₁ ∧
        ProofsInTheBook.ChordInnerTri.SpliceUntouched
          (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) k

/-- The canonical non-touched inner classifier, with the side outer orbit identified as exactly the
side-1 boundary arc and the touched `face₁` orbit carved out explicitly. -/
theorem canonicalSide₁NonTouchedInnerClassifier_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    CanonicalSide₁NonTouchedInnerClassifier hNT data hsep := by
  classical
  intro f hfOuter hfTouched
  obtain ⟨k, hkf⟩ :=
    ProofsInTheBook.ChordFaceClass.sideFace_has_inl_rep data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) f
  have hnotOuterM : M.dartFace k.1 ≠ hNT.outerFace := by
    intro hkOuterFace
    have hkKept : k.1 ∈ data.keptSet₁ := (data.mem_keptDel₁_iff k.1).1 k.2
    rcases hkKept.1 with hside | houterArc
    · exact data.side₁_subset_nonouter hside hkOuterFace
    · obtain ⟨i, hi⟩ := outerArc₁_mem_bwdArc_canonical hNT data hsep houterArc
      have hTA := canonicalTracePhiArc_bwdArc_uncond hNT data hsep
      have hkArc :
          k =
            ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i,
              bwdArc_arcDart_notMem_keptDel₁ hNT data hsep i⟩ := by
        apply Subtype.ext
        exact hi
      have hτ :
          (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
            ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) k :=
        (hTA.mem_iff k).2 ⟨i, hkArc⟩
      have hfaceOuter :
          (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
            =
          (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) :=
        (ProofsInTheBook.ChordBoundaryOrbit.sideFace_eq_chordOrbit1_iff
          (data.sideAlpha₁ hsep) data.sideSigma₁
          (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
          (side₁Anchors_ne data hsep) k).2 hτ.symm
      exact hfOuter (hkf.symm.trans hfaceOuter)
  have hside : M.dartFace k.1 ∈ data.side₁ :=
    ProofsInTheBook.ChordFaceClass.keptDart_face_mem_side₁ data k hnotOuterM
  have hnotFace₁ : M.dartFace k.1 ≠ data.face₁ := by
    intro hkFace₁
    have htouch :
        (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
          =
        (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) :=
      face₁_rep_touched_canonical hNT data hsep k hkFace₁
    exact hfTouched (hkf.symm.trans htouch)
  have h0 :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
        ≠
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 0) := by
    intro h
    apply hfTouched
    exact hkf.symm.trans
      (h.trans (ProofsInTheBook.ZinanCh35Hclass.side₁_chord0_face_eq_face₁_canonical data hsep))
  have h1 :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
        ≠
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) := by
    intro h
    exact hfOuter (hkf.symm.trans h)
  refine ⟨k, hkf, hside, hnotFace₁, ?_⟩
  exact ProofsInTheBook.ChordBoundaryOrbit.spliceUntouched_of_face_ne_chordOrbits
    (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
    (side₁Anchors_ne data hsep) h0 h1

/-- Direct `inner_tri` from the exact remaining non-touched classifier. -/
theorem side₁_inner_tri_of_nonTouchedClassifier
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hclass : CanonicalSide₁NonTouchedInnerClassifier hNT data hsep) :
    ∀ f : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).Face,
      f ≠ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) →
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceLen f = 3 := by
  intro f hf
  by_cases hf₀ :
      f = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))
  · rw [hf₀]
    exact side₁_touched_faceLen_three_canonical hNT data hsep
  · obtain ⟨k, hkf, hside, hface₁, huntouched⟩ := hclass f hf hf₀
    rw [← hkf]
    exact ProofsInTheBook.ChordInnerTri.sideMap₁_faceLen_inl_three_of_side₁
      data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep) k hside hface₁ huntouched

/-- **Direct side-1 `ContiguousInterval` assembler, bypassing `InnerRepsAvoidBoundary`.**
If the side-map `inner_tri` field is supplied directly, all other canonical side-1 inputs are
now proved unconditionally (`sphere`, `simpleGraph`, `outer_simple`, `outer_len`). -/
noncomputable def contiguousInterval₁_direct_of_inner_tri
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (inner_tri : ∀ f :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).Face,
        f ≠ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) →
        (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).faceLen f = 3) :
    ChordSideNT.ContiguousInterval data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) :=
  ChordSideNT.contiguousInterval_of_nearTriangulation data hsep
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
    (ProofsInTheBook.ZinanCh35BoundaryAssembler.nearTriangulation_of_explicit_boundary_classification
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep))
      (ChordSideNT.side₁_sphere_unconditional data hsep
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
        (side₁AnchorsShareFace_canonical data hsep))
      (sideMap₁_isSimpleGraph_canonical hNT data hsep)
      ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1))
      (Sum.inr 1) rfl
      (side₁_outer_simple_canonical_uncond hNT data hsep)
      (ProofsInTheBook.ZinanCh35Contiguous.side₁_outerLen_ge_three data hsep
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
        (side₁ChordIncidenceNonDegenerate_canonical hNT data hsep))
      inner_tri)

/-- `ContiguousInterval` from the precise remaining non-touched inner-face classifier. -/
noncomputable def contiguousInterval₁_direct_of_nonTouchedClassifier
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hclass : CanonicalSide₁NonTouchedInnerClassifier hNT data hsep) :
    ChordSideNT.ContiguousInterval data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) :=
  contiguousInterval₁_direct_of_inner_tri hNT data hsep
    (side₁_inner_tri_of_nonTouchedClassifier hNT data hsep hclass)

/-- Unconditional canonical side-1 `ContiguousInterval`, using the direct non-touched classifier. -/
noncomputable def contiguousInterval₁_direct_canonical_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ChordSideNT.ContiguousInterval data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) :=
  contiguousInterval₁_direct_of_nonTouchedClassifier hNT data hsep
    (canonicalSide₁NonTouchedInnerClassifier_uncond hNT data hsep)



/-- The `M.φ`-orbit of a side-2 kept dart stays kept. -/
def OrbitKept₂ (data : hNT.ChordSplitData u v) (k : {d : D // d ∉ data.keptDel₂}) : Prop :=
  ∀ n : ℕ, M.φ^[n] k.1 ∉ data.keptDel₂

/-- One side-2 kept-face step agrees with one `M.φ` step when the successor is kept. -/
lemma sideKeptPhi₂_apply_eq_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂}) (hnext : M.φ k.1 ∉ data.keptDel₂) :
    (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ k : D) = M.φ k.1 := by
  show (data.sideSigma₂ (data.sideAlpha₂ hsep k) : {d : D // d ∉ data.keptDel₂}).1
    = M.φ k.1
  have hσnext : M.σ ((data.sideAlpha₂ hsep k : {d : D // d ∉ data.keptDel₂}) : D)
      ∉ data.keptDel₂ := by
    rw [data.sideAlpha₂_apply_coe hsep]
    have : M.φ k.1 = M.σ (M.α k.1) := rfl
    rwa [← this]
  show (FilteredRotation.filteredRotation M.σ data.keptDel₂
      (data.sideAlpha₂ hsep k) : {d : D // d ∉ data.keptDel₂}).1 = M.φ k.1
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₂
    (data.sideAlpha₂ hsep k) hσnext, data.sideAlpha₂_apply_coe hsep]
  rfl

lemma sideKeptPhi₂_iterate_eq_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂}) (hkept : OrbitKept₂ hNT data k) (n : ℕ) :
    ((keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂)^[n] k : D) = M.φ^[n] k.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hkn : ((keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂)^[n] k : D)
          = M.φ^[n] k.1 := ih
      have hnext : M.φ ((keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂)^[n] k : D)
          ∉ data.keptDel₂ := by
        rw [hkn]
        have := hkept (n + 1)
        rwa [Function.iterate_succ_apply'] at this
      rw [sideKeptPhi₂_apply_eq_phi hNT data hsep _ hnext, hkn]

lemma sideKeptPhi₂_sameCycle_iff_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂}) (hkept : OrbitKept₂ hNT data k)
    (x : {d : D // d ∉ data.keptDel₂}) :
    (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂).SameCycle k x ↔
      M.φ.SameCycle k.1 x.1 := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    have := congrArg Subtype.val hn
    rw [sideKeptPhi₂_iterate_eq_phi hNT data hsep k hkept n] at this
    exact this
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    apply Subtype.ext
    rw [sideKeptPhi₂_iterate_eq_phi hNT data hsep k hkept n]
    exact hn

lemma orbitKept₂_mem (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₂}) (hkept : OrbitKept₂ hNT data k)
    {d : D} (hd : M.φ.SameCycle k.1 d) : d ∉ data.keptDel₂ := by
  obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact hkept n

theorem sideKeptMap₂_faceLen_eq_M (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂}) (hkept : OrbitKept₂ hNT data k) :
    (ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep).faceLen
      ((ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep).dartFace k)
      = M.faceLen (M.dartFace k.1) := by
  classical
  show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid
          (ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep).φ) k)).card
    = (Finset.univ.filter (fun d => Quotient.mk _ d
      = Quotient.mk (cycleSetoid M.φ) k.1)).card
  have hφ : (ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep).φ
      = keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ := rfl
  rw [show (Finset.univ.filter (fun x => Quotient.mk _
      x = Quotient.mk (cycleSetoid
        (ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep).φ) k)).card
      = ((Finset.univ.filter (fun x : {d : D // d ∉ data.keptDel₂} =>
          Quotient.mk _ x = Quotient.mk (cycleSetoid
            (ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep).φ) k)).map
          ⟨Subtype.val, Subtype.val_injective⟩).card from (Finset.card_map _).symm]
  congr 1
  ext d
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, hcd, rfl⟩
    have hsc : (ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep).φ.SameCycle k c :=
      Quotient.exact hcd.symm
    rw [hφ, sideKeptPhi₂_sameCycle_iff_phi hNT data hsep k hkept] at hsc
    exact Quotient.sound hsc.symm
  · intro hd
    have hsc : M.φ.SameCycle k.1 d := Quotient.exact hd.symm
    have hdkept : d ∉ data.keptDel₂ := orbitKept₂_mem hNT data k hkept hsc
    refine ⟨⟨d, hdkept⟩, ?_, rfl⟩
    apply Quotient.sound
    show (ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep).φ.SameCycle
      (⟨d, hdkept⟩ : {d : D // d ∉ data.keptDel₂}) k
    refine Equiv.Perm.SameCycle.symm ?_
    rw [hφ, sideKeptPhi₂_sameCycle_iff_phi hNT data hsep k hkept ⟨d, hdkept⟩]
    exact hsc

theorem orbitKept_of_side₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂})
    (hside : M.dartFace k.1 ∈ data.side₂) (hface₂ : M.dartFace k.1 ≠ data.face₂) :
    OrbitKept₂ hNT data k := by
  intro n
  rw [data.mem_keptDel₂_iff]
  have hsameface : M.dartFace (M.φ^[n] k.1) = M.dartFace k.1 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', M.dartFace_phi, ih]
  have hin : M.φ^[n] k.1 ∈ data.sideDarts₂ := by
    show M.dartFace (M.φ^[n] k.1) ∈ data.side₂
    rw [hsameface]; exact hside
  have hne_alpha_dart : M.φ^[n] k.1 ≠ M.α data.dart := by
    intro he
    apply hface₂
    have : M.dartFace (M.φ^[n] k.1) = data.face₂ := by rw [he]; rfl
    rwa [hsameface] at this
  exact ⟨Or.inl hin, by simpa using hne_alpha_dart⟩

theorem sideMap₂_faceLen_inl_eq_M (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₂})
    (huntouched : ProofsInTheBook.ChordInnerTri.SpliceUntouched
      (data.sideAlpha₂ hsep) data.sideSigma₂ a₀ a₁ k)
    (hkept : OrbitKept₂ hNT data k) :
    (data.sideMap₂ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₂ hsep a₀ a₁ hne).dartFace (Sum.inl k))
      = M.faceLen (M.dartFace k.1) := by
  have h1 := ProofsInTheBook.ChordInnerTri.freshPhi_faceLen_inl_eq_keptPhi
    (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) hne huntouched
  have h2 := sideKeptMap₂_faceLen_eq_M (hNT := hNT) (data := data) (hsep := hsep)
    (k := k) (hkept := hkept)
  rw [show data.sideMap₂ hsep a₀ a₁ hne
      = freshMap (data.sideAlpha₂ hsep) data.sideSigma₂
          (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) a₀ a₁ hne from rfl]
  rw [h1]
  rw [show ProofsInTheBook.ChordSideRecon.keptCombMap (data.sideAlpha₂ hsep) data.sideSigma₂
      (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
      = ProofsInTheBook.ChordSideRecon.sideKeptMap₂ data hsep from rfl]
  exact h2

theorem sideMap₂_faceLen_inl_eq_three (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₂})
    (huntouched : ProofsInTheBook.ChordInnerTri.SpliceUntouched
      (data.sideAlpha₂ hsep) data.sideSigma₂ a₀ a₁ k)
    (hkept : OrbitKept₂ hNT data k)
    (hMinner : M.dartFace k.1 ≠ hNT.outerFace) :
    (data.sideMap₂ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₂ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 := by
  rw [sideMap₂_faceLen_inl_eq_M hNT data hsep a₀ a₁ hne k huntouched hkept]
  exact hNT.inner_tri (M.dartFace k.1) hMinner

theorem sideMap₂_faceLen_inl_three_of_side₂ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₂})
    (hside : M.dartFace k.1 ∈ data.side₂) (hface₂ : M.dartFace k.1 ≠ data.face₂)
    (huntouched : ProofsInTheBook.ChordInnerTri.SpliceUntouched
      (data.sideAlpha₂ hsep) data.sideSigma₂ a₀ a₁ k) :
    (data.sideMap₂ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₂ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 :=
  sideMap₂_faceLen_inl_eq_three hNT data hsep a₀ a₁ hne k huntouched
    (orbitKept_of_side₂ hNT data hsep k hside hface₂)
    (data.side₂_subset_nonouter hside)

theorem sideFace₂_has_inl_rep (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₂ hsep a₀ a₁ hne).Face) :
    ∃ k : {d : D // d ∉ data.keptDel₂},
      (data.sideMap₂ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f := by
  classical
  refine Quotient.inductionOn f (fun x => ?_)
  refine ⟨faceProj (data.sideAlpha₂ hsep) a₀ a₁ x, ?_⟩
  show Quotient.mk (cycleSetoid (data.sideMap₂ hsep a₀ a₁ hne).φ)
      (Sum.inl (faceProj (data.sideAlpha₂ hsep) a₀ a₁ x))
    = Quotient.mk (cycleSetoid (data.sideMap₂ hsep a₀ a₁ hne).φ) x
  apply Quotient.sound
  have h := freshPhi_sameCycle_inl_faceProj (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) hne x
  exact h.symm

theorem keptDart_face_side₂_or_outer (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₂}) :
    M.dartFace k.1 ∈ data.side₂ ∨ M.dartFace k.1 = hNT.outerFace := by
  have hk : k.1 ∈ data.keptSet₂ := (data.mem_keptDel₂_iff k.1).1 k.2
  obtain ⟨hU, _⟩ := hk
  rcases hU with hin | hout
  · exact Or.inl hin
  · exact Or.inr hout.1

theorem keptDart_face_mem_side₂ (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₂}) (houter : M.dartFace k.1 ≠ hNT.outerFace) :
    M.dartFace k.1 ∈ data.side₂ :=
  (keptDart_face_side₂_or_outer hNT data k).resolve_right houter

/-- Every canonical side-2 outer-arc dart is one of the `fwdArc` darts. -/
theorem outerArc₂_mem_fwdArc_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) {d : D}
    (hdouter : d ∈ data.outerArc₂) :
    ∃ i : Fin (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).len,
      d = (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i := by
  classical
  set C := hNT.outerCycle
  have hdmem : d ∈ C.darts := by
    exact (C.mem_darts_iff d).2 hdouter.1
  have hne : M.tail data.dart ≠ M.head data.dart :=
    ProofsInTheBook.ChordSigmaContig.u_ne_v data
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  have hxy_edge : s(M.tail data.dart, M.head data.dart) = s(u, v) := hedge
  have htail_bv : C.IsBoundaryVertex (M.tail data.dart) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · rw [hxu]; exact data.chord.left_boundary
    · rw [hxv]; exact data.chord.right_boundary
  have hhead_bv : C.IsBoundaryVertex (M.head data.dart) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨_, hyv⟩ | ⟨_, hyu⟩
    · rw [hyv]; exact data.chord.right_boundary
    · rw [hyu]; exact data.chord.left_boundary
  have hnbe : ¬ C.IsBoundaryEdge s(M.tail data.dart, M.head data.dart) := by
    rw [hxy_edge]; exact data.chord.not_boundary_edge
  let R := ProofsInTheBook.ZinanCh35BoundaryAssembler.BoundaryCycle.nonEdgeRuns
    C hNT.outer_simple hne htail_bv hhead_bv hnbe
  have hboundaryVertex : C.IsBoundaryVertex (M.tail d) := by
    rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq]
    exact List.mem_map_of_mem hdmem
  have hdisj : Disjoint data.side₁ data.side₂ := by
    simpa [NearTriangulation.SidesDisjoint] using
      (separates_iff_sidesDisjoint data).1 hsep
  rcases R.covering hboundaryVertex with hUV | hVU | htail | hhead
  · obtain ⟨i, hi⟩ := hUV
    have hd_eq : d = R.arcUV.arcDart i := by
      apply C.tail_injective_on_darts hNT.outer_simple hdmem (R.arcUV.boundary i)
      exact hi.symm
    have hside₁ : M.dartFace (M.α d) ∈ data.side₁ := by
      rw [hd_eq]
      exact ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.bwdRun_reverse_face_mem_side₁ data
        R.arcUV R.lenUV i
    rw [Set.disjoint_left] at hdisj
    exact False.elim (hdisj hside₁ hdouter.2)
  · obtain ⟨i, hi⟩ := hVU
    have hd_eq : d = R.arcVU.arcDart i := by
      apply C.tail_injective_on_darts hNT.outer_simple hdmem (R.arcVU.boundary i)
      exact hi.symm
    let A := ProofsInTheBook.ZinanCh35Aligned.daCast
      (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data) rfl rfl
    obtain ⟨j, hj⟩ := dartArc_dart_mem_of_same_endpoints C hNT.outer_simple A R.arcVU i
    refine ⟨Fin.cast
      (ProofsInTheBook.ZinanCh35Aligned.daCast_len
        (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data) rfl rfl) j, ?_⟩
    have hcast := ProofsInTheBook.ZinanCh35Aligned.daCast_arcDart_eq
      (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data) rfl rfl j
    exact hd_eq.trans (hj.trans hcast)
  · have hd_eq : d = R.arcUV.arcDart R.arcUV.firstIdx := by
      apply C.tail_injective_on_darts hNT.outer_simple hdmem (R.arcUV.boundary R.arcUV.firstIdx)
      rw [htail, R.arcUV.tail_firstIdx]
    have hside₁ : M.dartFace (M.α d) ∈ data.side₁ := by
      rw [hd_eq]
      exact ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.bwdRun_reverse_face_mem_side₁ data
        R.arcUV R.lenUV R.arcUV.firstIdx
    rw [Set.disjoint_left] at hdisj
    exact False.elim (hdisj hside₁ hdouter.2)
  · refine ⟨(ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).firstIdx, ?_⟩
    apply C.tail_injective_on_darts hNT.outer_simple hdmem
      ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).boundary _)
    rw [hhead, (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).tail_firstIdx]

lemma face₂Dart_distinct (data : hNT.ChordSplitData u v) :
    face₂Dart₁ data ≠ face₂Dart₂ data := by
  intro h
  exact face₂_kept_darts_distinct data (congrArg Subtype.val h)

lemma sideAlpha₂_anchor₀_eq_face₂Dart₂
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₂ hsep (side₂Anchor₀ data hsep) = face₂Dart₂ data := by
  have ha₀ : side₂Anchor₀ data hsep = data.sideAlpha₂ hsep (face₂Dart₂ data) := by
    apply data.sideSigma₂.injective
    rw [sideSigma₂_side₂Anchor₀ data hsep]
    rfl
  rw [ha₀]
  have hinv : data.sideAlpha₂ hsep * data.sideAlpha₂ hsep = 1 :=
    data.sideAlpha₂_involutive hsep
  have := congrArg (fun f : Equiv.Perm {d : D // d ∉ data.keptDel₂} =>
      f (face₂Dart₂ data)) hinv
  simpa [Equiv.Perm.mul_apply] using this

/-- In the swapped side-2 map, the assembler root `inr 1` is the chord orbit through
`face₂Dart₂`, not the original canonical boundary orbit. -/
theorem side₂_swapped_inr1_face_eq_face₂Dart₂
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inr 1)
      =
    (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).dartFace
      (Sum.inl (face₂Dart₂ data)) := by
  have hβa₁ :
      data.sideAlpha₂ hsep (side₂Anchor₀ data hsep) = face₂Dart₂ data :=
    sideAlpha₂_anchor₀_eq_face₂Dart₂ hNT data hsep
  change
      (freshMap (data.sideAlpha₂ hsep) data.sideSigma₂
          (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inr 1)
        =
      (freshMap (data.sideAlpha₂ hsep) data.sideSigma₂
          (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl (face₂Dart₂ data))
  simpa [hβa₁] using
    (ProofsInTheBook.ChordBoundaryOrbit.chordDart_face_eq_b1
      (data.sideAlpha₂ hsep) data.sideSigma₂
      (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
      ((side₂Anchors_ne hNT data hsep).symm))

/-- The swapped side-2 chord predecessors are still in distinct `tracePhi` orbits. -/
theorem side₂_chordPred_notSameCycle_canonical_swapped
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ¬ (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
      ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep))
      ((data.sideAlpha₂ hsep) (side₂Anchor₀ data hsep)) := by
  classical
  set β := data.sideAlpha₂ hsep with hβ
  set ρ := data.sideSigma₂ with hρ
  set a₀ := side₂Anchor₁ data hsep with ha₀
  set a₁ := side₂Anchor₀ data hsep with ha₁
  have hshare : (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁) := by
    have h := side₂AnchorsShareFace_canonical_swapped (hNT := hNT) data hsep
    simpa [hβ, hρ, ha₀, ha₁, ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace, keptPhi]
      using h
  have hne : ρ a₀ ≠ ρ a₁ := ρa₀_ne_ρa₁ ρ (side₂Anchors_ne hNT data hsep).symm
  have hsplit : ¬ (tracePhi β ρ a₀ a₁).SameCycle (ρ a₀) (ρ a₁) := by
    rw [show tracePhi β ρ a₀ a₁ = Equiv.swap (ρ a₀) (ρ a₁) * keptPhi β ρ from rfl]
    exact notSameCycle_swap_mul_left_of_sameCycle (keptPhi β ρ) hne hshare
  intro hsc
  apply hsplit
  have hb0 : tracePhi β ρ a₀ a₁ (β a₀) = ρ a₁ :=
    tracePhi_b0 β ρ (data.sideAlpha₂_involutive hsep) a₀ a₁
  have hb1 : tracePhi β ρ a₀ a₁ (β a₁) = ρ a₀ :=
    tracePhi_b1 β ρ (data.sideAlpha₂_involutive hsep) a₀ a₁
  have hstep : (tracePhi β ρ a₀ a₁).SameCycle
      (tracePhi β ρ a₀ a₁ (β a₀)) (tracePhi β ρ a₀ a₁ (β a₁)) :=
    hsc.apply_left.apply_right
  rw [hb0, hb1] at hstep
  exact hstep.symm



/-- Swapped side-2 outer-orbit membership iff for the root `inr 0`. -/
theorem canonical_side₂_outer_orbit_mem_iff_swapped_root0
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (x : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) :
    x ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)
      ↔ x = Sum.inr 0 ∨
        ∃ k : {d : D // d ∉ data.keptDel₂}, x = Sum.inl k ∧
          (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
              (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
            ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k := by
  classical
  set a₀ := side₂Anchor₁ data hsep with ha₀
  set a₁ := side₂Anchor₀ data hsep with ha₁
  set hne := (side₂Anchors_ne hNT data hsep).symm with hhne
  set β := data.sideAlpha₂ hsep with hβ
  set ρ := data.sideSigma₂ with hρ
  have hinv : β * β = 1 := data.sideAlpha₂_involutive hsep
  have hfix : ∀ k, β k ≠ k := data.sideAlpha₂_no_fixed hsep
  have hSeq : data.sideMap₂ hsep a₀ a₁ hne = freshMap β ρ hinv hfix a₀ a₁ hne := rfl
  have hsplit : ¬ (tracePhi β ρ a₀ a₁).SameCycle (β a₀) (β a₁) := by
    simpa [hβ, hρ, ha₀, ha₁, hhne] using
      side₂_chordPred_notSameCycle_canonical_swapped hNT data hsep
  have hroot_support :
      (Sum.inr 0 : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2)
        ∈ (freshMap β ρ hinv hfix a₀ a₁ hne).φ.support := by
    rw [Equiv.Perm.mem_support, freshMap_phi_inr_zero β ρ hinv hfix hne]
    exact Sum.inl_ne_inr
  rw [hSeq, CombMap.faceDartList]
  constructor
  · intro hx
    rw [Equiv.Perm.mem_toList_iff] at hx
    obtain ⟨hcyc, _⟩ := hx
    have hτ : (tracePhi β ρ a₀ a₁).SameCycle (β a₀) (faceProj β a₀ a₁ x) := by
      have h := (freshFace_sameCycle_iff β ρ hinv hfix hne (Sum.inr 0) x).1 hcyc
      simpa [faceProj_inr_zero] using h
    cases x with
    | inl k =>
        right
        exact ⟨k, rfl, by simpa [faceProj_inl] using hτ⟩
    | inr j =>
        fin_cases j
        · left; rfl
        · exact absurd (by simpa [faceProj_inr_one] using hτ) hsplit
  · intro hx
    rw [Equiv.Perm.mem_toList_iff]
    refine ⟨?_, hroot_support⟩
    rcases hx with hroot | ⟨k, hxk, hk⟩
    · rw [hroot]
    · rw [hxk]
      refine (freshFace_sameCycle_iff β ρ hinv hfix hne (Sum.inr 0) (Sum.inl k)).2 ?_
      simpa [faceProj_inl, faceProj_inr_zero] using hk

/-- Swapped side-2 `OuterTraceInjOn` rooted at `inr 0`. -/
def OuterTraceInjOn₂SwappedRoot0
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop :=
  ∀ x ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0),
    ∀ y ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0),
      M.tail (proj (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) x).1 =
        M.tail (proj (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) y).1 → x = y

/-- Swapped side-2 root-`inr 0` `OuterTraceInjOn`, from the original fwd-arc trace. -/
theorem canonical_OuterTraceInjOn₂_swapped_root0_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    OuterTraceInjOn₂SwappedRoot0 hNT data hsep := by
  classical
  set A := ProofsInTheBook.ZinanCh35ArcSide.fwdArc data
  set hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₂ :=
    fun i => fwdArc_arcDart_notMem_keptDel₂ hNT data hsep i
  have H := side₂EndpointBoundaryAlignment_uncond hNT data hsep
  have hTA := canonicalTracePhiArc₂_fwdArc_of_alignment hNT data hsep H.1 H.2
  have hroot : M.tail (proj (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (Sum.inr 0)).1 = M.tail data.dart := by
    rw [proj_inr_zero, canonicalSide₂Anchor₁_tail hNT data hsep]
  intro x hx y hy htail
  rcases (canonical_side₂_outer_orbit_mem_iff_swapped_root0 hNT data hsep x).1 hx with
    hxr | ⟨kx, hxk, hτx⟩
  <;> rcases (canonical_side₂_outer_orbit_mem_iff_swapped_root0 hNT data hsep y).1 hy with
    hyr | ⟨ky, hyk, hτy⟩
  · rw [hxr, hyr]
  · exfalso
    rw [hxr, hyk] at htail
    simp only [proj_inl, hroot] at htail
    have hτy' :
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
          ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) ky := by
      simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτy
    rcases (hTA.mem_iff ky).1 hτy' with ⟨j, hyj⟩
    rw [hyj] at htail
    exact A.head_last_ne_tail j htail
  · exfalso
    rw [hyr, hxk] at htail
    simp only [proj_inl, hroot] at htail
    have hτx' :
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
          ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) kx := by
      simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτx
    rcases (hTA.mem_iff kx).1 hτx' with ⟨i, hxi⟩
    rw [hxi] at htail
    exact A.head_last_ne_tail i htail.symm
  · rw [hxk, hyk]
    rw [hxk, hyk] at htail
    simp only [proj_inl] at htail
    have hτx' :
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
          ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) kx := by
      simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτx
    have hτy' :
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
          ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) ky := by
      simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτy
    rcases (hTA.mem_iff kx).1 hτx' with ⟨i, hxi⟩
    rcases (hTA.mem_iff ky).1 hτy' with ⟨j, hyj⟩
    rw [hxi, hyj]
    rw [hxi, hyj] at htail
    simp only [A, hArcKept, arcK₂] at htail
    have hij : i = j := A.tail_nodup htail
    rw [hij]

/-- Swapped side-2 root-`inr 0` `outer_simple`. -/
theorem side₂_outer_simple_canonical_swapped_root0_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)).map
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).tail).Nodup := by
  have hL : ((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)).Nodup := by
    rw [ProofsInTheBook.PlanarMap.CombMap.faceDartList]
    exact Equiv.Perm.nodup_toList _ _
  rw [List.nodup_map_iff_inj_on hL]
  intro x hx y hy htail
  have hMtail : M.tail (proj (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) x).1
      = M.tail (proj (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) y).1 :=
    (sideMap₂_tail_eq_iff_M_tail_proj hNT data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm x y).1 htail
  exact canonical_OuterTraceInjOn₂_swapped_root0_uncond hNT data hsep x hx y hy hMtail

theorem side₂Anchors_trace12 (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
      (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep) (face₂Dart₁ data)
      = face₂Dart₂ data := by
  classical
  have h0 : data.sideAlpha₂ hsep (face₂Dart₁ data) ≠ side₂Anchor₀ data hsep := by
    intro h
    have hβa₀ := sideAlpha₂_anchor₀_eq_face₂Dart₂ hNT data hsep
    have hd : face₂Dart₁ data = face₂Dart₂ data := by
      rw [← hβa₀, ← h]
      have hinv : data.sideAlpha₂ hsep * data.sideAlpha₂ hsep = 1 :=
        data.sideAlpha₂_involutive hsep
      have := congrArg (fun f : Equiv.Perm {d : D // d ∉ data.keptDel₂} =>
          f (face₂Dart₁ data)) hinv
      simpa [Equiv.Perm.mul_apply] using this.symm
    exact face₂Dart_distinct hNT data hd
  have h1 : data.sideAlpha₂ hsep (face₂Dart₁ data) ≠ side₂Anchor₁ data hsep := by
    intro h
    have hβa₀ := sideAlpha₂_anchor₀_eq_face₂Dart₂ hNT data hsep
    have hβa₁ : data.sideAlpha₂ hsep (side₂Anchor₁ data hsep) = face₂Dart₁ data := by
      rw [← h]
      have hinv : data.sideAlpha₂ hsep * data.sideAlpha₂ hsep = 1 :=
        data.sideAlpha₂_involutive hsep
      have := congrArg (fun f : Equiv.Perm {d : D // d ∉ data.keptDel₂} =>
          f (face₂Dart₁ data)) hinv
      simpa [Equiv.Perm.mul_apply] using this
    have hρa₁ : data.sideSigma₂ (side₂Anchor₁ data hsep) = face₂Dart₁ data :=
      sideSigma₂_side₂Anchor₁ data hsep
    have hstep :
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep))
            (data.sideAlpha₂ hsep (side₂Anchor₀ data hsep))
          =
        data.sideAlpha₂ hsep (side₂Anchor₁ data hsep) := by
      rw [tracePhi_b0 (data.sideAlpha₂ hsep) data.sideSigma₂
        (data.sideAlpha₂_involutive hsep) (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)]
      rw [hρa₁, hβa₁]
    exact side₂_chordPred_notSameCycle_canonical hNT data hsep
      ⟨1, by rw [zpow_one, hstep]⟩
  rw [tracePhi_other (data.sideAlpha₂ hsep) data.sideSigma₂
    (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep) h0 h1]
  exact keptPhi_face₂Dart₁ data hsep

theorem side₂Anchors_trace21 (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
      (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep) (face₂Dart₂ data)
      = face₂Dart₁ data := by
  have hβa₀ := sideAlpha₂_anchor₀_eq_face₂Dart₂ hNT data hsep
  rw [← hβa₀]
  rw [tracePhi_b0 (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep),
    sideSigma₂_side₂Anchor₁ data hsep]



theorem sideMap₂_faceLen_three_of_count (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₂})
    (htwo : ProofsInTheBook.ChordFaceFinal.tOrbitCard
      (data.sideAlpha₂ hsep) data.sideSigma₂ a₀ a₁ k = 2)
    (hone : ((if (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂ a₀ a₁).SameCycle k
            ((data.sideAlpha₂ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂ a₀ a₁).SameCycle k
            ((data.sideAlpha₂ hsep) a₁) then 1 else 0)) = 1) :
    (data.sideMap₂ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₂ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 := by
  rw [show data.sideMap₂ hsep a₀ a₁ hne
      = freshMap (data.sideAlpha₂ hsep) data.sideSigma₂
          (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) a₀ a₁ hne from rfl]
  exact ProofsInTheBook.ChordFaceFinal.sideFaceLen_three_of_count
    (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) hne htwo hone



/-- The non-outer touched side-2 face in the swapped canonical map is triangular. -/
theorem side₂_touched_faceLen_three_canonical_swapped
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceLen
      ((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl (face₂Dart₂ data))) = 3 := by
  have h12 :
      tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) (face₂Dart₁ data)
        = face₂Dart₂ data := by
    simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using
      side₂Anchors_trace12 hNT data hsep
  have h21 :
      tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) (face₂Dart₂ data)
        = face₂Dart₁ data := by
    simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using
      side₂Anchors_trace21 hNT data hsep
  have htwo : ProofsInTheBook.ChordFaceFinal.tOrbitCard
      (data.sideAlpha₂ hsep) data.sideSigma₂
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) (face₂Dart₂ data) = 2 :=
    ProofsInTheBook.ChordAnchor.tOrbitCard_eq_two_of_tracePhi_swap
      (data.sideAlpha₂ hsep) data.sideSigma₂ (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      h21 h12 (face₂Dart_distinct hNT data).symm
  have hone : ((if (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
          (face₂Dart₂ data)
          ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
          (face₂Dart₂ data)
          ((data.sideAlpha₂ hsep) (side₂Anchor₀ data hsep)) then 1 else 0)) = 1 := by
    classical
    have hβa₁ :
        data.sideAlpha₂ hsep (side₂Anchor₀ data hsep) = face₂Dart₂ data :=
      sideAlpha₂_anchor₀_eq_face₂Dart₂ hNT data hsep
    have hfirst : ¬
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
            (face₂Dart₂ data) ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) := by
      intro h
      have hpred :
          (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
            ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep))
            ((data.sideAlpha₂ hsep) (side₂Anchor₀ data hsep)) := by
        rw [hβa₁]
        exact h.symm
      exact side₂_chordPred_notSameCycle_canonical_swapped hNT data hsep hpred
    have hsecond :
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
            (face₂Dart₂ data) ((data.sideAlpha₂ hsep) (side₂Anchor₀ data hsep)) := by
      rw [hβa₁]
    rw [if_neg hfirst, if_pos hsecond]
  exact sideMap₂_faceLen_three_of_count hNT data hsep
    (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) (side₂Anchors_ne hNT data hsep).symm
    (face₂Dart₂ data) htwo hone



theorem face₂_rep_touched_canonical_swapped
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂})
    (hface₂ : M.dartFace k.1 = data.face₂) :
    (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl k)
      =
    (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl (face₂Dart₂ data)) := by
  classical
  have hsc : M.φ.SameCycle (M.α data.dart) k.1 := by
    have hf : M.dartFace k.1 = M.dartFace (M.α data.dart) := by
      rw [hface₂]; rfl
    exact (Quotient.exact hf).symm
  rcases ProofsInTheBook.ChordSideClose.face₂_dart_cases data hsc with hk | hk | hk
  · exact False.elim (k.2 (hk ▸ ProofsInTheBook.ChordSideClose.alphaDart_mem_keptDel₂ data))
  · have hk' : k = face₂Dart₁ data := by
      apply Subtype.ext
      exact hk
    rw [hk']
    exact (ProofsInTheBook.ChordBoundaryOrbit.sideFace_inl_eq_iff_tracePhi
      (data.sideAlpha₂ hsep) data.sideSigma₂
      (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
      (side₂Anchors_ne hNT data hsep).symm (face₂Dart₁ data) (face₂Dart₂ data)).2
      ⟨1, by
        rw [zpow_one]
        simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)]
          using side₂Anchors_trace12 hNT data hsep⟩
  · have hk' : k = face₂Dart₂ data := by
      apply Subtype.ext
      exact hk
    rw [hk']



def CanonicalSide₂NonTouchedInnerClassifierSwappedRoot0
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop :=
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  ∀ f : S.Face,
    f ≠ S.dartFace (Sum.inr 0) →
    f ≠ S.dartFace (Sum.inl (face₂Dart₂ data)) →
      ∃ k : {d : D // d ∉ data.keptDel₂},
        S.dartFace (Sum.inl k) = f ∧
        M.dartFace k.1 ∈ data.side₂ ∧
        M.dartFace k.1 ≠ data.face₂ ∧
        ProofsInTheBook.ChordInnerTri.SpliceUntouched
          (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep) k



theorem canonicalSide₂NonTouchedInnerClassifier_swapped_root0_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    CanonicalSide₂NonTouchedInnerClassifierSwappedRoot0 hNT data hsep := by
  classical
  intro f hfOuter hfTouched
  obtain ⟨k, hkf⟩ :=
    sideFace₂_has_inl_rep hNT data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm f
  have hnotOuterM : M.dartFace k.1 ≠ hNT.outerFace := by
    intro hkOuterFace
    have hkKept : k.1 ∈ data.keptSet₂ := (data.mem_keptDel₂_iff k.1).1 k.2
    rcases hkKept.1 with hside | houterArc
    · exact data.side₂_subset_nonouter hside hkOuterFace
    · obtain ⟨i, hi⟩ := outerArc₂_mem_fwdArc_canonical hNT data hsep houterArc
      have H := side₂EndpointBoundaryAlignment_uncond hNT data hsep
      have hTA := canonicalTracePhiArc₂_fwdArc_of_alignment hNT data hsep H.1 H.2
      have hkArc :
          k =
            ⟨(ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i,
              fwdArc_arcDart_notMem_keptDel₂ hNT data hsep i⟩ := by
        apply Subtype.ext
        exact hi
      have hτ :
          (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
            ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k :=
        (hTA.mem_iff k).2 ⟨i, hkArc⟩
      have hτswapped :
          (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
            ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k := by
        simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτ
      have hfaceOuter :
          (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
              (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl k)
            =
          (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
              (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inr 0) :=
        (ProofsInTheBook.ChordBoundaryOrbit.sideFace_eq_chordOrbit0_iff
          (data.sideAlpha₂ hsep) data.sideSigma₂
          (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
          (side₂Anchors_ne hNT data hsep).symm k).2 hτswapped.symm
      exact hfOuter (hkf.symm.trans hfaceOuter)
  have hside : M.dartFace k.1 ∈ data.side₂ :=
    keptDart_face_mem_side₂ hNT data k hnotOuterM
  have hnotFace₂ : M.dartFace k.1 ≠ data.face₂ := by
    intro hkFace₂
    have htouch :
        (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
            (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl k)
          =
        (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
            (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl (face₂Dart₂ data)) :=
      face₂_rep_touched_canonical_swapped hNT data hsep k hkFace₂
    exact hfTouched (hkf.symm.trans htouch)
  have h0 :
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl k)
        ≠
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inr 0) := by
    intro h
    exact hfOuter (hkf.symm.trans h)
  have h1 :
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl k)
        ≠
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inr 1) := by
    intro h
    have htouch :
        (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
            (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl k)
          =
        (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
            (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl (face₂Dart₂ data)) :=
      h.trans (side₂_swapped_inr1_face_eq_face₂Dart₂ hNT data hsep)
    exact hfTouched (hkf.symm.trans htouch)
  refine ⟨k, hkf, hside, hnotFace₂, ?_⟩
  exact ProofsInTheBook.ChordBoundaryOrbit.spliceUntouched_of_face_ne_chordOrbits
    (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
    (side₂Anchors_ne hNT data hsep).symm h0 h1





theorem side₂_inner_tri_of_nonTouchedClassifier_swapped_root0
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hclass : CanonicalSide₂NonTouchedInnerClassifierSwappedRoot0 hNT data hsep) :
    ∀ f : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).Face,
      f ≠ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inr 0) →
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceLen f = 3 := by
  intro f hf
  by_cases hf₀ :
      f = (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inl (face₂Dart₂ data))
  · rw [hf₀]
    exact side₂_touched_faceLen_three_canonical_swapped hNT data hsep
  · obtain ⟨k, hkf, hside, hface₂, huntouched⟩ := hclass f hf hf₀
    rw [← hkf]
    exact sideMap₂_faceLen_inl_three_of_side₂ hNT data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm k hside hface₂ huntouched

theorem side₂_inner_tri_canonical_swapped_root0_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ f : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).Face,
      f ≠ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm).dartFace (Sum.inr 0) →
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceLen f = 3 :=
  side₂_inner_tri_of_nonTouchedClassifier_swapped_root0 hNT data hsep
    (canonicalSide₂NonTouchedInnerClassifier_swapped_root0_uncond hNT data hsep)



noncomputable def contiguousInterval₂_direct_canonical_swapped_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ZinanCh35Side2.ContiguousInterval₂ data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm := by
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  have H := side₂EndpointBoundaryAlignment_uncond hNT data hsep
  have hd :
      ProofsInTheBook.ZinanCh35Contiguous.Side₂ChordIncidenceNonDegenerate data hsep
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep) :=
    side₂ChordIncidenceNonDegenerate_canonical hNT data hsep H.1 H.2
  have hlen : 3 ≤ (S.faceDartList (Sum.inr 0)).length := by
    change 3 ≤ ((freshMap (data.sideAlpha₂ hsep) data.sideSigma₂
      (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)).length
    exact freshMap_outerLen_zero_ge_three
      (data.sideAlpha₂ hsep) data.sideSigma₂
      (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)
      (side₂Anchors_ne hNT data hsep).symm hd
  exact ProofsInTheBook.ZinanCh35Side2.contiguousInterval₂_of_nearTriangulation data hsep
    (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
    (ProofsInTheBook.ZinanCh35BoundaryAssembler.nearTriangulation_of_explicit_boundary_classification
      S
      (side₂_isSphereMap_canonical_swapped_uncond hNT data hsep)
      (sideMap₂_isSimpleGraph_canonical_swapped hNT data hsep)
      (S.dartFace (Sum.inr 0)) (Sum.inr 0) rfl
      (side₂_outer_simple_canonical_swapped_root0_uncond hNT data hsep)
      hlen
      (side₂_inner_tri_canonical_swapped_root0_uncond hNT data hsep))



variable {α : Type u} [DecidableEq α]

/-- Canonical side-1 `Side₁InputsNoConf`, with only the Thomassen recursion fuel left as input.
This threads the closed canonical `ContiguousInterval`, canonical share-face, chord adjacency,
endpoint equations, and `OuterDartArc₁`; it does not solve the supplier's universal-arbitrary
anchor quantifier. -/
noncomputable def canonicalSide₁InputsNoConf_of_fuel
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) (L : M.Vertex → Finset α)
    (htu : M.tail data.dart = u) (hhv : M.head data.dart = v)
    (pₛ qₛ :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).Vertex)
    (cpₛ cqₛ : α)
    (hLₛ : ProofsInTheBook.ThomassenLists.CombMap.ThomassenLists
      (ProofsInTheBook.ChordSideNT.chordSideNearTriangulation_of_share data hsep
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
        (side₁AnchorsShareFace_canonical data hsep)
        (contiguousInterval₁_direct_canonical_uncond hNT data hsep))
      pₛ qₛ
      (fun x => L (ProofsInTheBook.ChordReconClose.sideVertexToM₁ data hsep
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) x))
      cpₛ cqₛ) :
    ProofsInTheBook.ZinanCh35ChordBranch.Side₁InputsNoConf data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) L where
  ci := contiguousInterval₁_direct_canonical_uncond hNT data hsep
  hshare := side₁AnchorsShareFace_canonical data hsep
  hchord := by
    have h0 := ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₀_tail data hsep
    have h1 := ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₁_tail data hsep
    simpa [h0, h1, htu, hhv] using (ProofsInTheBook.ChordContiguous.chordChoice_adj data).2
  ha₀ := (ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₀_tail data hsep).trans htu
  ha₁ := (ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₁_tail data hsep).trans hhv
  pₛ := pₛ
  qₛ := qₛ
  cpₛ := cpₛ
  cqₛ := cqₛ
  hLₛ := hLₛ
  houter := ProofsInTheBook.ZinanCh35EdgeCoreFinal.outerDartArc₁_uncond data hsep



/-- Canonical side-2 `Side₂InputsNoConf` in the standard chord endpoint order.  The canonical
side-2 anchors realize this order only after swapping the fresh insertion order, so this constructor
threads the swapped `ContiguousInterval₂`. -/
noncomputable def canonicalSide₂InputsNoConf_of_fuel
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) (L : M.Vertex → Finset α)
    (htu : M.tail data.dart = u) (hhv : M.head data.dart = v)
    (pₛ qₛ :
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).Vertex)
    (cpₛ cqₛ : α)
    (hLₛ : ProofsInTheBook.ThomassenLists.CombMap.ThomassenLists
      (ProofsInTheBook.ZinanCh35Side2.chordSideNearTriangulation₂_of_share data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm
        (ProofsInTheBook.ChordSideClose.side₂IsDisk_unconditional data hsep)
        (side₂AnchorsShareFace_canonical_swapped (hNT := hNT) data hsep)
        (contiguousInterval₂_direct_canonical_swapped_uncond hNT data hsep))
      pₛ qₛ
      (fun x => L (ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm x))
      cpₛ cqₛ) :
    ProofsInTheBook.ZinanCh35ChordBranch.Side₂InputsNoConf data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm L where
  hdisk := ProofsInTheBook.ChordSideClose.side₂IsDisk_unconditional data hsep
  hshare := side₂AnchorsShareFace_canonical_swapped (hNT := hNT) data hsep
  ci := contiguousInterval₂_direct_canonical_swapped_uncond hNT data hsep
  hchord := by
    have h0 := canonicalSide₂Anchor₁_tail hNT data hsep
    have h1 := canonicalSide₂Anchor₀_tail hNT data hsep
    simpa [h0, h1, htu, hhv] using (ProofsInTheBook.ChordContiguous.chordChoice_adj data).2
  ha₀ := (canonicalSide₂Anchor₁_tail hNT data hsep).trans htu
  ha₁ := (canonicalSide₂Anchor₀_tail hNT data hsep).trans hhv
  pₛ := pₛ
  qₛ := qₛ
  cpₛ := cpₛ
  cqₛ := cqₛ
  hLₛ := hLₛ

/-- Canonical `ChordBranchResidualData` producer with only the genuine recursion fuel left explicit:
precolored placement in side 1 and the two side Thomassen-list inputs. -/
noncomputable def canonicalChordBranchResidualData_of_fuel
    {h : hNT.outerCycle.Chord u v} {p q : M.Vertex}
    (L : M.Vertex → Finset α) (cp cq : α)
    (htu : M.tail (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h).dart = u)
    (hhv : M.head (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h).dart = v)
    (hp : p ∈ ProofsInTheBook.ChordReconClose.sideRegion₁
      (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h))
    (hq : q ∈ ProofsInTheBook.ChordReconClose.sideRegion₁
      (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h))
    (p₁ q₁ :
      ((ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h).sideMap₁
        (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)
        (side₁Anchor₀ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₁Anchor₁ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₁Anchors_ne (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))).Vertex)
    (cp₁ cq₁ : α)
    (hL₁ : ProofsInTheBook.ThomassenLists.CombMap.ThomassenLists
      (ProofsInTheBook.ChordSideNT.chordSideNearTriangulation_of_share
        (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
        (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)
        (side₁Anchor₀ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₁Anchor₁ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₁Anchors_ne (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₁AnchorsShareFace_canonical
          (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (contiguousInterval₁_direct_canonical_uncond hNT
          (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)))
      p₁ q₁
      (fun x => L (ProofsInTheBook.ChordReconClose.sideVertexToM₁
        (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
        (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)
        (side₁Anchor₀ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₁Anchor₁ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₁Anchors_ne (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)) x))
      cp₁ cq₁)
    (p₂ q₂ : ∀ c₁ : M.Vertex → α, c₁ u ≠ c₁ v →
      ((ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h).sideMap₂
        (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)
        (side₂Anchor₁ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₂Anchor₀ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
        (side₂Anchors_ne hNT
          (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)).symm).Vertex)
    (cp₂ cq₂ : ∀ c₁ : M.Vertex → α, c₁ u ≠ c₁ v → α)
    (hL₂ : ∀ (c₁ : M.Vertex → α) (hcuv : c₁ u ≠ c₁ v),
      ProofsInTheBook.ThomassenLists.CombMap.ThomassenLists
        (ProofsInTheBook.ZinanCh35Side2.chordSideNearTriangulation₂_of_share
          (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
          (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)
          (side₂Anchor₁ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
            (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
          (side₂Anchor₀ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
            (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
          (side₂Anchors_ne hNT
            (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
            (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)).symm
          (ProofsInTheBook.ChordSideClose.side₂IsDisk_unconditional
            (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
            (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
          (side₂AnchorsShareFace_canonical_swapped (hNT := hNT)
            (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
            (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
          (contiguousInterval₂_direct_canonical_swapped_uncond hNT
            (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
            (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)))
        (p₂ c₁ hcuv) (q₂ c₁ hcuv)
        (fun x =>
          (ProofsInTheBook.ZinanCh35ChordResidue.chordSplitRegions_of_residue
            (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
            (ProofsInTheBook.ZinanCh35ChordResidue.normSep h) htu hhv
            (ProofsInTheBook.ZinanCh35Regions.chordSplitRegionsResidue_of_precolored
              (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
              (ProofsInTheBook.ZinanCh35ChordResidue.normSep h) hp hq)
            (L := L) (cp := cp) (cq := cq)).forcedLists c₁ L
            (ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂
              (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
              (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)
              (side₂Anchor₁ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
                (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
              (side₂Anchor₀ (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
                (ProofsInTheBook.ZinanCh35ChordResidue.normSep h))
              (side₂Anchors_ne hNT
                (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h)
                (ProofsInTheBook.ZinanCh35ChordResidue.normSep h)).symm x))
        (cp₂ c₁ hcuv) (cq₂ c₁ hcuv)) :
    ProofsInTheBook.ZinanCh35ChordBranch.ChordBranchResidualData h p q L cp cq := by
  let data := ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h
  let hsep := ProofsInTheBook.ZinanCh35ChordResidue.normSep h
  let res := ProofsInTheBook.ZinanCh35Regions.chordSplitRegionsResidue_of_precolored data hsep hp hq
  let regions := ProofsInTheBook.ZinanCh35ChordResidue.chordSplitRegions_of_residue
    data hsep htu hhv res (L := L) (cp := cp) (cq := cq)
  refine
    { hsep := hsep
      htu := htu
      hhv := hhv
      regions := regions
      regions_s₁ := rfl
      regions_s₂ := rfl
      a₁₀ := side₁Anchor₀ data hsep
      a₁₁ := side₁Anchor₁ data hsep
      ha₁₀ := (ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₀_tail data hsep).trans htu
      ha₁₁ := (ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₁_tail data hsep).trans hhv
      hne₁ := side₁Anchors_ne data hsep
      side₁ := canonicalSide₁InputsNoConf_of_fuel hNT data hsep L htu hhv p₁ q₁ cp₁ cq₁ hL₁
      a₂₀ := side₂Anchor₁ data hsep
      a₂₁ := side₂Anchor₀ data hsep
      ha₂₀ := (canonicalSide₂Anchor₁_tail hNT data hsep).trans htu
      ha₂₁ := (canonicalSide₂Anchor₀_tail hNT data hsep).trans hhv
      hne₂ := (side₂Anchors_ne hNT data hsep).symm
      side₂ := fun c₁ hcuv =>
        canonicalSide₂InputsNoConf_of_fuel hNT data hsep (regions.forcedLists c₁ L)
          htu hhv (p₂ c₁ hcuv) (q₂ c₁ hcuv) (cp₂ c₁ hcuv) (cq₂ c₁ hcuv)
          (hL₂ c₁ hcuv)
      uv_ne := by
        intro huv
        have hne := ProofsInTheBook.ChordSigmaContig.u_ne_v data
        exact hne (by rw [htu, hhv, huv]) }

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

theorem boundaryCycle_head_mem_vertices_of_mem_darts
    {f : M.Face} (C : BoundaryCycle M f) {d : D} (hd : d ∈ C.darts) :
    C.IsBoundaryVertex (M.head d) := by
  classical
  rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq]
  rw [List.mem_iff_getElem] at hd
  obtain ⟨n, hn, hdget⟩ := hd
  set i : Fin C.darts.length := ⟨n, hn⟩ with hi
  have hnext := C.consecutive_vertex i
  have hdi : C.darts.get i = d := by
    rw [List.get_eq_getElem]
    exact hdget
  rw [hdi] at hnext
  rw [← hnext]
  exact List.mem_map_of_mem (List.get_mem C.darts (cyclicNext C.normalized.length_pos i))

theorem boundaryCycle_tail_mem_vertices_of_mem_darts
    {f : M.Face} (C : BoundaryCycle M f) {d : D} (hd : d ∈ C.darts) :
    C.IsBoundaryVertex (M.tail d) := by
  rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq]
  exact List.mem_map_of_mem hd





@[simp] lemma sideVertexToM₁_tail_inl_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁}) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        ((data.sideMap₁ hsep a₀ a₁ hne).tail (Sum.inl k))
      = M.tail k.1 := by
  exact sideVertexToM₁_inl data hsep a₀ a₁ hne k

@[simp] lemma sideVertexToM₁_head_inl_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁}) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        ((data.sideMap₁ hsep a₀ a₁ hne).head (Sum.inl k))
      = M.head k.1 := by
  exact ProofsInTheBook.ChordReconClose.sideVertexToM₁_head_inl data hsep a₀ a₁ hne k



@[simp] lemma sideVertexToM₁_tail_inr_one_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        ((data.sideMap₁ hsep a₀ a₁ hne).tail (Sum.inr (1 : Fin 2)))
      = M.tail a₁.1 := by
  simpa using ProofsInTheBook.ZinanCh35Iota.sideVertexToM₁_tail_inr data hsep a₀ a₁ hne
    (1 : Fin 2)

/-- The canonical side-1 near-triangulation used by the recursion supplier. -/
noncomputable def canonicalSide₁NT (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    NearTriangulation
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)) :=
  ProofsInTheBook.ChordSideNT.chordSideNearTriangulation_of_share data hsep
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
    (side₁AnchorsShareFace_canonical data hsep)
    (ProofsInTheBook.ZinanCh35OuterTraceProof.contiguousInterval₁_direct_canonical_uncond
      hNT data hsep)

@[simp] theorem canonicalSide₁NT_outerCycle_darts
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.darts =
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1) :=
  rfl

theorem canonicalSide₁_boundary_tail_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)) :
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
      ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).tail x) := by
  rw [BoundaryCycle.IsBoundaryVertex,
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.vertices_eq]
  exact List.mem_map_of_mem hx

theorem canonicalSide₁_boundary_edge_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)) :
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
      ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartEdge x) := by
  rw [BoundaryCycle.IsBoundaryEdge,
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.edges_eq]
  exact List.mem_map_of_mem hx

theorem canonicalSide₁_boundary_head_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)) :
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
      ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).head x) := by
  exact boundaryCycle_head_mem_vertices_of_mem_darts
    ((canonicalSide₁NT (hNT := hNT) data hsep).outerCycle)
    (by simpa [canonicalSide₁NT_outerCycle_darts (hNT := hNT) data hsep] using hx)

theorem canonicalSide₁_preedge_outerArc_lift
    {α : Type u} [DecidableEq α] {h : hNT.outerCycle.Chord u v}
    {L : M.Vertex → Finset α} {cp cq : α}
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v)
    (hTL : ThomassenLists hNT p q L cp cq)
    (hp : p ∈ sideRegion₁ (normalizedChordSplitData h))
    (hq : q ∈ sideRegion₁ (normalizedChordSplitData h)) :
    ∃ b : D, b ∈ (normalizedChordSplitData h).outerArc₁ ∧ M.dartEdge b = s(p, q) := by
  classical
  let data := normalizedChordSplitData h
  have hpq := hTL.pq_boundary_edge
  rw [BoundaryCycle.IsBoundaryEdge, hNT.outerCycle.edges_eq, List.mem_map] at hpq
  obtain ⟨b, hbC, hedge⟩ := hpq
  have hface : M.dartFace b = hNT.outerFace := (hNT.outerCycle.mem_darts_iff b).mp hbC
  have hchord : M.dartEdge b ≠ s(u, v) := by
    intro hbuv
    apply h.not_boundary_edge
    rw [BoundaryCycle.IsBoundaryEdge, hNT.outerCycle.edges_eq, List.mem_map]
    exact ⟨b, hbC, hbuv⟩
  have htailhead : M.tail b ∈ sideRegion₁ data ∧ M.head b ∈ sideRegion₁ data := by
    have hedge' : (s(M.tail b, M.head b) : Sym2 M.Vertex) = s(p, q) := hedge
    rcases Sym2.eq_iff.mp hedge' with ⟨htp, hhq⟩ | ⟨htq, hhp⟩
    · exact ⟨htp ▸ hp, hhq ▸ hq⟩
    · exact ⟨htq ▸ hq, hhp ▸ hp⟩
  have hrev : M.dartFace (M.α b) ∈ data.side₁ :=
    ProofsInTheBook.ZinanCh35EdgeCoreFinal.outerDartArc₁_uncond data hsep
      hchord hface htailhead.1 htailhead.2
  exact ⟨b, ⟨hface, hrev⟩, hedge⟩

theorem canonicalSide₁_faceDartList_mem_of_outerArc₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hk : k.1 ∈ data.outerArc₁) :
    (Sum.inl k : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) ∈
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1) := by
  classical
  obtain ⟨i, hi⟩ :=
    ProofsInTheBook.ZinanCh35OuterTraceProof.outerArc₁_mem_bwdArc_canonical
      hNT data hsep hk
  have hTA :=
    ProofsInTheBook.ZinanCh35OuterTraceProof.canonicalTracePhiArc_bwdArc_uncond
      hNT data hsep
  have hkArc :
      k =
        ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i,
          ProofsInTheBook.ZinanCh35OuterTraceProof.bwdArc_arcDart_notMem_keptDel₁
            hNT data hsep i⟩ := by
    apply Subtype.ext
    exact hi
  have hτ :
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) k :=
    (hTA.mem_iff k).2 ⟨i, hkArc⟩
  exact (ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_side₁_outer_orbit_mem_iff
    hNT data hsep (Sum.inl k)).2 (Or.inr ⟨k, rfl, hτ⟩)



theorem canonicalSide₁_boundary_vertex_parent_boundary
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hhv : M.head data.dart = v)
    (W : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).Vertex)
    (hW : (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W) :
    hNT.outerCycle.IsBoundaryVertex
      (sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep) W) := by
  classical
  rw [BoundaryCycle.IsBoundaryVertex,
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.vertices_eq,
    canonicalSide₁NT_outerCycle_darts (hNT := hNT) data hsep] at hW
  rw [List.mem_map] at hW
  obtain ⟨x, hx, hxW⟩ := hW
  rcases (ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_side₁_outer_orbit_mem_iff
      hNT data hsep x).1 hx with hroot | ⟨k, hxk, hτ⟩
  · rw [← hxW, hroot]
    rw [sideVertexToM₁_tail_inr_one_apply]
    rw [ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₁_tail data hsep, hhv]
    exact data.chord.right_boundary
  · have hTA :=
      ProofsInTheBook.ZinanCh35OuterTraceProof.canonicalTracePhiArc_bwdArc_uncond
        hNT data hsep
    rcases (hTA.mem_iff k).1 hτ with ⟨i, hk⟩
    rw [← hxW, hxk]
    rw [sideVertexToM₁_tail_inl_apply]
    rw [hk]
    exact boundaryCycle_tail_mem_vertices_of_mem_darts hNT.outerCycle
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary i)

theorem bwdArc_arcDart_mem_outerArc₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (i : Fin (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).len) :
    (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i ∈ data.outerArc₁ := by
  constructor
  · exact (hNT.outerCycle.mem_darts_iff _).mp
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary i)
  · exact ProofsInTheBook.ZinanCh35ArcSide.bwdArc_reverse_face_mem_side₁ data i

theorem canonicalSide₁_boundary_of_outerArc_tail_eq
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).Vertex}
    {b : D} (hb : b ∈ data.outerArc₁)
    (htail : M.tail b =
      sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep) W) :
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let k : {d : D // d ∉ data.keptDel₁} :=
    ⟨b, ProofsInTheBook.ChordSideClose.outerArc_notMem_keptDel₁ data hb.1 hb.2⟩
  let Wb : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).Vertex :=
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).tail (Sum.inl k)
  have hWb :
      (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex Wb :=
    canonicalSide₁_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep
      (canonicalSide₁_faceDartList_mem_of_outerArc₁ (hNT := hNT) data hsep k hb)
  have hι :
      sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep) Wb =
        sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep) W := by
    dsimp [Wb, k]
    rw [sideVertexToM₁_tail_inl_apply]
    exact htail
  have hEq : Wb = W :=
    ProofsInTheBook.ZinanCh35Iota.sideVertexToM₁_injective_canonical data hsep (side₁Anchor₀ data hsep)
      (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) hι
  simpa [hEq] using hWb

theorem canonicalSide₁_boundary_of_parent_eq_tail
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).Vertex}
    (htu : M.tail data.dart = u)
    (hW : sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep) W = u) :
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  let i := (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx
  exact canonicalSide₁_boundary_of_outerArc_tail_eq (hNT := hNT) data hsep
    (bwdArc_arcDart_mem_outerArc₁ (hNT := hNT) data hsep i) (by
      rw [(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).tail_firstIdx, M.head_alpha, htu, hW])

theorem canonicalSide₁_boundary_of_parent_eq_head
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).Vertex}
    (hhv : M.head data.dart = v)
    (hW : sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep) W = v) :
    (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let S := data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)
  let Wb : S.Vertex := S.tail (Sum.inr (1 : Fin 2))
  have hx : (Sum.inr (1 : Fin 2) :
      {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) ∈ S.faceDartList (Sum.inr 1) :=
    (ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_side₁_outer_orbit_mem_iff
      hNT data hsep (Sum.inr (1 : Fin 2))).2 (Or.inl rfl)
  have hWb :
      (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex Wb :=
    canonicalSide₁_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hι :
      sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep) Wb =
        sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep) W := by
    dsimp [Wb, S]
    rw [sideVertexToM₁_tail_inr_one_apply,
      ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₁_tail data hsep, hhv, hW]
  have hEq : Wb = W :=
    ProofsInTheBook.ZinanCh35Iota.sideVertexToM₁_injective_canonical data hsep (side₁Anchor₀ data hsep)
      (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) hι
  simpa [hEq] using hWb

theorem canonicalSide₁_parent_boundary_vertex_side_boundary_normalized
    {h : hNT.outerCycle.Chord u v}
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v)
    (W : ((normalizedChordSplitData h).sideMap₁ hsep
      (side₁Anchor₀ (normalizedChordSplitData h) hsep)
      (side₁Anchor₁ (normalizedChordSplitData h) hsep)
      (side₁Anchors_ne (normalizedChordSplitData h) hsep)).Vertex)
    (hparent : hNT.outerCycle.IsBoundaryVertex
      (sideVertexToM₁ (normalizedChordSplitData h) hsep
        (side₁Anchor₀ (normalizedChordSplitData h) hsep)
        (side₁Anchor₁ (normalizedChordSplitData h) hsep)
        (side₁Anchors_ne (normalizedChordSplitData h) hsep) W)) :
    (canonicalSide₁NT (hNT := hNT) (normalizedChordSplitData h) hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let data := normalizedChordSplitData h
  let ι := sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)
  have hWside : ι W ∈ sideRegion₁ data :=
    sideVertexToM₁_mem data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep) W
  have hparentι : hNT.outerCycle.IsBoundaryVertex (ι W) := by
    simpa [ι, data] using hparent
  let R := normalizedRuns h
  rcases R.covering hparentι with hUV | hVU | hWu | hWv
  · obtain ⟨i, hi⟩ := hUV
    have hB : M.dartFace (M.α ((ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcUV htu.symm hhv.symm).symm i))) ∈ data.side₁ :=
      bwdRun_reverse_face_mem_side₁ data (ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm)
        (by rw [ZinanCh35Aligned.daCast_len]; exact R.lenUV) _
    have hsame : (ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcUV htu.symm hhv.symm).symm i)
          = R.arcUV.arcDart i := by
      rw [ZinanCh35Aligned.daCast_arcDart_eq]; congr 1
    rw [hsame] at hB
    have hb : R.arcUV.arcDart i ∈ data.outerArc₁ := by
      constructor
      · exact (hNT.outerCycle.mem_darts_iff _).mp (R.arcUV.boundary i)
      · exact hB
    exact canonicalSide₁_boundary_of_outerArc_tail_eq (hNT := hNT) data hsep hb (by
      simpa [ι] using hi)
  · obtain ⟨i, hi⟩ := hVU
    have hF : M.dartFace (M.α ((ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcVU hhv.symm htu.symm).symm i))) ∈ data.side₂ :=
      fwdRun_reverse_face_mem_side₂ data (ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm)
        (by rw [ZinanCh35Aligned.daCast_len]; exact R.lenVU) _
    have hsame : (ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcVU hhv.symm htu.symm).symm i)
          = R.arcVU.arcDart i := by
      rw [ZinanCh35Aligned.daCast_arcDart_eq]; congr 1
    rw [hsame] at hF
    have hchord : M.dartEdge (R.arcVU.arcDart i) ≠ s(u, v) := by
      intro he
      apply h.not_boundary_edge
      rw [← he]
      show M.dartEdge (R.arcVU.arcDart i) ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]
      exact List.mem_map_of_mem (R.arcVU.boundary i)
    have hWside₂ : ι W ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data := by
      have := ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.dartRun_tail_mem_sideRegion₂_of_face
        data hsep hchord hF
      rw [hi] at this
      exact this
    rcases ProofsInTheBook.ZinanCh35StarConn.sideRegionInterChordEnds_holds data hsep hWside hWside₂ with hWu' | hWv'
    · exact canonicalSide₁_boundary_of_parent_eq_tail (hNT := hNT) data hsep (W := W) htu (by
        simpa [ι] using hWu')
    · exact canonicalSide₁_boundary_of_parent_eq_head (hNT := hNT) data hsep (W := W) hhv (by
        simpa [ι] using hWv')
  · exact canonicalSide₁_boundary_of_parent_eq_tail (hNT := hNT) data hsep (W := W) htu (by
      simpa [ι] using hWu)
  · exact canonicalSide₁_boundary_of_parent_eq_head (hNT := hNT) data hsep (W := W) hhv (by
      simpa [ι] using hWv)

theorem canonicalSide₁ThomassenLists_of_lifted_preedge_normalized
    {α : Type u} [DecidableEq α] {h : hNT.outerCycle.Chord u v}
    {L : M.Vertex → Finset α} {cp cq : α}
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v)
    (hTL : ThomassenLists hNT p q L cp cq)
    (pₛ qₛ : ((normalizedChordSplitData h).sideMap₁ hsep
      (side₁Anchor₀ (normalizedChordSplitData h) hsep)
      (side₁Anchor₁ (normalizedChordSplitData h) hsep)
      (side₁Anchors_ne (normalizedChordSplitData h) hsep)).Vertex)
    (hpmap : sideVertexToM₁ (normalizedChordSplitData h) hsep
        (side₁Anchor₀ (normalizedChordSplitData h) hsep)
        (side₁Anchor₁ (normalizedChordSplitData h) hsep)
        (side₁Anchors_ne (normalizedChordSplitData h) hsep) pₛ = p)
    (hqmap : sideVertexToM₁ (normalizedChordSplitData h) hsep
        (side₁Anchor₀ (normalizedChordSplitData h) hsep)
        (side₁Anchor₁ (normalizedChordSplitData h) hsep)
        (side₁Anchors_ne (normalizedChordSplitData h) hsep) qₛ = q)
    (hpbd : (canonicalSide₁NT (hNT := hNT) (normalizedChordSplitData h) hsep).outerCycle.IsBoundaryVertex pₛ)
    (hqbd : (canonicalSide₁NT (hNT := hNT) (normalizedChordSplitData h) hsep).outerCycle.IsBoundaryVertex qₛ)
    (hpqbd : (canonicalSide₁NT (hNT := hNT) (normalizedChordSplitData h) hsep).outerCycle.IsBoundaryEdge s(pₛ, qₛ)) :
    ThomassenLists
      (canonicalSide₁NT (hNT := hNT) (normalizedChordSplitData h) hsep)
      pₛ qₛ
      (fun x => L (sideVertexToM₁ (normalizedChordSplitData h) hsep
        (side₁Anchor₀ (normalizedChordSplitData h) hsep)
        (side₁Anchor₁ (normalizedChordSplitData h) hsep)
        (side₁Anchors_ne (normalizedChordSplitData h) hsep) x))
      cp cq := by
  classical
  let data := normalizedChordSplitData h
  let S := data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)
  let ι := sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)
  refine
    { p_boundary := hpbd
      q_boundary := hqbd
      pq_boundary_edge := hpqbd
      colors_ne := hTL.colors_ne
      list_p := ?_
      list_q := ?_
      boundary_ge_three := ?_
      interior_ge_five := ?_ }
  · simpa [ι, data, hpmap] using hTL.list_p
  · simpa [ι, data, hqmap] using hTL.list_q
  · intro W hW hWp hWq
    have hparent :
        hNT.outerCycle.IsBoundaryVertex
          (sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep) W) :=
      canonicalSide₁_boundary_vertex_parent_boundary (hNT := hNT) data hsep hhv W hW
    have hWp_parent :
        sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep) W ≠ p := by
      intro hιp
      have hEq : W = pₛ :=
        (ProofsInTheBook.ZinanCh35Iota.sideVertexToM₁_injective_canonical data hsep
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)) (hιp.trans hpmap.symm)
      exact hWp hEq
    have hWq_parent :
        sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep) W ≠ q := by
      intro hιq
      have hEq : W = qₛ :=
        (ProofsInTheBook.ZinanCh35Iota.sideVertexToM₁_injective_canonical data hsep
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)) (hιq.trans hqmap.symm)
      exact hWq hEq
    simpa [ι, data] using hTL.boundary_ge_three
      (sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep) W) hparent hWp_parent hWq_parent
  · intro W hWint
    have hparentInt :
        ¬ hNT.outerCycle.IsBoundaryVertex
          (sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep) W) := by
      intro hparent
      exact hWint
        (canonicalSide₁_parent_boundary_vertex_side_boundary_normalized
          (hNT := hNT) (h := h) hsep htu hhv W (by simpa [data] using hparent))
    simpa [ι, data] using hTL.interior_ge_five
      (sideVertexToM₁ data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep) W) hparentInt

theorem canonicalSide₁ThomassenLists_exists_normalized
    {α : Type u} [DecidableEq α] {h : hNT.outerCycle.Chord u v}
    {L : M.Vertex → Finset α} {cp cq : α}
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v)
    (hTL : ThomassenLists hNT p q L cp cq)
    (hp : p ∈ sideRegion₁ (normalizedChordSplitData h))
    (hq : q ∈ sideRegion₁ (normalizedChordSplitData h)) :
    ∃ pₛ qₛ : ((normalizedChordSplitData h).sideMap₁ hsep
        (side₁Anchor₀ (normalizedChordSplitData h) hsep)
        (side₁Anchor₁ (normalizedChordSplitData h) hsep)
        (side₁Anchors_ne (normalizedChordSplitData h) hsep)).Vertex,
      ThomassenLists
        (canonicalSide₁NT (hNT := hNT) (normalizedChordSplitData h) hsep)
        pₛ qₛ
        (fun x => L (sideVertexToM₁ (normalizedChordSplitData h) hsep
          (side₁Anchor₀ (normalizedChordSplitData h) hsep)
          (side₁Anchor₁ (normalizedChordSplitData h) hsep)
          (side₁Anchors_ne (normalizedChordSplitData h) hsep) x))
        cp cq := by
  classical
  let data := normalizedChordSplitData h
  let S := data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep)
  obtain ⟨b, hb, hedge⟩ :=
    canonicalSide₁_preedge_outerArc_lift (hNT := hNT) (h := h)
      hsep htu hhv hTL hp hq
  let k : {d : D // d ∉ data.keptDel₁} :=
    ⟨b, ProofsInTheBook.ChordSideClose.outerArc_notMem_keptDel₁ data hb.1 hb.2⟩
  have hx : (Sum.inl k : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) ∈ S.faceDartList (Sum.inr 1) :=
    canonicalSide₁_faceDartList_mem_of_outerArc₁ (hNT := hNT) data hsep k hb
  have htailbd :
      (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
        (S.tail (Sum.inl k)) :=
    canonicalSide₁_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hheadbd :
      (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
        (S.head (Sum.inl k)) :=
    canonicalSide₁_boundary_head_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hedgeSide :
      (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
        (S.dartEdge (Sum.inl k)) :=
    canonicalSide₁_boundary_edge_of_faceDartList_mem (hNT := hNT) data hsep hx
  rcases Sym2.eq_iff.mp (show (s(M.tail b, M.head b) : Sym2 M.Vertex) = s(p, q) from hedge) with
    ⟨htp, hhq⟩ | ⟨htq, hhp⟩
  · refine ⟨S.tail (Sum.inl k), S.head (Sum.inl k), ?_⟩
    exact canonicalSide₁ThomassenLists_of_lifted_preedge_normalized
      (hNT := hNT) (h := h) hsep htu hhv hTL
      (S.tail (Sum.inl k)) (S.head (Sum.inl k))
      (by dsimp [S, k, data]; rw [sideVertexToM₁_tail_inl_apply, htp])
      (by
        dsimp [S, k, data]
        rw [sideVertexToM₁_head_inl_apply, hhq])
      htailbd hheadbd
      (by simpa [S] using hedgeSide)
  · refine ⟨S.head (Sum.inl k), S.tail (Sum.inl k), ?_⟩
    exact canonicalSide₁ThomassenLists_of_lifted_preedge_normalized
      (hNT := hNT) (h := h) hsep htu hhv hTL
      (S.head (Sum.inl k)) (S.tail (Sum.inl k))
      (by
        dsimp [S, k, data]
        rw [sideVertexToM₁_head_inl_apply, hhp])
      (by dsimp [S, k, data]; rw [sideVertexToM₁_tail_inl_apply, htq])
      hheadbd htailbd
      (by
        rw [Sym2.eq_swap]
        change (canonicalSide₁NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
          (S.dartEdge (Sum.inl k))
        exact hedgeSide)



@[simp] theorem normalizedChordSplitData_dart_tail (h : hNT.outerCycle.Chord u v) :
    M.tail (normalizedChordSplitData h).dart = u := by
  simpa [normalizedChordSplitData, ChordSplitData.dart] using hNT.chordDart_tail h

@[simp] theorem normalizedChordSplitData_dart_head (h : hNT.outerCycle.Chord u v) :
    M.head (normalizedChordSplitData h).dart = v := by
  simpa [normalizedChordSplitData, ChordSplitData.dart] using hNT.chordDart_head h

theorem normalizedChordSplitData_chord_symm_dart
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).dart =
      M.α (normalizedChordSplitData h).dart := by
  let d := (normalizedChordSplitData h).dart
  let d' := (normalizedChordSplitData (chord_symm h)).dart
  have ht : M.tail d = u := normalizedChordSplitData_dart_tail h
  have hh : M.head d = v := normalizedChordSplitData_dart_head h
  have ht' : M.tail d' = v := normalizedChordSplitData_dart_tail (chord_symm h)
  have hh' : M.head d' = u := normalizedChordSplitData_dart_head (chord_symm h)
  have hsame : M.α.SameCycle d' d :=
    M.alpha_sameCycle_of_same_endpoints_symm hNT.simpleGraph (ht'.trans hh.symm) (hh'.trans ht.symm)
  rcases (M.alpha_sameCycle_iff d' d).mp hsame with hsame_d | hα
  · exfalso
    exact h.endpoints_ne (ht.symm.trans (hsame_d.symm ▸ ht'))
  · change d' = M.α d
    calc
      d' = M.α (M.α d') := by rw [M.alpha_alpha]
      _ = M.α d := by rw [← hα]

theorem chordSplitAdj_swap_iff {f g : M.Face} :
    hNT.ChordSplitAdj v u f g ↔ hNT.ChordSplitAdj u v f g := by
  constructor
  · rintro ⟨d, hdf, hdg, hb, hch⟩
    refine ⟨d, hdf, hdg, hb, ?_⟩
    rwa [Sym2.eq_swap]
  · rintro ⟨d, hdf, hdg, hb, hch⟩
    refine ⟨d, hdf, hdg, hb, ?_⟩
    rwa [Sym2.eq_swap]

theorem normalizedChordSplitData_chord_symm_face₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).face₁ =
      (normalizedChordSplitData h).face₂ := by
  unfold ChordSplitData.face₁ ChordSplitData.face₂
  rw [normalizedChordSplitData_chord_symm_dart]



theorem normalizedChordSplitData_chord_symm_side₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).side₁ =
      (normalizedChordSplitData h).side₂ := by
  ext f
  constructor
  · intro hf
    change Relation.ReflTransGen (hNT.ChordSplitAdj v u)
      (normalizedChordSplitData (chord_symm h)).face₁ f at hf
    rw [normalizedChordSplitData_chord_symm_face₁ h] at hf
    exact hf.mono (fun _ _ hstep => (chordSplitAdj_swap_iff (hNT := hNT)).1 hstep)
  · intro hf
    change Relation.ReflTransGen (hNT.ChordSplitAdj u v)
      (normalizedChordSplitData h).face₂ f at hf
    rw [← normalizedChordSplitData_chord_symm_face₁ h] at hf
    exact hf.mono (fun _ _ hstep => (chordSplitAdj_swap_iff (hNT := hNT)).2 hstep)

theorem normalizedChordSplitData_chord_symm_sideDarts₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).sideDarts₁ =
      (normalizedChordSplitData h).sideDarts₂ := by
  ext d
  change M.dartFace d ∈ (normalizedChordSplitData (chord_symm h)).side₁ ↔
    M.dartFace d ∈ (normalizedChordSplitData h).side₂
  rw [normalizedChordSplitData_chord_symm_side₁ h]

theorem normalizedChordSplitData_chord_symm_outerArc₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).outerArc₁ =
      (normalizedChordSplitData h).outerArc₂ := by
  ext d
  change (M.dartFace d = hNT.outerFace ∧
      M.dartFace (M.α d) ∈ (normalizedChordSplitData (chord_symm h)).side₁) ↔
    (M.dartFace d = hNT.outerFace ∧
      M.dartFace (M.α d) ∈ (normalizedChordSplitData h).side₂)
  rw [normalizedChordSplitData_chord_symm_side₁ h]

theorem normalizedChordSplitData_chord_symm_keptSet₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).keptSet₁ =
      (normalizedChordSplitData h).keptSet₂ := by
  ext d
  change d ∈ ((normalizedChordSplitData (chord_symm h)).sideDarts₁ ∪
      (normalizedChordSplitData (chord_symm h)).outerArc₁) \
        {(normalizedChordSplitData (chord_symm h)).dart} ↔
    d ∈ ((normalizedChordSplitData h).sideDarts₂ ∪
      (normalizedChordSplitData h).outerArc₂) \ {M.α (normalizedChordSplitData h).dart}
  rw [normalizedChordSplitData_chord_symm_sideDarts₁ h,
    normalizedChordSplitData_chord_symm_outerArc₁ h,
    normalizedChordSplitData_chord_symm_dart h]

theorem normalizedChordSplitData_chord_symm_sideRegion₁
    (h : hNT.outerCycle.Chord u v) :
    sideRegion₁ (normalizedChordSplitData (chord_symm h)) =
      ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ (normalizedChordSplitData h) := by
  ext w
  constructor
  · rintro ⟨d, hd, htail⟩
    have hkept₁ :
        d ∈ (normalizedChordSplitData (chord_symm h)).keptSet₁ :=
      ((normalizedChordSplitData (chord_symm h)).mem_keptDel₁_iff d).1 hd
    have hkept₂ : d ∈ (normalizedChordSplitData h).keptSet₂ := by
      rwa [normalizedChordSplitData_chord_symm_keptSet₁ h] at hkept₁
    exact ⟨d, ((normalizedChordSplitData h).mem_keptDel₂_iff d).2 hkept₂, htail⟩
  · rintro ⟨d, hd, htail⟩
    have hkept₂ : d ∈ (normalizedChordSplitData h).keptSet₂ :=
      ((normalizedChordSplitData h).mem_keptDel₂_iff d).1 hd
    have hkept₁ : d ∈ (normalizedChordSplitData (chord_symm h)).keptSet₁ := by
      rwa [normalizedChordSplitData_chord_symm_keptSet₁ h]
    exact ⟨d, ((normalizedChordSplitData (chord_symm h)).mem_keptDel₁_iff d).2 hkept₁, htail⟩

/-- The parent precoloured boundary edge is confined to one of the two chord sides. -/
theorem precolored_edge_confined_to_one_side
    {α : Type u} [DecidableEq α] (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {L : M.Vertex → Finset α} {cp cq : α}
    (hTL : ThomassenLists hNT p q L cp cq) :
    (p ∈ sideRegion₁ data ∧ q ∈ sideRegion₁ data) ∨
      (p ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data ∧
        q ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data) := by
  classical
  have hadj : M.toSimpleGraph.Adj p q := by
    have hpq_boundary := hTL.pq_boundary_edge
    change s(p, q) ∈ hNT.outerCycle.edges at hpq_boundary
    rw [hNT.outerCycle.edges_eq, List.mem_map] at hpq_boundary
    obtain ⟨d, _hd, hedge⟩ := hpq_boundary
    exact ⟨hTL.p_ne_q, d, hedge⟩
  exact edge_confined_holds data hsep hadj

theorem precolored_edge_side₁_or_swapped_side₁
    {α : Type u} [DecidableEq α] (h : hNT.outerCycle.Chord u v)
    {L : M.Vertex → Finset α} {cp cq : α}
    (hTL : ThomassenLists hNT p q L cp cq) :
    (p ∈ sideRegion₁ (normalizedChordSplitData h) ∧
        q ∈ sideRegion₁ (normalizedChordSplitData h)) ∨
      (p ∈ sideRegion₁ (normalizedChordSplitData (chord_symm h)) ∧
        q ∈ sideRegion₁ (normalizedChordSplitData (chord_symm h))) := by
  have hconf :=
    precolored_edge_confined_to_one_side (normalizedChordSplitData h)
      (ProofsInTheBook.ZinanCh35ChordResidue.normSep h) hTL
  rcases hconf with h₁ | h₂
  · exact Or.inl h₁
  · right
    rwa [normalizedChordSplitData_chord_symm_sideRegion₁ h]

/-- Choose the chord orientation whose side-1 region contains the precoloured edge. -/
noncomputable def orientChordForPreedge
    {α : Type u} [DecidableEq α] (h : hNT.outerCycle.Chord u v)
    {L : M.Vertex → Finset α} {cp cq : α}
    (hTL : ThomassenLists hNT p q L cp cq) :
    Σ' (u' v' : M.Vertex) (h' : hNT.outerCycle.Chord u' v'),
      p ∈ sideRegion₁ (normalizedChordSplitData h') ∧
        q ∈ sideRegion₁ (normalizedChordSplitData h') := by
  classical
  exact Classical.choice (show Nonempty
    (Σ' (u' v' : M.Vertex) (h' : hNT.outerCycle.Chord u' v'),
      p ∈ sideRegion₁ (normalizedChordSplitData h') ∧
        q ∈ sideRegion₁ (normalizedChordSplitData h')) from by
      rcases precolored_edge_side₁_or_swapped_side₁ h hTL with h₁ | h₂
      · exact ⟨⟨u, v, h, h₁⟩⟩
      · exact ⟨⟨v, u, chord_symm h, h₂⟩⟩)

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

@[simp] lemma sideVertexToM₂_tail_inr_zero_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep a₀ a₁ hne
        ((data.sideMap₂ hsep a₀ a₁ hne).tail (Sum.inr (0 : Fin 2)))
      = M.tail a₀.1 := by
  simpa using ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_tail_inr data hsep a₀ a₁ hne
    (0 : Fin 2)

@[simp] lemma sideVertexToM₂_head_inr_zero_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep a₀ a₁ hne
        ((data.sideMap₂ hsep a₀ a₁ hne).head (Sum.inr (0 : Fin 2)))
      = M.tail a₁.1 := by
  simpa using ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_head_inr data hsep a₀ a₁ hne
    (0 : Fin 2)

@[simp] lemma sideVertexToM₂_tail_inl_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₂}) :
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep a₀ a₁ hne
        ((data.sideMap₂ hsep a₀ a₁ hne).tail (Sum.inl k))
      = M.tail k.1 := by
  exact ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_inl data hsep a₀ a₁ hne k



/-- The swapped-root canonical side-2 near-triangulation. -/
noncomputable def canonicalSide₂NT (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    NearTriangulation
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm) :=
  ProofsInTheBook.ZinanCh35Side2.chordSideNearTriangulation₂_of_share data hsep
    (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
    (ProofsInTheBook.ChordSideClose.side₂IsDisk_unconditional data hsep)
    (side₂AnchorsShareFace_canonical_swapped (hNT := hNT) data hsep)
    (contiguousInterval₂_direct_canonical_swapped_uncond hNT data hsep)

@[simp] theorem canonicalSide₂NT_outerCycle_darts
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.darts =
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0) :=
  rfl

theorem canonicalSide₂_boundary_tail_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
      ((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).tail x) := by
  rw [BoundaryCycle.IsBoundaryVertex,
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.vertices_eq]
  exact List.mem_map_of_mem hx

theorem canonicalSide₂_boundary_head_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
      ((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).head x) := by
  exact boundaryCycle_head_mem_vertices_of_mem_darts
    ((canonicalSide₂NT (hNT := hNT) data hsep).outerCycle)
    (by simpa [canonicalSide₂NT_outerCycle_darts (hNT := hNT) data hsep] using hx)

theorem canonicalSide₂_boundary_edge_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
      ((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).dartEdge x) := by
  rw [BoundaryCycle.IsBoundaryEdge,
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.edges_eq]
  exact List.mem_map_of_mem hx

theorem canonicalSide₂_root0_mem_faceDartList
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (Sum.inr (0 : Fin 2) : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) ∈
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0) :=
  (ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_side₂_outer_orbit_mem_iff_swapped_root0
    hNT data hsep (Sum.inr (0 : Fin 2))).2 (Or.inl rfl)

theorem canonicalSide₂_boundary_vertex_parent_boundary
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (htu : M.tail data.dart = u)
    (W : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).Vertex)
    (hW : (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W) :
    hNT.outerCycle.IsBoundaryVertex
      (ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W) := by
  classical
  rw [BoundaryCycle.IsBoundaryVertex,
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.vertices_eq,
    canonicalSide₂NT_outerCycle_darts (hNT := hNT) data hsep] at hW
  rw [List.mem_map] at hW
  obtain ⟨x, hx, hxW⟩ := hW
  rcases (canonical_side₂_outer_orbit_mem_iff_swapped_root0 hNT data hsep x).1 hx with
    hroot | ⟨k, hxk, hτ⟩
  · rw [← hxW, hroot]
    rw [sideVertexToM₂_tail_inr_zero_apply]
    rw [canonicalSide₂Anchor₁_tail hNT data hsep, htu]
    exact data.chord.left_boundary
  · have H := side₂EndpointBoundaryAlignment_uncond hNT data hsep
    have hTA := canonicalTracePhiArc₂_fwdArc_of_alignment hNT data hsep H.1 H.2
    have hτorig :
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
          ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k := by
      simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτ
    rcases (hTA.mem_iff k).1 hτorig with ⟨i, hk⟩
    rw [← hxW, hxk]
    rw [sideVertexToM₂_tail_inl_apply]
    rw [hk]
    exact boundaryCycle_tail_mem_vertices_of_mem_darts hNT.outerCycle
      ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).boundary i)



theorem canonicalSide₂_faceDartList_mem_of_outerArc₂
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂}) (hk : k.1 ∈ data.outerArc₂) :
    (Sum.inl k : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) ∈
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0) := by
  classical
  obtain ⟨i, hi⟩ := outerArc₂_mem_fwdArc_canonical hNT data hsep hk
  have H := side₂EndpointBoundaryAlignment_uncond hNT data hsep
  have hTA := canonicalTracePhiArc₂_fwdArc_of_alignment hNT data hsep H.1 H.2
  have hkArc :
      k =
        ⟨(ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i,
          fwdArc_arcDart_notMem_keptDel₂ hNT data hsep i⟩ := by
    apply Subtype.ext
    exact hi
  have hτ :
      (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
        ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k :=
    (hTA.mem_iff k).2 ⟨i, hkArc⟩
  have hτswapped :
      (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
        ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k := by
    simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτ
  exact (canonical_side₂_outer_orbit_mem_iff_swapped_root0
    hNT data hsep (Sum.inl k)).2 (Or.inr ⟨k, rfl, hτswapped⟩)

theorem canonicalSide₂_boundary_of_outerArc_tail_eq
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).Vertex}
    {b : D} (hb : b ∈ data.outerArc₂)
    (htail : M.tail b =
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let k : {d : D // d ∉ data.keptDel₂} :=
    ⟨b, ProofsInTheBook.ChordSideClose.outerArc_notMem_keptDel₂ data hb.1 hb.2⟩
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  let Wb : S.Vertex := S.tail (Sum.inl k)
  have hWb :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex Wb :=
    canonicalSide₂_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep
      (canonicalSide₂_faceDartList_mem_of_outerArc₂ (hNT := hNT) data hsep k hb)
  have hι :
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm Wb =
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm W := by
    dsimp [Wb, S, k]
    rw [sideVertexToM₂_tail_inl_apply]
    exact htail
  have hEq : Wb = W :=
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm hι
  simpa [hEq] using hWb

theorem canonicalSide₂_boundary_of_parent_eq_tail
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).Vertex}
    (htu : M.tail data.dart = u)
    (hW : ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W = u) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  let Wb : S.Vertex := S.tail (Sum.inr (0 : Fin 2))
  have hx := canonicalSide₂_root0_mem_faceDartList (hNT := hNT) data hsep
  have hWb :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex Wb :=
    canonicalSide₂_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hι :
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm Wb =
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm W := by
    dsimp [Wb, S]
    rw [sideVertexToM₂_tail_inr_zero_apply, canonicalSide₂Anchor₁_tail hNT data hsep, htu, hW]
  have hEq : Wb = W :=
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm hι
  simpa [hEq] using hWb

theorem canonicalSide₂_boundary_of_parent_eq_head
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).Vertex}
    (hhv : M.head data.dart = v)
    (hW : ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W = v) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  let Wb : S.Vertex := S.head (Sum.inr (0 : Fin 2))
  have hx := canonicalSide₂_root0_mem_faceDartList (hNT := hNT) data hsep
  have hWb :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex Wb :=
    canonicalSide₂_boundary_head_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hι :
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm Wb =
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm W := by
    dsimp [Wb, S]
    rw [sideVertexToM₂_head_inr_zero_apply, canonicalSide₂Anchor₀_tail hNT data hsep, hhv, hW]
  have hEq : Wb = W :=
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm hι
  simpa [hEq] using hWb

theorem canonicalSide₂_parent_boundary_vertex_side_boundary_normalized
    {h : hNT.outerCycle.Chord u v}
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v)
    (W : ((normalizedChordSplitData h).sideMap₂ hsep
      (side₂Anchor₁ (normalizedChordSplitData h) hsep)
      (side₂Anchor₀ (normalizedChordSplitData h) hsep)
      (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm).Vertex)
    (hparent : hNT.outerCycle.IsBoundaryVertex
      (ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ (normalizedChordSplitData h) hsep
        (side₂Anchor₁ (normalizedChordSplitData h) hsep)
        (side₂Anchor₀ (normalizedChordSplitData h) hsep)
        (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm W)) :
    (canonicalSide₂NT (hNT := hNT) (normalizedChordSplitData h) hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let data := normalizedChordSplitData h
  let ι := ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
    (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  have hWside : ι W ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data :=
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_mem data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm W
  have hparentι : hNT.outerCycle.IsBoundaryVertex (ι W) := by
    simpa [ι, data] using hparent
  let R := normalizedRuns h
  rcases R.covering hparentι with hUV | hVU | hWu | hWv
  · obtain ⟨i, hi⟩ := hUV
    have hB : M.dartFace (M.α ((ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcUV htu.symm hhv.symm).symm i))) ∈ data.side₁ :=
      bwdRun_reverse_face_mem_side₁ data (ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm)
        (by rw [ZinanCh35Aligned.daCast_len]; exact R.lenUV) _
    have hsame : (ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcUV htu.symm hhv.symm).symm i)
          = R.arcUV.arcDart i := by
      rw [ZinanCh35Aligned.daCast_arcDart_eq]; congr 1
    rw [hsame] at hB
    have hchord : M.dartEdge (R.arcUV.arcDart i) ≠ s(u, v) := by
      intro he
      apply h.not_boundary_edge
      rw [← he]
      show M.dartEdge (R.arcUV.arcDart i) ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]
      exact List.mem_map_of_mem (R.arcUV.boundary i)
    have hWside₁ : ι W ∈ sideRegion₁ data := by
      have hchordα : M.dartEdge (M.α (R.arcUV.arcDart i)) ≠ s(u, v) := by
        rw [M.dartEdge_alpha]
        exact hchord
      obtain ⟨_, htail⟩ :=
        endpoints_mem_sideRegion₁_of_face data hsep hchordα hB
      rw [M.head_alpha] at htail
      rw [hi] at htail
      exact htail
    rcases ProofsInTheBook.ZinanCh35StarConn.sideRegionInterChordEnds_holds data hsep hWside₁ hWside with hWu' | hWv'
    · exact canonicalSide₂_boundary_of_parent_eq_tail (hNT := hNT) data hsep (W := W) htu (by
        simpa [ι] using hWu')
    · exact canonicalSide₂_boundary_of_parent_eq_head (hNT := hNT) data hsep (W := W) hhv (by
        simpa [ι] using hWv')
  · obtain ⟨i, hi⟩ := hVU
    have hF : M.dartFace (M.α ((ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcVU hhv.symm htu.symm).symm i))) ∈ data.side₂ :=
      fwdRun_reverse_face_mem_side₂ data (ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm)
        (by rw [ZinanCh35Aligned.daCast_len]; exact R.lenVU) _
    have hsame : (ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcVU hhv.symm htu.symm).symm i)
          = R.arcVU.arcDart i := by
      rw [ZinanCh35Aligned.daCast_arcDart_eq]; congr 1
    rw [hsame] at hF
    have hb : R.arcVU.arcDart i ∈ data.outerArc₂ := by
      constructor
      · exact (hNT.outerCycle.mem_darts_iff _).mp (R.arcVU.boundary i)
      · exact hF
    exact canonicalSide₂_boundary_of_outerArc_tail_eq (hNT := hNT) data hsep hb (by
      simpa [ι] using hi)
  · exact canonicalSide₂_boundary_of_parent_eq_tail (hNT := hNT) data hsep (W := W) htu (by
      simpa [ι] using hWu)
  · exact canonicalSide₂_boundary_of_parent_eq_head (hNT := hNT) data hsep (W := W) hhv (by
      simpa [ι] using hWv)

theorem canonicalSide₂ThomassenLists_forced_normalized
    {α : Type u} [DecidableEq α] {h : hNT.outerCycle.Chord u v}
    {L : M.Vertex → Finset α} {cp cq : α}
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v)
    (hTL : ThomassenLists hNT p q L cp cq)
    (hp : p ∈ sideRegion₁ (normalizedChordSplitData h))
    (hq : q ∈ sideRegion₁ (normalizedChordSplitData h))
    (regions : ChordSplitRegions hNT u v p q L cp cq)
    (c₁ : M.Vertex → α) (hcuv : c₁ u ≠ c₁ v) :
    ThomassenLists
      (canonicalSide₂NT (hNT := hNT) (normalizedChordSplitData h) hsep)
      (((normalizedChordSplitData h).sideMap₂ hsep
        (side₂Anchor₁ (normalizedChordSplitData h) hsep)
        (side₂Anchor₀ (normalizedChordSplitData h) hsep)
        (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm).tail (Sum.inr 0))
      (((normalizedChordSplitData h).sideMap₂ hsep
        (side₂Anchor₁ (normalizedChordSplitData h) hsep)
        (side₂Anchor₀ (normalizedChordSplitData h) hsep)
        (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm).head (Sum.inr 0))
      (fun x => regions.forcedLists c₁ L
        (ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ (normalizedChordSplitData h) hsep
          (side₂Anchor₁ (normalizedChordSplitData h) hsep)
          (side₂Anchor₀ (normalizedChordSplitData h) hsep)
          (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm x))
      (c₁ u) (c₁ v) := by
  classical
  let data := normalizedChordSplitData h
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  let ι := ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
    (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  have hx : (Sum.inr (0 : Fin 2) : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) ∈
      S.faceDartList (Sum.inr 0) :=
    canonicalSide₂_root0_mem_faceDartList (hNT := hNT) data hsep
  have hpbd :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
        (S.tail (Sum.inr (0 : Fin 2))) :=
    canonicalSide₂_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hqbd :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
        (S.head (Sum.inr (0 : Fin 2))) :=
    canonicalSide₂_boundary_head_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hpqbd :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
        (S.dartEdge (Sum.inr (0 : Fin 2))) :=
    canonicalSide₂_boundary_edge_of_faceDartList_mem (hNT := hNT) data hsep hx
  refine
    { p_boundary := by simpa [data, S] using hpbd
      q_boundary := by simpa [data, S] using hqbd
      pq_boundary_edge := by
        change (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
          (S.dartEdge (Sum.inr (0 : Fin 2)))
        exact hpqbd
      colors_ne := hcuv
      list_p := ?_
      list_q := ?_
      boundary_ge_three := ?_
      interior_ge_five := ?_ }
  · have hιp : ι (S.tail (Sum.inr (0 : Fin 2))) = u := by
      dsimp [ι, S]
      rw [sideVertexToM₂_tail_inr_zero_apply, canonicalSide₂Anchor₁_tail hNT data hsep, htu]
    simpa [ι, data, S, hιp] using regions.forcedLists_u c₁ L
  · have hιq : ι (S.head (Sum.inr (0 : Fin 2))) = v := by
      dsimp [ι, S]
      rw [sideVertexToM₂_head_inr_zero_apply, canonicalSide₂Anchor₀_tail hNT data hsep, hhv]
    have huv : u ≠ v := h.endpoints_ne
    simpa [ι, data, S, hιq] using regions.forcedLists_v huv c₁ L
  · intro W hW hWp hWq
    have hparent :
        hNT.outerCycle.IsBoundaryVertex (ι W) :=
      canonicalSide₂_boundary_vertex_parent_boundary (hNT := hNT) data hsep htu W hW
    have hWside₂ : ι W ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data :=
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_mem data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W
    have hWu : ι W ≠ u := by
      intro hιu
      have hEq : W = S.tail (Sum.inr (0 : Fin 2)) :=
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm (by
            dsimp [ι, S] at hιu ⊢
            rw [sideVertexToM₂_tail_inr_zero_apply, canonicalSide₂Anchor₁_tail hNT data hsep,
              htu]
            exact hιu)
      exact hWp hEq
    have hWv : ι W ≠ v := by
      intro hιv
      have hEq : W = S.head (Sum.inr (0 : Fin 2)) :=
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm (by
            dsimp [ι, S] at hιv ⊢
            rw [sideVertexToM₂_head_inr_zero_apply, canonicalSide₂Anchor₀_tail hNT data hsep,
              hhv]
            exact hιv)
      exact hWq hEq
    have hWp_parent : ι W ≠ p := by
      intro hιp
      have hp₂ : p ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data := by
        simpa [hιp] using hWside₂
      rcases ProofsInTheBook.ZinanCh35StarConn.sideRegionInterChordEnds_holds data hsep hp hp₂ with
        hpu | hpv
      · exact hWu (hιp.trans hpu)
      · exact hWv (hιp.trans hpv)
    have hWq_parent : ι W ≠ q := by
      intro hιq
      have hq₂ : q ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data := by
        simpa [hιq] using hWside₂
      rcases ProofsInTheBook.ZinanCh35StarConn.sideRegionInterChordEnds_holds data hsep hq hq₂ with
        hqu | hqv
      · exact hWu (hιq.trans hqu)
      · exact hWv (hιq.trans hqv)
    rw [regions.forcedLists_other hWu hWv c₁ L]
    exact hTL.boundary_ge_three (ι W) hparent hWp_parent hWq_parent
  · intro W hWint
    have hparentInt : ¬ hNT.outerCycle.IsBoundaryVertex (ι W) := by
      intro hparent
      exact hWint
        (canonicalSide₂_parent_boundary_vertex_side_boundary_normalized
          (hNT := hNT) (h := h) hsep htu hhv W (by simpa [data, ι] using hparent))
    have hWu : ι W ≠ u := by
      intro hιu
      exact hWint
        (canonicalSide₂_boundary_of_parent_eq_tail (hNT := hNT) data hsep (W := W) htu
          (by simpa [ι] using hιu))
    have hWv : ι W ≠ v := by
      intro hιv
      exact hWint
        (canonicalSide₂_boundary_of_parent_eq_head (hNT := hNT) data hsep (W := W) hhv
          (by simpa [ι] using hιv))
    rw [regions.forcedLists_other hWu hWv c₁ L]
    exact hTL.interior_ge_five (ι W) hparentInt

noncomputable def canonicalChordBranchResidualData
    {α : Type u} [DecidableEq α] {h : hNT.outerCycle.Chord u v}
    {L : M.Vertex → Finset α} {cp cq : α}
    (hTL : ThomassenLists hNT p q L cp cq)
    (hp : p ∈ sideRegion₁ (normalizedChordSplitData h))
    (hq : q ∈ sideRegion₁ (normalizedChordSplitData h)) :
    ProofsInTheBook.ZinanCh35ChordBranch.ChordBranchResidualData h p q L cp cq := by
  classical
  let data := normalizedChordSplitData h
  let hsep := ProofsInTheBook.ZinanCh35ChordResidue.normSep h
  have htu : M.tail data.dart = u := by
    simpa [data] using normalizedChordSplitData_dart_tail (hNT := hNT) h
  have hhv : M.head data.dart = v := by
    simpa [data] using normalizedChordSplitData_dart_head (hNT := hNT) h
  have hSide₁ :
      ∃ pₛ qₛ : (data.sideMap₁ hsep
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).Vertex,
        ThomassenLists
          (canonicalSide₁NT (hNT := hNT) data hsep)
          pₛ qₛ
          (fun x => L (sideVertexToM₁ data hsep
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep) x))
          cp cq :=
    canonicalSide₁ThomassenLists_exists_normalized (hNT := hNT) (h := h)
      hsep htu hhv hTL hp hq
  let p₁ := Classical.choose hSide₁
  let hSide₁' := Classical.choose_spec hSide₁
  let q₁ := Classical.choose hSide₁'
  have hL₁ := Classical.choose_spec hSide₁'
  let res := chordSplitRegionsResidue_of_precolored data hsep hp hq
  let regions :=
    ProofsInTheBook.ZinanCh35ChordResidue.chordSplitRegions_of_residue
      data hsep htu hhv res (L := L) (cp := cp) (cq := cq)
  refine canonicalChordBranchResidualData_of_fuel (hNT := hNT) (h := h)
    L cp cq htu hhv hp hq p₁ q₁ cp cq ?_
    (fun _ _ => data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm |>.tail (Sum.inr (0 : Fin 2)))
    (fun _ _ => data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm |>.head (Sum.inr (0 : Fin 2)))
    (fun c₁ _ => c₁ u) (fun c₁ _ => c₁ v) ?_
  · simpa [canonicalSide₁NT, data, hsep] using hL₁
  · intro c₁ hcuv
    simpa [canonicalSide₂NT, data, hsep, res, regions] using
      canonicalSide₂ThomassenLists_forced_normalized (hNT := hNT) (h := h)
        hsep htu hhv hTL hp hq regions c₁ hcuv

noncomputable def canonicalChordBranchResidualSupplier
    (α : Type u) [DecidableEq α] :
    ProofsInTheBook.ZinanCh35ChordBranch.ChordBranchResidualSupplier α where
  supply := by
    intro D _ _ M hNT p q L cp cq hTL hchord
    let u := Classical.choose hchord
    let hchord' := Classical.choose_spec hchord
    let v := Classical.choose hchord'
    let h := Classical.choose_spec hchord'
    obtain ⟨u', v', h', hpq⟩ :=
      orientChordForPreedge (hNT := hNT) (h := h) hTL
    exact ⟨u', v', h',
      canonicalChordBranchResidualData (hNT := hNT) (h := h') hTL hpq.1 hpq.2⟩

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

/-- **Cyclic predecessor witness.**  Every listed dart has a cyclic predecessor on
the cyclic dart list: a dart `bin ∈ C.darts` with `M.φ bin = bout` (and hence
`M.head bin = M.tail bout`, by `consecutive_vertex`). -/
lemma exists_phi_pred (C : BoundaryCycle M f) {bout : D} (hbout : bout ∈ C.darts) :
    ∃ bin : D, bin ∈ C.darts ∧ M.φ bin = bout ∧ M.head bin = M.tail bout := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  -- the position of `bout`
  rw [List.mem_iff_getElem] at hbout
  obtain ⟨q, hq, hgetq⟩ := hbout
  -- its cyclic predecessor index `p = (q + L - 1) % L`
  set p : ℕ := (q + L - 1) % L with hp
  have hpL : p < L := by rw [hp]; exact Nat.mod_lt _ hLpos
  -- cyclicNext p = q
  have hcyc : (cyclicNext C.normalized.length_pos ⟨p, hpL⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext
    show (p + 1) % L = q
    rw [hp]
    -- ((q + L - 1) % L + 1) % L = q
    rw [Nat.mod_add_mod, show q + L - 1 + 1 = q + L from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  refine ⟨C.darts[p]'hpL, List.getElem_mem hpL, ?_, ?_⟩
  · -- `M.φ bin = bout` from `consecutive_phi`
    have hcp := C.consecutive_phi ⟨p, hpL⟩
    rw [hcyc] at hcp
    have hq' : C.darts.get ⟨q, hq⟩ = C.darts[q]'hq := rfl
    have hp' : C.darts.get ⟨p, hpL⟩ = C.darts[p]'hpL := rfl
    rw [hq', hp', hgetq] at hcp
    -- hcp : bout = M.φ (C.darts[p])
    exact hcp.symm
  · -- `M.head bin = M.tail bout` from `consecutive_vertex`
    have hcv := C.consecutive_vertex ⟨p, hpL⟩
    rw [hcyc] at hcv
    have hq' : C.darts.get ⟨q, hq⟩ = C.darts[q]'hq := rfl
    have hp' : C.darts.get ⟨p, hpL⟩ = C.darts[p]'hpL := rfl
    rw [hq', hp', hgetq] at hcv
    -- hcv : M.tail bout = M.head (C.darts[p])
    exact hcv.symm

/-- `C.darts` is closed under `M.φ`: the face of `M.φ d` equals the face of `d`. -/
lemma phi_mem_darts (C : BoundaryCycle M f) {d : D} (hd : d ∈ C.darts) :
    M.φ d ∈ C.darts := by
  rw [C.mem_darts_iff] at hd ⊢
  rw [dartFace_phi, hd]

end BoundaryCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M) {v0 : M.Vertex}

/-- **Unique outer out-dart at `v0`.**  Exactly one boundary dart has tail `v0`.
This is `tail_injective_on_darts` (i.e. `outer_simple`) packaged as existence and
uniqueness. -/
lemma exists_unique_outer_tail (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃! bout : D, bout ∈ hNT.outerCycle.darts ∧ M.tail bout = v0 := by
  classical
  obtain ⟨p, hp⟩ := hNT.outerCycle.exists_pos_of_isBoundaryVertex hv0
  refine ⟨hNT.outerCycle.darts[p.1]'p.2, ⟨List.getElem_mem p.2, hp⟩, ?_⟩
  rintro b ⟨hbmem, hbtail⟩
  exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hbmem
    (List.getElem_mem p.2) (by rw [hbtail, hp])

/-- **Unique outer in-dart at `v0`.**  Exactly one boundary dart has head `v0`.
Head-uniqueness reduces to tail-uniqueness of the `φ`-successor (`tail_phi` +
`phi_mem_darts` + `tail_injective_on_darts`). -/
lemma exists_unique_outer_head (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃! bin : D, bin ∈ hNT.outerCycle.darts ∧ M.head bin = v0 := by
  classical
  -- the unique out-dart `bout`
  obtain ⟨bout, ⟨hboutmem, hbouttail⟩, _⟩ := hNT.exists_unique_outer_tail hv0
  -- its cyclic predecessor is an in-dart
  obtain ⟨bin, hbinmem, hphi, hhead⟩ := hNT.outerCycle.exists_phi_pred hboutmem
  have hbinhead : M.head bin = v0 := by rw [hhead, hbouttail]
  refine ⟨bin, ⟨hbinmem, hbinhead⟩, ?_⟩
  rintro b ⟨hbmem, hbhead⟩
  -- head b = head bin = v0 ⟹ tail (φ b) = tail (φ bin), and both φ-images are listed
  have hφb : M.φ b ∈ hNT.outerCycle.darts := hNT.outerCycle.phi_mem_darts hbmem
  have hφbin : M.φ bin ∈ hNT.outerCycle.darts := hNT.outerCycle.phi_mem_darts hbinmem
  have htails : M.tail (M.φ b) = M.tail (M.φ bin) := by
    rw [tail_phi, tail_phi, hbhead, hbinhead]
  have hφeq : M.φ b = M.φ bin :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφb hφbin htails
  exact M.φ.injective hφeq

/-- **The two consecutive outer darts at a boundary vertex `v0` (Ch35 R6a
keystone).**  On the outer cycle there is a unique in-dart `bin` (head `v0`) and
a unique out-dart `bout` (tail `v0`), and `bout = M.φ bin`.

All consumed planarity input is `hNT.outer_simple : VertexNodup`; the φ-adjacency
is the cyclic structure of `C.darts`.  This discharges the seam keystone of
`MergedOuterArcData` (see `PlanarMapOuterArc.lean`). -/
theorem outer_v0_darts_consecutive (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃ bin bout : D,
      -- the in-dart, unique with head v0
      (bin ∈ hNT.outerCycle.darts ∧ M.head bin = v0) ∧
      (∀ b, b ∈ hNT.outerCycle.darts → M.head b = v0 → b = bin) ∧
      -- the out-dart, unique with tail v0
      (bout ∈ hNT.outerCycle.darts ∧ M.tail bout = v0) ∧
      (∀ b, b ∈ hNT.outerCycle.darts → M.tail b = v0 → b = bout) ∧
      -- and they are φ-consecutive
      M.φ bin = bout := by
  classical
  obtain ⟨bout, ⟨hboutmem, hbouttail⟩, hboutuniq⟩ := hNT.exists_unique_outer_tail hv0
  obtain ⟨bin, ⟨hbinmem, hbinhead⟩, hbinuniq⟩ := hNT.exists_unique_outer_head hv0
  -- The cyclic predecessor of `bout` is an in-dart, hence equals `bin`; so φ bin = bout.
  obtain ⟨bpred, hbpredmem, hphi, hhead⟩ := hNT.outerCycle.exists_phi_pred hboutmem
  have hpredhead : M.head bpred = v0 := by rw [hhead, hbouttail]
  have hpred_eq_bin : bpred = bin := hbinuniq bpred ⟨hbpredmem, hpredhead⟩
  refine ⟨bin, bout, ⟨hbinmem, hbinhead⟩, ?_, ⟨hboutmem, hbouttail⟩, ?_, ?_⟩
  · intro b hbmem hbhead; exact hbinuniq b ⟨hbmem, hbhead⟩
  · intro b hbmem hbtail; exact hboutuniq b ⟨hbmem, hbtail⟩
  · rw [← hpred_eq_bin]; exact hphi



/-- A dart whose head is `v0 = M.tail d0` is deleted by the star deletion of `d0`
(it is `α` of a dart at `v0`).  Mirrors `fanTriangle_d2_deleted`. -/
lemma mem_deleteVertexSet_of_head {d d0 : D} (htail0 : M.tail d0 = v0)
    (hhead : M.head d = v0) : d ∈ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]; right
  rw [mem_vertexDarts]
  exact Quotient.exact (show M.tail d0 = M.tail (M.α d) by
    rw [tail_alpha, hhead, htail0])

/-- **The two derivable `exit_*` facts for the exit survivor.**  Let `oPre` be a
surviving dart on the outer face whose `M.φ`-successor `bin` has head `v0` (the
exit survivor `o_pre`, cyclic predecessor of the in-dart).  Then its `M.dartFace`
is the outer face and `M.φ oPre` is deleted — the two `MergedOuterArcData` fields
`exit_face`/`exit_next_deleted` discharged directly from the keystone geometry. -/
lemma exit_face_and_next_deleted {d0 : D} (htail0 : M.tail d0 = v0)
    (oPre : {d : D // d ∉ M.deleteVertexSet d0})
    (hface : oPre.1 ∈ hNT.outerCycle.darts)
    (hnexthead : M.head (M.φ oPre.1) = v0) :
    M.dartFace oPre.1 = hNT.outerFace ∧
      M.φ oPre.1 ∈ M.deleteVertexSet d0 :=
  ⟨hNT.outerCycle.dartFace_of_mem_darts hface,
    mem_deleteVertexSet_of_head (v0 := v0) htail0 hnexthead⟩

/-- **Assemble `MergedOuterArcData` from the keystone, given the two genuinely
planar residual fields.**  The keystone supplies the seam `bin/bout` and the exit
survivor `oPre` (cyclic predecessor of `bin`, `M.φ oPre = bin`, `M.head bin = v0`);
this lemma derives `exit_face` and `exit_next_deleted` from it, and consumes the
two remaining seam facts — the Case-B spoke jump (`exit_jump`) and the surviving-arc
contiguity (`arc_run`) — as the precisely-stated residual interface they genuinely
are (discharged by the `PlanarMapFanMergedOrbit` Case-B calculus +
`fanTriangle_shared_spoke`, not by this keystone). -/
def mergedOuterArcData_of_exit {d0 : D}
    (r : {d : D // d ∉ M.deleteVertexSet d0})
    (htail0 : M.tail d0 = v0)
    (oPre : {d : D // d ∉ M.deleteVertexSet d0})
    (hface : oPre.1 ∈ hNT.outerCycle.darts)
    (hnexthead : M.head (M.φ oPre.1) = v0)
    -- residual seam fields (NOT from the keystone; supplied by the fan layer):
    (hjump : M.σ (M.φ oPre.1) = r.1)
    (harc : ∀ x : {d : D // d ∉ M.deleteVertexSet d0},
      M.dartFace x.1 = hNT.outerFace →
      ∃ k : ℕ, (∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet d0) ∧
        (M.φ ^ k) x.1 = oPre.1) :
    MergedOuterArcData M d0 r hNT.outerFace where
  exit := oPre
  exit_face := (hNT.exit_face_and_next_deleted htail0 oPre hface hnexthead).1
  exit_next_deleted := (hNT.exit_face_and_next_deleted htail0 oPre hface hnexthead).2
  exit_jump := hjump
  arc_run := harc

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







/-- The outgoing outer-boundary spoke has nontrivial `σ`-orbit. -/
theorem outgoingOuterDart_sigma_ne {d0 : D}
    (hd0 : M.dartFace d0 = hNT.outerFace) :
    M.σ d0 ≠ d0 :=
  hNT.boundary_dart_sigma_ne ((hNT.outerCycle.mem_darts_iff d0).2 hd0)



/-- **The first fan endpoint is a boundary vertex.**  `x := head d0` is the next
outer-cycle vertex along the outer dart `d0`, hence a boundary vertex.  Indeed
`head d0 = tail (φ d0)` and `φ d0` is again an outer dart. -/
theorem head_outgoing_boundary {d0 : D}
    (hd0 : M.dartFace d0 = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryVertex (M.head d0) := by
  -- `φ d0` is an outer dart, and `tail (φ d0) = head d0`.
  have hφ : M.dartFace (M.φ d0) = hNT.outerFace := by
    rw [dartFace_phi]; exact hd0
  have hbv : hNT.outerCycle.IsBoundaryVertex (M.tail (M.φ d0)) :=
    ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer (hNT := hNT) hφ
  rwa [M.tail_phi] at hbv

/-- **The incoming outer-boundary spoke's head is a boundary vertex.**  The dart
`σ⁻¹ d0` has its *edge* on the outer face: by the rotation identity
`dartFace (σ (σ⁻¹ d0)) = dartFace (α (σ⁻¹ d0))`, i.e. `dartFace d0 = outerFace`, the
α-partner `α (σ⁻¹ d0)` is an outer dart with tail `head (σ⁻¹ d0)`.  Hence
`w := head (σ⁻¹ d0)` is a boundary vertex.  This is the *other* outer-cycle neighbour
of `v0`. -/
theorem head_incoming_boundary {d0 : D}
    (hd0 : M.dartFace d0 = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryVertex (M.head (M.σ.symm d0)) := by
  -- `α (σ⁻¹ d0)` is on the outer face.
  have hαface : M.dartFace (M.α (M.σ.symm d0)) = hNT.outerFace := by
    -- `φ (σ⁻¹ d0) = σ (α (σ⁻¹ d0))`, and `dartFace (φ x) = dartFace x`.
    -- Compute `dartFace (α (σ⁻¹ d0))` via `starFace_next_eq_alpha`-style identity:
    -- `dartFace (σ (σ⁻¹ d0)) = dartFace (α (σ⁻¹ d0))`.
    have hkey : M.dartFace (M.σ (M.σ.symm d0)) = M.dartFace (M.α (M.σ.symm d0)) := by
      -- `φ (α x) = σ x` ⟹ `dartFace (σ x) = dartFace (α x)` for `x = σ⁻¹ d0`.
      have hφeq : M.φ (M.α (M.σ.symm d0)) = M.σ (M.σ.symm d0) := by
        simp [φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
      calc M.dartFace (M.σ (M.σ.symm d0))
          = M.dartFace (M.φ (M.α (M.σ.symm d0))) := by rw [hφeq]
        _ = M.dartFace (M.α (M.σ.symm d0)) := M.dartFace_phi _
    rw [Equiv.apply_symm_apply] at hkey
    rw [← hkey]; exact hd0
  -- `tail (α (σ⁻¹ d0)) = head (σ⁻¹ d0)`.
  have hbv : hNT.outerCycle.IsBoundaryVertex (M.tail (M.α (M.σ.symm d0))) :=
    ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer (hNT := hNT) hαface
  -- `head d = tail (α d)`.
  have hheadtail : M.tail (M.α (M.σ.symm d0)) = M.head (M.σ.symm d0) := rfl
  rwa [hheadtail] at hbv







/-- **An inner spoke at a boundary vertex has a non-boundary edge.**  If a dart `d`
has both faces inner (`dartFace d ≠ outerFace` and `dartFace (α d) ≠ outerFace`), its
edge is not a boundary edge.  This is `ZinanCh35InnerConn.not_boundaryEdge_of_both_inner`,
re-exported for the fan interior. -/
theorem inner_spoke_edge_nonboundary {d : D}
    (h1 : M.dartFace d ≠ hNT.outerFace) (h2 : M.dartFace (M.α d) ≠ hNT.outerFace) :
    ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) :=
  ProofsInTheBook.ZinanCh35InnerConn.not_boundaryEdge_of_both_inner (hNT := hNT) h1 h2

/-- **Chordlessness ⟹ an interior fan vertex is not an old boundary vertex.**

Let `d` be a spoke at the boundary vertex `v0` (`tail d = v0`) whose two incident
faces are both inner (so its edge is non-boundary), and whose head `z := head d` is
distinct from `v0`.  If the boundary is chordless, then `z` is **not** a boundary
vertex: otherwise `(v0, z)` would be a boundary chord — `v0, z` are distinct boundary
vertices, adjacent in `M` via `d`, joined by a non-boundary edge.

This is exactly the `FanIncidenceData.interior_not_boundary_of_chordless` content for
each interior spoke: it follows from chordlessness and the σ-rotation calculus, **not**
from any additional planar certificate. -/
theorem interior_vertex_chord_of_boundary {v0 : M.Vertex} {d : D}
    (hv0b : hNT.outerCycle.IsBoundaryVertex v0)
    (htd : M.tail d = v0)
    (h1 : M.dartFace d ≠ hNT.outerFace) (h2 : M.dartFace (M.α d) ≠ hNT.outerFace)
    (hz : M.head d ≠ v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hzb : hNT.outerCycle.IsBoundaryVertex (M.head d)) :
    False := by
  -- The spoke `d` certifies `(v0, head d)` is a boundary chord, contradicting
  -- chordlessness.
  refine hchordless (u := v0) (v := M.head d) ?_
  refine
    { endpoints_ne := fun h => hz h.symm
      left_boundary := hv0b
      right_boundary := hzb
      adj := ?_
      not_boundary_edge := ?_ }
  · -- adjacency in the simple graph: distinct + dart-adjacent via `d`.
    rw [M.toSimpleGraph_adj]
    refine ⟨fun h => hz h.symm, ?_⟩
    rw [← htd]; exact M.adj_of_dart d
  · -- the edge `s(v0, head d) = dartEdge d` is non-boundary (both faces inner).
    have hedge : (s(v0, M.head d) : Sym2 M.Vertex) = M.dartEdge d := by
      rw [CombMap.dartEdge, htd]
    rw [hedge]
    exact inner_spoke_edge_nonboundary hNT h1 h2










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



/-- `l = l.head hne :: l.tail`. -/
lemma list_head_cons_tail {α : Type*} (l : List α) (hne : l ≠ []) :
    l = l.head hne :: l.tail :=
  (List.cons_head?_tail (l.head?_eq_some_head hne ▸ rfl)).symm

/-- `α⁻¹ = α`: the edge involution is its own inverse. -/
lemma alpha_symm_apply (e : D) : M.α.symm e = M.α e := by
  rw [Equiv.symm_apply_eq, M.alpha_alpha]

/-- `φ⁻¹ e = α (σ⁻¹ e)` (from `φ = σ α`, `α` involutive). -/
lemma phi_symm_apply (e : D) : M.φ.symm e = M.α (M.σ.symm e) := by
  have hsymm : M.φ.symm = M.α.symm * M.σ.symm := by
    rw [φ]; exact mul_inv_rev M.σ M.α
  rw [hsymm]
  show (M.α.symm) (M.σ.symm e) = M.α (M.σ.symm e)
  rw [alpha_symm_apply]

/-- **Spoke-face tail identity.**  For an inner spoke `e` (its face a triangle,
`φ³ e = e`), `head (φ e) = head (σ⁻¹ e)`.  Hence the `φ`-triangle of `e` has tails
`(tail e, head e, head (σ⁻¹ e))` in `φ`-order.  This is `spokeFace_tails` of the
module docstring. -/
lemma spokeFace_head_eq {e : D} (hcube : (M.φ ^ 3) e = e) :
    M.head (M.φ e) = M.head (M.σ.symm e) := by
  -- head (φ e) = tail (φ² e)
  have h1 : M.head (M.φ e) = M.tail (M.φ (M.φ e)) := (M.tail_phi _).symm
  -- φ² e = φ⁻¹ e  (from the cube)
  have h2 : M.φ (M.φ e) = M.φ.symm e := by
    have hthree : M.φ (M.φ (M.φ e)) = e := by
      have hexp : (M.φ ^ 3) e = M.φ (M.φ (M.φ e)) := by
        rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ, pow_two]; rfl
      rw [← hexp, hcube]
    exact (Equiv.eq_symm_apply M.φ).mpr hthree
  rw [h1, h2, phi_symm_apply, M.tail_alpha]







/-- The `σ`-spoke list at a boundary vertex has length at least two (degree ≥ 2). -/
lemma vertexDartList_length_ge_two {d0 : D} (hσ : M.σ d0 ≠ d0) :
    2 ≤ (M.vertexDartList d0).length := by
  rw [vertexDartList]
  exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr
    (by simpa [Equiv.Perm.mem_support] using hσ)

/-- The last spoke of the `σ`-rotation is `σ⁻¹ d0` (the incoming boundary spoke). -/
lemma vertexDartList_getLast {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hne : (M.vertexDartList d0) ≠ []) :
    (M.vertexDartList d0).getLast hne = M.σ.symm d0 := by
  have hpos := M.vertexDartList_length_pos hσ
  set n := (M.vertexDartList d0).length with hn
  rw [List.getLast_eq_getElem, M.vertexDartList_getElem d0 (n-1) (by omega)]
  have hcyc : (M.σ ^ n) d0 = d0 := M.vertexDartList_pow_length hσ
  have key : M.σ.symm ((M.σ ^ n) d0) = (M.σ ^ (n-1)) d0 := by
    rw [show n = (n-1) + 1 by omega, pow_succ']
    simp [Equiv.Perm.mul_apply]
  rw [← key, hcyc]

/-- The canonical decomposition of the spoke-head list into `x :: interior ++ [w]`
with `x = head d0`, `w = head (σ⁻¹ d0)`.  This *defines* the fan endpoints and makes
`heads_eq` definitional. -/
lemma pathHeads_decomp {d0 : D} (hσ : M.σ d0 ≠ d0) :
    (M.vertexDartList d0).map M.head
      = fanPath (M.head d0)
          (((M.vertexDartList d0).map M.head).tail.dropLast)
          (M.head (M.σ.symm d0)) := by
  set hlist := (M.vertexDartList d0).map M.head with hlistdef
  have hpos : 0 < hlist.length := by
    rw [hlistdef, List.length_map]; exact M.vertexDartList_length_pos hσ
  have hge2 : 2 ≤ hlist.length := by
    rw [hlistdef, List.length_map]; exact vertexDartList_length_ge_two hσ
  have hne : hlist ≠ [] := List.ne_nil_of_length_pos hpos
  -- head of hlist = head d0
  have hhead : hlist.head hne = M.head d0 := by
    have hh : (M.vertexDartList d0).head? = some d0 := M.vertexDartList_head hσ
    have : hlist.head? = some (M.head d0) := by
      rw [hlistdef, List.head?_map, hh, Option.map_some]
    rwa [List.head?_eq_some_head hne, Option.some.injEq] at this
  -- last of hlist = head (σ⁻¹ d0)
  have hvne : (M.vertexDartList d0) ≠ [] :=
    List.ne_nil_of_length_pos (M.vertexDartList_length_pos hσ)
  have hlast : hlist.getLast hne = M.head (M.σ.symm d0) := by
    have hmap : hlist.getLast hne = M.head ((M.vertexDartList d0).getLast hvne) :=
      List.getLast_map hne
    rw [hmap, vertexDartList_getLast hσ hvne]
  -- assemble: hlist = head :: (tail.dropLast) ++ [getLast]
  simp only [fanPath]
  rw [← hhead, ← hlast]
  -- hlist = hlist.head :: hlist.tail ; and hlist.tail = hlist.tail.dropLast ++ [hlist.getLast]
  conv_lhs => rw [list_head_cons_tail hlist hne]
  rw [List.cons_append]
  congr 1
  -- hlist.tail = hlist.tail.dropLast ++ [hlist.getLast hne]
  have htne : hlist.tail ≠ [] := by
    intro h
    have hlt : hlist.tail.length = hlist.length - 1 := List.length_tail
    rw [h, List.length_nil] at hlt
    omega
  have hglast : hlist.tail.getLast htne = hlist.getLast hne := by
    rw [List.getLast_tail]
  rw [← hglast, List.dropLast_append_getLast htne]



/-- The canonical interior list. -/
def canonInterior {d0 : D} : List M.Vertex :=
  ((M.vertexDartList d0).map M.head).tail.dropLast

/-- **The orientation certificate** (the isolated planar residue): the exact
incident-non-outer-face structure against the canonical fan path.  This is the
`FanTriangle`-orientation content that the `σ`-forward neighbour list does not pin
down (the handedness of `v0`'s rotation relative to the boundary face). -/
def OrientationCert {v0 : M.Vertex} {d0 : D} : Prop :=
  Nonempty (IncidentNonOuterFacesExactly hNT v0
    (fanPath (M.head d0) (canonInterior (M := M) (d0 := d0)) (M.head (M.σ.symm d0))))

/-- **The base-triangle count** (the isolated counting residue): the degree-2 ⟺
`V = 3` characterization, against the canonical interior. -/
def BaseCount {d0 : D} : Prop :=
  BoundaryChordless hNT.outerCycle →
    (canonInterior (M := M) (d0 := d0) = [] ↔ hNT.IsBaseTriangle)

/-- An interior fan vertex is the head of an interior spoke `e` at `v0`, with `e`
distinct from the outgoing boundary spoke `d0` and from the incoming boundary spoke
`σ⁻¹ d0`.  (Pure list algebra: `canonInterior` is the strict middle of the nodup head
list.) -/
lemma interior_mem_isHead (hNT : NearTriangulation M) {d0 : D} (hσ : M.σ d0 ≠ d0)
    {z : M.Vertex} (hz : z ∈ canonInterior (M := M) (d0 := d0)) :
    ∃ e : D, e ∈ M.vertexDartList d0 ∧ M.head e = z ∧ e ≠ d0 ∧ e ≠ M.σ.symm d0 := by
  simp only [canonInterior] at hz
  set hlist := (M.vertexDartList d0).map M.head with hlistdef
  have hpos : 0 < hlist.length := by
    rw [hlistdef, List.length_map]; exact M.vertexDartList_length_pos hσ
  have hne : hlist ≠ [] := List.ne_nil_of_length_pos hpos
  have hnodup : hlist.Nodup := by
    rw [hlistdef]; exact vertexDartList_heads_nodup hNT hσ rfl
  -- `z ∈ hlist.tail.dropLast ⊆ hlist`, and `z ≠ hlist.head`, `z ≠ hlist.getLast`.
  have hzlist : z ∈ hlist := by
    have h1 : z ∈ hlist.tail := List.dropLast_subset _ hz
    exact List.mem_of_mem_tail h1
  -- `z` is the head of some spoke `e`.
  obtain ⟨e, he_mem, he_head⟩ := List.mem_map.mp hzlist
  -- nodup of the tail: `z ∉` head, and dropLast: `z ∉` getLast.
  have htail_nodup : hlist.tail.Nodup := hnodup.sublist (List.tail_sublist _)
  have hz_ne_head : z ≠ hlist.head hne := by
    intro h
    have hhd : hlist = hlist.head hne :: hlist.tail := list_head_cons_tail hlist hne
    have hnd : (hlist.head hne :: hlist.tail).Nodup := hhd ▸ hnodup
    rw [List.nodup_cons] at hnd
    have hzt : z ∈ hlist.tail := List.dropLast_subset _ hz
    exact hnd.1 (h ▸ hzt)
  have hz_ne_getLast : z ≠ hlist.getLast hne := by
    -- `z ∈ tail.dropLast`, and the getLast of `hlist` is the getLast of `tail`,
    -- which is not in `tail.dropLast` by nodup.
    have htne : hlist.tail ≠ [] := by
      intro h
      have : hlist.length ≤ 1 := by
        have hlt : hlist.tail.length = hlist.length - 1 := List.length_tail
        rw [h, List.length_nil] at hlt; omega
      have hge2 : 2 ≤ hlist.length := by
        rw [hlistdef, List.length_map]; exact vertexDartList_length_ge_two hσ
      omega
    have hgl : hlist.tail.getLast htne = hlist.getLast hne := by rw [List.getLast_tail]
    intro h
    have hzdl : z ∈ hlist.tail.dropLast := hz
    have hzgl : z = hlist.tail.getLast htne := by rw [hgl]; exact h
    -- nodup ⟹ getLast ∉ dropLast
    have hsplit : hlist.tail = hlist.tail.dropLast ++ [hlist.tail.getLast htne] :=
      (List.dropLast_append_getLast htne).symm
    rw [hsplit] at htail_nodup
    have hdisj := (List.nodup_append.mp htail_nodup).2.2
    -- z ∈ dropLast and z = getLast ⟹ z ≠ getLast forced, but z = getLast.
    exact hdisj z hzdl (hlist.tail.getLast htne) (List.mem_singleton_self _) hzgl
  refine ⟨e, he_mem, he_head, ?_, ?_⟩
  · -- `e ≠ d0`: else `z = head d0 = hlist.head`.
    intro he
    apply hz_ne_head
    -- `hlist.head hne = head d0`
    have hhh : hlist.head? = some (M.head d0) := by
      rw [hlistdef, List.head?_map, M.vertexDartList_head hσ, Option.map_some]
    rw [List.head?_eq_some_head hne, Option.some.injEq] at hhh
    -- z = head e = head d0 = hlist.head
    rw [← he_head, he, hhh]
  · -- `e ≠ σ⁻¹ d0`: else `z = head (σ⁻¹ d0) = hlist.getLast`.
    intro he
    apply hz_ne_getLast
    have hvne : (M.vertexDartList d0) ≠ [] :=
      List.ne_nil_of_length_pos (M.vertexDartList_length_pos hσ)
    have hgl : hlist.getLast hne = M.head (M.σ.symm d0) := by
      have hmap : hlist.getLast hne = M.head ((M.vertexDartList d0).getLast hvne) :=
        List.getLast_map hne
      rw [hmap, vertexDartList_getLast hσ hvne]
    rw [hgl, ← he_head, he]



/-- **The maximal `FanIncidenceData` constructor.**  From `hNT`, the outgoing
boundary spoke `d0` at `v0` (`σ d0 ≠ d0`, `tail d0 = v0`, `dartFace d0 = outerFace`),
the chordlessness, and the *only* two isolated items — the orientation certificate
and the base-triangle count — the **full** `FanIncidenceData hNT v0` is assembled.
Every other field is discharged from `σ + hNT` (Sections 1–2 here +
`ZinanCh35Chordless`). -/
noncomputable def fanIncidenceData_of_orientation {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (horient : OrientationCert hNT (v0 := v0) (d0 := d0))
    (hbase : BaseCount hNT (d0 := d0)) :
    NearTriangulation.FanIncidenceData hNT v0 where
  d0 := d0
  sigma_ne := hσ
  tail0 := htail0
  x := M.head d0
  interior := canonInterior (M := M) (d0 := d0)
  w := M.head (M.σ.symm d0)
  heads_eq := by
    have h := pathHeads_decomp (M := M) hσ
    simpa only [canonInterior] using h
  v0_boundary := htail0 ▸
    ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer (hNT := hNT) hface0
  x_boundary := ProofsInTheBook.ZinanCh35Chordless.head_outgoing_boundary hNT hface0
  w_boundary := ProofsInTheBook.ZinanCh35Chordless.head_incoming_boundary hNT hface0
  incident_faces_exact := horient.some
  interior_not_boundary_of_chordless := by
    intro hchord z hz hzb
    -- `z ∈ canonInterior` ⟹ `z` is the head of a spoke `e` at `v0` with `e ≠ d0`
    -- (not the head vertex `x`) and `e ≠ σ⁻¹ d0` (not the last vertex `w`).
    obtain ⟨e, he_mem, he_head, he_ne_d0, he_ne_last⟩ := interior_mem_isHead hNT hσ hz
    have htail_e : M.tail e = v0 :=
      (M.vertexDartList_tail hσ he_mem).trans htail0
    -- both faces of `e` are inner, by uniqueness of the outer dart at `v0`:
    --   dartFace e = outer ⟹ e = d0 (excluded);  dartFace (α e) = dartFace (σ e),
    --   and dartFace (σ e) = outer ⟹ σ e = d0 ⟹ e = σ⁻¹ d0 (excluded).
    have htail_e_d0 : M.tail e = M.tail d0 := by rw [htail_e, htail0]
    have h1 : M.dartFace e ≠ hNT.outerFace :=
      ProofsInTheBook.ZinanCh35StarConn.nonouter_of_ne_outer (hNT := hNT)
        hface0 htail_e_d0 he_ne_d0
    have h2 : M.dartFace (M.α e) ≠ hNT.outerFace := by
      rw [(ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M) e).symm]
      refine ProofsInTheBook.ZinanCh35StarConn.nonouter_of_ne_outer (hNT := hNT)
        hface0 ?_ ?_
      · rw [M.tail_sigma, htail_e, htail0]
      · -- σ e ≠ d0, else e = σ⁻¹ d0
        intro hσe
        exact he_ne_last (by rw [← hσe, Equiv.symm_apply_apply])
    have hzne : M.head e ≠ v0 := by
      rw [← htail_e]; exact fun h => hNT.simpleGraph.no_loop e (by rw [← h])
    exact ProofsInTheBook.ZinanCh35Chordless.interior_vertex_chord_of_boundary hNT
      (htail0 ▸ ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer (hNT := hNT) hface0)
      htail_e h1 h2 hzne hchord (he_head ▸ hzb)
  empty_iff_base_triangle_of_chordless := hbase







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



/-- **The σ-backward spoke triangle** (R9 §4).  For an inner spoke `e` at `v0`
(`tail e = v0`, `dartFace e ≠ outerFace`) the `φ`-triangle `(e, φ e, φ² e)` has tails
`(v0, head e, head (σ⁻¹ e))`, i.e. it is a `FanTriangle hNT v0 (head e) (head (σ⁻¹ e))`.
The natural local fan triangle points to the σ-**predecessor**. -/
def fanTriangle_of_spoke_pred {v0 : M.Vertex} {e : D}
    (htail : M.tail e = v0) (hinner : M.dartFace e ≠ hNT.outerFace) :
    FanTriangle hNT v0 (M.head e) (M.head (M.σ.symm e)) where
  d0 := e
  d1 := M.φ e
  d2 := M.φ (M.φ e)
  triangle := hNT.inner_face_isFaceTriangle hinner
  inner := hinner
  tail0 := htail
  tail1 := by simp
  tail2 := by
    -- `tail (φ² e) = head (φ e) = head (σ⁻¹ e)`.
    have hcube : (M.φ ^ 3) e = e :=
      faceLen_three_phi_cube_eq_self M hNT.simpleGraph (hNT.inner_faceLen_eq_three hinner)
    have hpred : M.head (M.φ e) = M.head (M.σ.symm e) :=
      ProofsInTheBook.ZinanCh35ChordlessFull.spokeFace_head_eq hcube
    rw [show M.tail (M.φ (M.φ e)) = M.head (M.φ e) from M.tail_phi _, hpred]

/-- The σ-backward spoke triangle has `d0`-dart `= e`, so its face is `dartFace e`. -/
lemma fanTriangle_of_spoke_pred_face {v0 : M.Vertex} {e : D}
    (htail : M.tail e = v0) (hinner : M.dartFace e ≠ hNT.outerFace) :
    (fanTriangle_of_spoke_pred htail hinner).face = M.dartFace e := rfl

/-- Transport a fan triangle along equalities of its two non-apex vertices. -/
def FanTriangle.cong {v0 a a' b b' : M.Vertex} (ha : a = a') (hb : b = b')
    (T : FanTriangle hNT v0 a b) : FanTriangle hNT v0 a' b' :=
  ha ▸ hb ▸ T

/-- `FanTriangle.cong` preserves the face (it only relabels the index vertices). -/
@[simp] lemma FanTriangle.cong_face {v0 a a' b b' : M.Vertex} (ha : a = a') (hb : b = b')
    (T : FanTriangle hNT v0 a b) :
    (FanTriangle.cong ha hb T).face = T.face := by
  subst ha; subst hb; rfl



/-- A pair lies in `consecutivePairs xs` iff it occurs at adjacent indices. -/
lemma mem_consecutivePairs_iff {β : Type*} (xs : List β) (a b : β) :
    (a, b) ∈ NearTriangulation.consecutivePairs xs ↔
      ∃ i : ℕ, ∃ (h : i + 1 < xs.length), xs[i] = a ∧ xs[i + 1] = b := by
  rw [NearTriangulation.consecutivePairs, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hget⟩
    rw [List.length_zip, List.length_tail] at hi
    have hi1 : i + 1 < xs.length := by omega
    have hil : i < xs.length := by omega
    have htl : i < xs.tail.length := by rw [List.length_tail]; omega
    refine ⟨i, hi1, ?_, ?_⟩
    · rw [List.getElem_zip] at hget
      exact (Prod.ext_iff.mp hget).1
    · rw [List.getElem_zip, List.getElem_tail htl] at hget
      exact (Prod.ext_iff.mp hget).2
  · rintro ⟨i, hi1, ha, hb⟩
    have hil : i < xs.length := by omega
    have htl : i < xs.tail.length := by rw [List.length_tail]; omega
    refine ⟨i, ?_, ?_⟩
    · rw [List.length_zip, List.length_tail]; omega
    · rw [List.getElem_zip, List.getElem_tail htl, ha, hb]





variable (hNT)



variable {hNT}

/-- `(vertexDartList d0)[i+1] = σ (vertexDartList d0)[i]` (consecutive non-wrap). -/
lemma vertexDartList_succ {d0 : D} (i : ℕ)
    (hi : i + 1 < (M.vertexDartList d0).length) :
    (M.vertexDartList d0)[i + 1] = M.σ ((M.vertexDartList d0)[i]) := by
  rw [M.vertexDartList_getElem d0 (i + 1) hi,
      M.vertexDartList_getElem d0 i (by omega), pow_succ', Equiv.Perm.coe_mul,
      Function.comp_apply]

/-- **Forward head pair ⟹ a σ-predecessor spoke.**  If `(b, a)` is a σ-forward
consecutive head pair of the star at `d0`, then there is an inner spoke `e` at `v0`
with `head e = a` and `head (σ⁻¹ e) = b`.  Hence `(a, b)` carries a fan triangle. -/
lemma forward_pair_spoke {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hpair : (b, a) ∈ NearTriangulation.consecutivePairs
      ((M.vertexDartList d0).map M.head)) :
    ∃ e : D, M.tail e = v0 ∧ M.dartFace e ≠ hNT.outerFace ∧
      M.head e = a ∧ M.head (M.σ.symm e) = b := by
  rw [mem_consecutivePairs_iff] at hpair
  obtain ⟨i, hi, hb, ha⟩ := hpair
  rw [List.length_map] at hi
  -- the two darts at indices i, i+1
  set D0 := M.vertexDartList d0 with hD0
  have hil : i < D0.length := by omega
  -- D0[i+1] = σ D0[i]
  have hsucc : D0[i + 1] = M.σ (D0[i]) := vertexDartList_succ i hi
  -- the spoke `e := D0[i+1] = σ D0[i]`
  refine ⟨D0[i + 1], ?_, ?_, ?_, ?_⟩
  · -- tail e = v0
    have hmem : D0[i + 1] ∈ D0 := List.getElem_mem _
    rw [M.vertexDartList_tail hσ hmem, htail0]
  · -- inner: e ≠ d0 (since D0[0] = d0 and i+1 ≥ 1, nodup)
    have hmem : D0[i + 1] ∈ D0 := List.getElem_mem _
    have htail_e : M.tail (D0[i + 1]) = M.tail d0 := M.vertexDartList_tail hσ hmem
    refine ProofsInTheBook.ZinanCh35StarConn.nonouter_of_ne_outer (hNT := hNT)
      hface0 htail_e ?_
    -- D0[i+1] ≠ d0
    intro he
    -- d0 = D0[0]
    have hd0 : D0[0]'(M.vertexDartList_length_pos hσ) = d0 := by
      have := M.vertexDartList_getElem d0 0 (M.vertexDartList_length_pos hσ)
      simpa using this
    have hidx : (0 : ℕ) = i + 1 :=
      (List.getElem_inj (h₀ := M.vertexDartList_length_pos hσ) (h₁ := hi)
        (M.vertexDartList_nodup d0)).mp (by rw [hd0]; exact he.symm)
    omega
  · -- head e = a : a = forwardHeads[i+1] = head D0[i+1]
    rw [← ha, List.getElem_map]
  · -- head (σ⁻¹ e) = b : σ⁻¹ e = σ⁻¹ (σ D0[i]) = D0[i] ; b = forwardHeads[i] = head D0[i]
    rw [hsucc, Equiv.symm_apply_apply, ← hb, List.getElem_map]











/-- Any `FanTriangle` at apex `v0` represents a non-outer face incident at `v0`. -/
lemma fanTriangle_faceIncident {v0 a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    NearTriangulation.FaceIncidentAtVertex M T.face v0 :=
  ⟨T.d0, rfl, T.tail0⟩











/-- The σ-forward head list at `v0` (the order fixed by `heads_eq`). -/
def forwardHeads (d0 : D) : List M.Vertex := (M.vertexDartList d0).map M.head

/-- **The σ-predecessor fan triangle for a forward consecutive pair.**  A forward
consecutive pair `(a, b)` of the σ-rotation head list comes from an inner spoke
`e := forwardSpoke` with `head e = b`, `head (σ⁻¹ e) = a`; `fanTriangle_of_spoke_pred`
gives `FanTriangle hNT v0 b a` (the predecessor orientation). -/
noncomputable def forwardTriangle {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (forwardHeads (M := M) d0)) :
    FanTriangle hNT v0 b a :=
  FanTriangle.cong (forward_pair_spoke hσ htail0 hface0 hp).choose_spec.2.2.1
    (forward_pair_spoke hσ htail0 hface0 hp).choose_spec.2.2.2
    (fanTriangle_of_spoke_pred (forward_pair_spoke hσ htail0 hface0 hp).choose_spec.1
      (forward_pair_spoke hσ htail0 hface0 hp).choose_spec.2.1)

/-- `forwardTriangle`'s face is the `dartFace` of the realizing forward spoke. -/
lemma forwardTriangle_face {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (forwardHeads (M := M) d0)) :
    (forwardTriangle hσ htail0 hface0 hp).face =
      M.dartFace (forward_pair_spoke hσ htail0 hface0 hp).choose := by
  rw [forwardTriangle, FanTriangle.cong_face, fanTriangle_of_spoke_pred_face]

/-- **Every inner face at `v0` is the face of some forward consecutive pair.**  The
forward analogue of `exists_backPair_face`: the spoke `d` realizing an inner face `f`
sits at index `k ≥ 1` of the σ-rotation, and the forward consecutive pair at indices
`(k-1, k)` has `forwardTriangle` face `f` (the realizing spoke is `d` by uniqueness). -/
lemma exists_forwardPair_face {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {f : M.Face}
    (hf : f ≠ hNT.outerFace) (hinc : NearTriangulation.FaceIncidentAtVertex M f v0) :
    ∃ (a b : M.Vertex) (hp : (a, b) ∈
        NearTriangulation.consecutivePairs (forwardHeads (M := M) d0)),
      (forwardTriangle hσ htail0 hface0 hp).face = f := by
  obtain ⟨d, hdf, hdt⟩ := hinc
  have hdne : d ≠ d0 := by
    intro h; rw [h] at hdf; exact hf (hdf ▸ hface0)
  have hdmem : d ∈ M.vertexDartList d0 := by
    rw [mem_vertexDartList_iff M hσ]
    exact Quotient.exact (show M.tail d0 = M.tail d by rw [hdt, htail0])
  obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hdmem
  have hd0_0 : (M.vertexDartList d0)[0]'(M.vertexDartList_length_pos hσ) = d0 := by
    have := M.vertexDartList_getElem d0 0 (M.vertexDartList_length_pos hσ); simpa using this
  have hk0 : k ≠ 0 := by
    intro h; subst h
    exact hdne (hkd.symm.trans hd0_0)
  set H := forwardHeads (M := M) d0 with hH
  have hHlen : H.length = (M.vertexDartList d0).length := by
    rw [hH, forwardHeads, List.length_map]
  have hHk : k < H.length := by rw [hHlen]; exact hk
  have hHk1 : k - 1 < H.length := by rw [hHlen]; omega
  have hfwd : (H[k-1], H[k]) ∈ NearTriangulation.consecutivePairs H := by
    rw [mem_consecutivePairs_iff]
    refine ⟨k - 1, by omega, rfl, ?_⟩
    exact getElem_congr (c := H) rfl (by omega) (by omega)
  refine ⟨H[k-1], H[k], hfwd, ?_⟩
  rw [forwardTriangle_face]
  -- `forwardSpoke` is the spoke at `v0` whose head is `H[k] = head d`; identify with `d`.
  obtain ⟨hsptail, hspinner, hsphead, _⟩ :=
    (forward_pair_spoke hσ htail0 hface0 hfwd).choose_spec
  have hHk_eq : H[k] = M.head d := by
    rw [show H[k] = M.head ((M.vertexDartList d0)[k]'(by rw [← hHlen]; exact hHk))
        from List.getElem_map M.head, hkd]
  have hsp_eq : (forward_pair_spoke hσ htail0 hface0 hfwd).choose = d :=
    ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.head_injOn_sameCycle hNT
      hsptail hdt (by rw [hsphead, hHk_eq])
  rw [hsp_eq, hdf]

/-- **The σ-forward `IncidentNonOuterFacesExactly` certificate (the FIX).**  Builds
the (now-σ-corrected) `IncidentNonOuterFacesExactly hNT v0 (forwardHeads d0)`
structure: `triangle_of_pair` is the predecessor-oriented `forwardTriangle`, and
`exact_faces` is the correctly-parenthesized `f ≠ outer → (Incident ↔ Exists)`.  This
is the σ-derived content the σ-forward `FanIncidenceData` / `BoundaryVertexFan`
interface demands; it was uninhabitable under the legacy (forward-oriented,
mis-parenthesized) field. -/
noncomputable def incidentNonOuterFacesExactly_forward {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    NearTriangulation.IncidentNonOuterFacesExactly hNT v0
      (forwardHeads (M := M) d0) where
  triangle_of_pair {_a _b} hp := forwardTriangle hσ htail0 hface0 hp
  exact_faces f hf := by
    constructor
    · intro hinc
      exact exists_forwardPair_face hσ htail0 hface0 hf hinc
    · rintro ⟨a, b, hp, hface⟩
      rw [← hface]
      exact fanTriangle_faceIncident (forwardTriangle hσ htail0 hface0 hp)



namespace Conn

variable {v0 : M.Vertex}





/-- A dart whose tail and head both differ (as `σ`-orbits) from the vertex of `v`
survives the star deletion. -/
lemma notMem_deleteVertexSet_of_tail_head_ne {v d : D}
    (htail : M.tail d ≠ M.tail v) (hhead : M.head d ≠ M.tail v) :
    d ∉ M.deleteVertexSet v := by
  rw [mem_deleteVertexSet_iff]
  simp only [mem_vertexDarts, not_or]
  refine ⟨?_, ?_⟩
  · intro h; exact htail (Quotient.sound h).symm
  · intro h; exact hhead (Quotient.sound h).symm

/-- The middle dart `T.d1` of a fan triangle `(v0, a, b)` survives the deletion of any
dart `d0` representing `v0`. -/
lemma fanTriangle_edge_dart_survives {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d1 ∉ M.deleteVertexSet d0 := by
  have hdist := T.vertices_pairwiseDistinct
  have htail : M.tail T.d1 ≠ M.tail d0 := by
    rw [T.tail1, htail0]; exact (hdist.1).symm
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have hhead : M.head T.d1 ≠ M.tail d0 := by
    rw [hhead_eq, htail0]; exact hdist.2.2
  exact notMem_deleteVertexSet_of_tail_head_ne htail hhead





















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

/-- `forwardHeads d0` is exactly the canonical fan path `fanPath (head d0)
canonInterior (head (σ⁻¹ d0))` used by `OrientationCert`. -/
lemma forwardHeads_eq_canon {d0 : D} (hσ : M.σ d0 ≠ d0) :
    ProofsInTheBook.ZinanCh35FanBackward.forwardHeads (M := M) d0 =
      fanPath (M.head d0)
        (ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0))
        (M.head (M.σ.symm d0)) := by
  rw [ProofsInTheBook.ZinanCh35FanBackward.forwardHeads]
  have h := ProofsInTheBook.ZinanCh35ChordlessFull.pathHeads_decomp (M := M) hσ
  simpa only [ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior] using h

/-- **The σ-forward orientation residue is σ-derived (discharged).**  From `hNT` and
the outgoing boundary spoke `d0` at `v0` (`σ d0 ≠ d0`, `tail d0 = v0`,
`dartFace d0 = outerFace`), the `OrientationCert` — `Nonempty
(IncidentNonOuterFacesExactly hNT v0 (fanPath (head d0) canonInterior (head (σ⁻¹ d0))))`
— holds, with no orientation/chirality input.  This is the planar residue the previous
σ-forward `FanIncidenceData` constructor took as an input; the interface fix makes it a
σ-derivable theorem. -/
theorem orientationCert_discharged {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    ProofsInTheBook.ZinanCh35ChordlessFull.OrientationCert hNT (v0 := v0) (d0 := d0) := by
  refine ⟨?_⟩
  rw [← forwardHeads_eq_canon hσ]
  exact ProofsInTheBook.ZinanCh35FanBackward.incidentNonOuterFacesExactly_forward
    hσ htail0 hface0

/-- **The full `FanIncidenceData` is σ-derived from `hNT` + the boundary spoke + the
base-triangle count.**  With the orientation residue discharged, the only remaining
input to `fanIncidenceData_of_orientation` is the genuine `BaseCount` (the degree-2 ⟺
`V = 3` Euler count). -/
noncomputable def fanIncidenceData_of_baseCount {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hbase : ProofsInTheBook.ZinanCh35ChordlessFull.BaseCount hNT (d0 := d0)) :
    NearTriangulation.FanIncidenceData hNT v0 :=
  ProofsInTheBook.ZinanCh35ChordlessFull.fanIncidenceData_of_orientation hNT
    hσ htail0 hface0 (orientationCert_discharged hσ htail0 hface0) hbase



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

/-- The Case-B seam jump at the old outer exit, once the incoming outer dart is
identified with the first fan spoke.  This is the algebraic core:
`σ bin = φ (α bin) = T.d1`. -/
lemma incoming_outer_exit_jumps_to_head_fan_edge {v0 a b : M.Vertex} {bin : D}
    (hbin_head : M.head bin = v0) (hbin_tail : M.tail bin = a)
    (T : FanTriangle hNT v0 a b) :
    M.σ bin = T.d1 := by
  have hαbin_tail : M.tail (M.α bin) = v0 := by
    rw [tail_alpha, hbin_head]
  have hαbin_head : M.head (M.α bin) = a := by
    rw [head_alpha, hbin_tail]
  have hT0_head : M.head T.d0 = a := by
    calc
      M.head T.d0 = M.tail (M.φ T.d0) := by rw [tail_phi]
      _ = M.tail T.d1 := by rw [T.triangle.1]
      _ = a := T.tail1
  have hspoke : M.α bin = T.d0 :=
    head_injOn_sameCycle hNT hαbin_tail T.tail0
      (hαbin_head.trans hT0_head.symm)
  calc
    M.σ bin = M.φ (M.α bin) := by rw [sigma_apply]
    _ = M.φ T.d0 := by rw [hspoke]
    _ = T.d1 := T.triangle.1

/-- On the old outer cycle, the darts deleted by deleting `v0` are exactly the
incoming and outgoing outer darts at `v0`. -/
lemma old_outer_deleted_iff_eq_bin_or_bout {v0 : M.Vertex} {dDel bin bout d : D}
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    (hd : d ∈ hNT.outerCycle.darts) :
    d ∈ M.deleteVertexSet dDel ↔ d = bin ∨ d = bout := by
  have hbout_mem : bout ∈ hNT.outerCycle.darts := by
    rw [hbout]
    exact hNT.outerCycle.phi_mem_darts hbin_mem
  have hbout_tail : M.tail bout = v0 := by
    rw [hbout, tail_phi, hbin_head]
  constructor
  · intro hdel
    rw [mem_deleteVertexSet_iff] at hdel
    rcases hdel with htail | hhead
    · have hd_tail : M.tail d = v0 := by
        rw [← htailDel]
        exact (Quotient.sound ((mem_vertexDarts M dDel d).mp htail)).symm
      right
      exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hd hbout_mem
        (hd_tail.trans hbout_tail.symm)
    · have hd_head : M.head d = v0 := by
        rw [← htailDel]
        exact (Quotient.sound ((mem_vertexDarts M dDel (M.α d)).mp hhead)).symm
      have hφd_mem : M.φ d ∈ hNT.outerCycle.darts :=
        hNT.outerCycle.phi_mem_darts hd
      have hφd_tail : M.tail (M.φ d) = v0 := by
        rw [tail_phi, hd_head]
      have hφd_eq :
          M.φ d = bout :=
        hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφd_mem hbout_mem
          (hφd_tail.trans hbout_tail.symm)
      left
      apply M.φ.injective
      rw [hφd_eq, hbout]
  · intro h
    rcases h with h | h
    · subst d
      exact mem_deleteVertexSet_of_head (M := M) (v0 := v0) htailDel hbin_head
    · subst d
      rw [mem_deleteVertexSet_iff]
      left
      rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail dDel = M.tail bout by
        rw [htailDel, hbout_tail])

/-- If `dOut` is the outgoing outer dart at `v0` and `bin` is the incoming outer
dart with `M.φ bin = dOut`, then the tail of `bin` is the other fan endpoint
`head (σ⁻¹ dOut)`. -/
lemma incoming_outer_tail_eq_head_sigma_symm {v0 : M.Vertex} {dOut bin : D}
    (hfaceOut : M.dartFace dOut = hNT.outerFace)
    (htailOut : M.tail dOut = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (_hphi : M.φ bin = dOut) :
    M.tail bin = M.head (M.σ.symm dOut) := by
  have hv0 : hNT.outerCycle.IsBoundaryVertex v0 := by
    simpa [htailOut] using
      (ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer
        (hNT := hNT) hfaceOut)
  obtain ⟨_bin0, _hb0, huniq⟩ := hNT.exists_unique_outer_head hv0
  have hαface : M.dartFace (M.α (M.σ.symm dOut)) = hNT.outerFace := by
    have hkey : M.dartFace (M.σ (M.σ.symm dOut)) =
        M.dartFace (M.α (M.σ.symm dOut)) := by
      have hφeq : M.φ (M.α (M.σ.symm dOut)) = M.σ (M.σ.symm dOut) := by
        simp [φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
      calc M.dartFace (M.σ (M.σ.symm dOut))
          = M.dartFace (M.φ (M.α (M.σ.symm dOut))) := by rw [hφeq]
        _ = M.dartFace (M.α (M.σ.symm dOut)) := M.dartFace_phi _
    rw [Equiv.apply_symm_apply] at hkey
    rw [← hkey]
    exact hfaceOut
  have hαmem : M.α (M.σ.symm dOut) ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff _).2 hαface
  have hαhead : M.head (M.α (M.σ.symm dOut)) = v0 := by
    rw [head_alpha]
    have htail : M.tail (M.σ.symm dOut) = M.tail dOut := by
      have h := M.tail_sigma (M.σ.symm dOut)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    rw [htail, htailOut]
  have hinc : M.α (M.σ.symm dOut) = bin :=
    huniq (M.α (M.σ.symm dOut)) ⟨hαmem, hαhead⟩ |>.trans
      (huniq bin ⟨hbin_mem, hbin_head⟩).symm
  rw [← hinc, tail_alpha]

/-- The cyclic predecessor `oPre` of the incoming outer dart survives the deletion:
the only deleted darts on the old outer face are `bin` and `bout = φ bin`, and
`outer_len ≥ 3` rules out `oPre` being either of them. -/
lemma old_outer_predecessor_survives {v0 : M.Vertex} {dDel bin bout oPre : D}
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    (hoPre_mem : oPre ∈ hNT.outerCycle.darts)
    (hoPre_phi : M.φ oPre = bin) :
    oPre ∉ M.deleteVertexSet dDel := by
  intro hdel
  have hclass :=
    (old_outer_deleted_iff_eq_bin_or_bout (hNT := hNT) htailDel hbin_mem
      hbin_head hbout hoPre_mem).1 hdel
  rcases hclass with hopre_bin | hopre_bout
  · have hφbin : M.φ bin = bin := by
      simpa [hopre_bin] using hoPre_phi
    exact phi_ne_self_of_isSimpleGraph M hNT.simpleGraph bin hφbin
  · have hφ2 : M.φ (M.φ bin) = bin := by
      calc
        M.φ (M.φ bin) = M.φ bout := by rw [← hbout]
        _ = M.φ oPre := by rw [hopre_bout]
        _ = bin := hoPre_phi
    have hφ : M.φ bin ≠ bin :=
      phi_ne_self_of_isSimpleGraph M hNT.simpleGraph bin
    have hcard2 : (M.φ.cycleOf bin).support.card = 2 :=
      card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
    have hbin_face : M.dartFace bin = hNT.outerFace :=
      hNT.outerCycle.dartFace_of_mem_darts hbin_mem
    have hface2 : M.faceLen hNT.outerFace = 2 := by
      have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
      rw [hbin_face, hcard2] at hsupport
      exact hsupport
    have hlen2 : hNT.outerCycle.length = 2 :=
      hNT.outerCycle.faceLen_eq_length.symm.trans hface2
    have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
    omega

/-- Every surviving old-outer dart reaches the predecessor `oPre` of the incoming
outer dart `bin` by a forward `M.φ`-run that stays outside the deleted star.  This
uses the previous classification of deleted old-outer darts and a first-hit
argument for `bin`, avoiding any global list equality for the rotated boundary
cycle. -/
lemma old_outer_survivor_run_to_exit {v0 : M.Vertex} {dDel bin bout oPre : D}
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    (hoPre_phi : M.φ oPre = bin)
    (x : {d : D // d ∉ M.deleteVertexSet dDel})
    (hxouter : M.dartFace x.1 = hNT.outerFace) :
    ∃ k : ℕ, (∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet dDel) ∧
      (M.φ ^ k) x.1 = oPre := by
  have hbin_face : M.dartFace bin = hNT.outerFace :=
    hNT.outerCycle.dartFace_of_mem_darts hbin_mem
  have hsame : M.φ.SameCycle x.1 bin := by
    exact Quotient.exact (show M.dartFace x.1 = M.dartFace bin by
      rw [hxouter, hbin_face])
  obtain ⟨n0, hn0⟩ := hsame.exists_nat_pow_eq
  let hhit : ∃ n : ℕ, (M.φ ^ n) x.1 = bin := ⟨n0, hn0⟩
  set n := Nat.find hhit with hn_def
  have hn : (M.φ ^ n) x.1 = bin := by
    rw [hn_def]
    exact Nat.find_spec hhit
  have hbin_deleted : bin ∈ M.deleteVertexSet dDel :=
    mem_deleteVertexSet_of_head (M := M) (v0 := v0) htailDel hbin_head
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    have hxbin : x.1 = bin := by simpa [hn0] using hn
    exact x.2 (hxbin ▸ hbin_deleted)
  have hface_iter_all : ∀ j : ℕ, M.dartFace ((M.φ ^ j) x.1) = hNT.outerFace := by
    intro j
    induction j with
    | zero => simpa using hxouter
    | succ j ih =>
        have hsucc : (M.φ ^ Nat.succ j) x.1 = M.φ ((M.φ ^ j) x.1) := by
          rw [Nat.succ_eq_add_one, pow_succ']; rfl
        rw [hsucc, dartFace_phi]
        exact ih
  set k := n - 1 with hkdef
  have hn_eq : n = k + 1 := by omega
  refine ⟨k, ?_, ?_⟩
  · intro j hj hdel
    have hface_iter : M.dartFace ((M.φ ^ j) x.1) = hNT.outerFace := hface_iter_all j
    have hmem_iter : (M.φ ^ j) x.1 ∈ hNT.outerCycle.darts :=
      (hNT.outerCycle.mem_darts_iff _).2 hface_iter
    have hclass :=
      (old_outer_deleted_iff_eq_bin_or_bout (hNT := hNT) htailDel hbin_mem
        hbin_head hbout hmem_iter).1 hdel
    rcases hclass with hhit_bin | hhit_bout
    · have hjlt : j < n := by omega
      exact (Nat.find_min (p := fun m => (M.φ ^ m) x.1 = bin)
        hhit hjlt) hhit_bin
    · cases j with
      | zero =>
          have hx_bout : x.1 = bout := by simpa using hhit_bout
          have hbout_mem : bout ∈ hNT.outerCycle.darts := by
            rw [hbout]
            exact hNT.outerCycle.phi_mem_darts hbin_mem
          have hbout_deleted : bout ∈ M.deleteVertexSet dDel :=
            (old_outer_deleted_iff_eq_bin_or_bout (hNT := hNT) htailDel hbin_mem
              hbin_head hbout hbout_mem).2 (Or.inr rfl)
          exact x.2 (hx_bout ▸ hbout_deleted)
      | succ j' =>
          have hprev : (M.φ ^ j') x.1 = bin := by
            have hsucc : (M.φ ^ Nat.succ j') x.1 = M.φ ((M.φ ^ j') x.1) := by
              rw [Nat.succ_eq_add_one, pow_succ']; rfl
            apply M.φ.injective
            rw [← hsucc, hhit_bout, hbout]
          have hjlt : j' < n := by omega
          exact (Nat.find_min (p := fun m => (M.φ ^ m) x.1 = bin)
            hhit hjlt) hprev
  · apply M.φ.injective
    have hsucc : (M.φ ^ (k + 1)) x.1 = M.φ ((M.φ ^ k) x.1) := by
      rw [pow_succ']; rfl
    rw [← hsucc, ← hn_eq, hn, hoPre_phi]

/-- Assemble `MergedOuterArcData` from the endpoint seam facts.  This is the
non-circular STAGE-A constructor: the old-outer survivor run and the Case-B jump
are proved above; the remaining inputs are exactly the endpoint alignments between
the old incoming boundary dart and the fan triangle edge where the seam actually
enters the fan chain. -/
def mergedOuterArcData_of_head_seam {v0 a b : M.Vertex}
    {dDel bin bout oPre : D}
    (r : {d : D // d ∉ M.deleteVertexSet dDel})
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbin_tail : M.tail bin = a)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet dDel)
    (hoPre_phi : M.φ oPre = bin)
    (T : FanTriangle hNT v0 a b)
    (hr : r.1 = T.d1) :
    MergedOuterArcData M dDel r hNT.outerFace :=
  hNT.mergedOuterArcData_of_exit (v0 := v0) r htailDel
    ⟨oPre, hoPre_surv⟩
    (by
      rw [hNT.outerCycle.mem_darts_iff]
      rw [← hNT.outerCycle.dartFace_of_mem_darts hbin_mem, ← hoPre_phi, dartFace_phi])
    (by rw [hoPre_phi, hbin_head])
    (by rw [hoPre_phi, incoming_outer_exit_jumps_to_head_fan_edge hbin_head hbin_tail T, ← hr])
    (old_outer_survivor_run_to_exit (hNT := hNT) htailDel hbin_mem hbin_head hbout hoPre_phi)

/-- The same seam constructor specialized to a canonical edge of a boundary fan.
For a consecutive pair `(a,b)` in the fan path, the stored triangle has type
`FanTriangle hNT v0 b a`; hence the incoming old-outer dart must have tail `b`.
This is the actual-seam form used when the Case-B jump enters at the end of the
fan chain rather than at the head. -/
noncomputable def mergedOuterArcData_of_fan_pair_seam
    (fan : BoundaryVertexFan hNT v0) {dDel bin bout oPre : D}
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet dDel)
    (hoPre_phi : M.φ oPre = bin) :
    MergedOuterArcData M dDel
      ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
        ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
          (fan.incident_faces_exact.triangle_of_pair hp) htailDel⟩
      hNT.outerFace :=
  mergedOuterArcData_of_head_seam
    (r := ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htailDel⟩)
    htailDel hbin_mem hbin_head hbin_tail hbout hoPre_surv hoPre_phi
    (fan.incident_faces_exact.triangle_of_pair hp) rfl

/-- The fan-pair seam data is attached to a canonical fan edge. -/
lemma fanPairSeamEdge_is_fan_edge
    (fan : BoundaryVertexFan hNT v0) {dDel : D} (htailDel : M.tail dDel = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path) :
    FanTriangleEdge fan
      (⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
        ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
          (fan.incident_faces_exact.triangle_of_pair hp) htailDel⟩ :
        {d : D // d ∉ M.deleteVertexSet dDel}) :=
  ⟨a, b, hp, rfl⟩

/-- STAGE A+B seam closure from the actual fan-edge package.  The old outer arc
may enter at any canonical fan edge; the fan-chain theorem transports that entry
edge to the whole merged orbit. -/
theorem deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
    (fan : BoundaryVertexFan hNT v0) (hchord : BoundaryChordless hNT.outerCycle)
    {dDel bin bout oPre : D} (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet dDel)
    (hoPre_phi : M.φ oPre = bin) :
    DeleteVertexMergedFaceSingleOrbit M dDel :=
  deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc_edge fan hchord htailDel
    (⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htailDel⟩)
    (fanPairSeamEdge_is_fan_edge fan htailDel hp)
    (mergedOuterArcData_of_fan_pair_seam fan htailDel hbin_mem hbin_head hp hbin_tail
      hbout hoPre_surv hoPre_phi)

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



/-- The bundled discrete-Jordan seam data of the chordless boundary-vertex
deletion: the merged outer-arc reconnection, the normalized merged boundary cycle,
and the clean-face classification. -/
structure DeletedSeamData (fan : BoundaryVertexFan hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle) {d0 : D} (htail0 : M.tail d0 = v0)
    where
  /-- The actual fan-triangle edge where the surviving old-outer arc enters the
  fan chain. -/
  seamEdge : {d : D // d ∉ M.deleteVertexSet d0}
  /-- The seam edge is one of the fan's canonical triangle edge darts. -/
  seamEdge_fan : FanTriangleEdge fan seamEdge
  /-- The outer-arc reconnection data at the actual seam edge: the surviving
  old-outer arc is one contiguous forward `M.φ`-run whose Case-B exit jump lands
  on `seamEdge`.  The fan-chain calculus transports this edge to the rest of the
  fan internally.  (R10 Layer B seam.) -/
  mergedArc : MergedOuterArcData M d0 seamEdge hNT.outerFace
  /-- The merged outer face of the deleted map. -/
  outerFace : (M.deleteVertex d0).Face
  /-- The normalized `φ'`-boundary cycle of the merged outer face. -/
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  /-- Its boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- Its boundary has length at least three. -/
  outer_len_ge_three : 3 ≤ outerCycle.length
  /-- Every non-outer deleted face is a clean, `M`-non-outer survivor (the merged
  outer face captures exactly the `v0`-incident orbit).  (R10 Layer C.) -/
  cleanFaceClass : CleanFaceClass (hNT := hNT) outerFace

namespace DeletedSeamData

variable {fan : BoundaryVertexFan hNT v0} {hchord : BoundaryChordless hNT.outerCycle}
  {d0 : D} {htail0 : M.tail d0 = v0}



/-- **`DeleteVertexMergedFaceSingleOrbit M d0`, σ-derived from the seam data.**
The `t + 1`-triangle backbone is discharged *unconditionally* from the fan
(closed-form `φ'`-successor chaining through the shared `v0`-spoke); the single
seam input is the outer-arc reconnection `mergedArc`.  This is the `φ`-level
itinerary of the merged boundary — not a posited single-orbit assertion, but the
reconnection derived by the proved `φ'`-iterate calculus. -/
theorem mergedFaceSingleOrbit (data : DeletedSeamData fan hchord htail0) :
    DeleteVertexMergedFaceSingleOrbit M d0 :=
  deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc_edge fan hchord htail0
    data.seamEdge data.seamEdge_fan data.mergedArc



/-- **`DeletedOuterBoundary hNT d0`, σ-derived from the seam data.**  The
orbit-algebraic boundary-cycle fields come from the supplied normalized cycle
(`DeletedOuterBoundary.ofMergedFace` would re-derive them from a root dart; here
we already carry the full cycle); the `inner_tri` field is discharged via the
*face-SIZE* route (`deleteVertex_inner_tri_of_cleanFaceClass`) from
`cleanFaceClass`, sidestepping the `CutFaceLabel` face-COUNT refutation exactly as
the chord side did. -/
noncomputable def deletedOuterBoundary (data : DeletedSeamData fan hchord htail0) :
    DeletedOuterBoundary hNT d0 :=
  deletedOuterBoundary_of_cleanFaceClass htail0 data.outerFace data.outerCycle
    data.outer_simple data.outer_len_ge_three data.cleanFaceClass



/-- **The full `FanSurgeryReconstruction hNT d0`, σ-derived from the seam data.**
All three dart-rotation surgery fields (`vertexQuotient`, `facesMerge`,
`connected`) come from the fan; the merged-orbit seam fact and the merged
boundary data come from `data`.  This is the chordless drop-in for
`ChordlessOracleResidual`'s `recon` field. -/
noncomputable def chordlessRecon (data : DeletedSeamData fan hchord htail0) :
    FanSurgeryReconstruction hNT d0 :=
  chordlessRecon_of_bdry fan htail0 (data.mergedFaceSingleOrbit) data.deletedOuterBoundary











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

/-- A small list-cardinality repackaging used by the route-(b) itinerary: three
pairwise distinct listed elements force length at least three. -/
lemma three_le_length_of_three_mem {α : Type u} [DecidableEq α] {L : List α}
    {a b c : α} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ L.length := by
  classical
  let S : Finset α := {a, b, c}
  have hSsub : S ⊆ L.toFinset := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [List.mem_toFinset]
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcardS : S.card = 3 := by
    simp [S, hab, hac, hbc]
  have hle_card : 3 ≤ L.toFinset.card := by
    rw [← hcardS]
    exact Finset.card_le_card hSsub
  exact hle_card.trans (List.toFinset_card_le L)



/-- The fan path has a terminal consecutive pair ending at `fan.w`. -/
lemma exists_terminal_fan_pair (fan : BoundaryVertexFan hNT v0) :
    ∃ a : M.Vertex, (a, fan.w) ∈ consecutivePairs fan.path := by
  classical
  have hterm : ∀ (x : M.Vertex) (l : List M.Vertex),
      ∃ a : M.Vertex, (a, fan.w) ∈ consecutivePairs (x :: l ++ [fan.w]) := by
    intro x l
    induction l generalizing x with
    | nil =>
        refine ⟨x, ?_⟩
        simp [consecutivePairs]
    | cons z zs ih =>
        rcases ih z with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        simp [consecutivePairs] at ha ⊢
        exact Or.inr ha
  rw [BoundaryVertexFan.path, fanPath]
  exact hterm fan.x fan.interior



/-- The old outer face is incident with the deleted vertex when `bin` is the
incoming outer dart and `bout = φ bin` is the outgoing outer dart at `v0`. -/
lemma oldOuterFace_incident_of_seam {d0 bin bout : D}
    (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin) :
    hNT.outerFace ∈ M.vertexFaces d0 := by
  classical
  rw [vertexFaces, Finset.mem_image]
  refine ⟨bout, ?_, ?_⟩
  · rw [mem_vertexDarts]
    have hbout_tail : M.tail bout = v0 := by
      rw [hbout, tail_phi, hbin_head]
    exact Quotient.exact (show M.tail d0 = M.tail bout by rw [htail0, hbout_tail])
  · have hbout_face : M.dartFace bout = hNT.outerFace := by
      rw [hbout, dartFace_phi]
      exact hNT.outerCycle.dartFace_of_mem_darts hbin_mem
    exact hbout_face

/-- A canonical fan-pair seam edge lies on a face incident with the deleted vertex. -/
lemma fanPairSeamEdge_incident
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path) :
    M.dartFace (fan.incident_faces_exact.triangle_of_pair hp).d1 ∈
      M.vertexFaces d0 := by
  classical
  set T := fan.incident_faces_exact.triangle_of_pair hp
  rw [vertexFaces, Finset.mem_image]
  refine ⟨T.d0, ?_, ?_⟩
  · rw [mem_vertexDarts]
    exact Quotient.exact (show M.tail d0 = M.tail T.d0 by rw [htail0, T.tail0])
  · have hface : M.dartFace T.d1 = M.dartFace T.d0 := by
      rw [← T.triangle.1, dartFace_phi]
    exact hface.symm

/-- Incident-with-`v0` is invariant along deleted-map `φ'` cycles.  This is the
public form needed for the route-(b) orbit classifier. -/
lemma incident_invariant_of_sameCycle {d0 : D} (htail0 : M.tail d0 = v0)
    {x y : {d : D // d ∉ M.deleteVertexSet d0}}
    (hxy : (M.deleteVertex d0).φ.SameCycle x y) :
    M.dartFace x.1 ∈ M.vertexFaces d0 ↔ M.dartFace y.1 ∈ M.vertexFaces d0 := by
  constructor
  · intro hx
    by_contra hy
    have hMsc : M.φ.SameCycle y.1 x.1 :=
      (cleanSameCycle_iff htail0 y hy x).1 hxy.symm
    have hface : M.dartFace y.1 = M.dartFace x.1 :=
      Quotient.sound hMsc
    exact hy (by rw [hface]; exact hx)
  · intro hy
    by_contra hx
    have hMsc : M.φ.SameCycle x.1 y.1 :=
      (cleanSameCycle_iff htail0 x hx y).1 hxy
    have hface : M.dartFace x.1 = M.dartFace y.1 :=
      Quotient.sound hMsc
    exact hx (by rw [hface]; exact hy)

/-- Any incident survivor lies on the `faceDartList` of an incident root once the
merged-orbit theorem is available. -/
lemma incident_survivor_mem_faceDartList_of_mergedOrbit
    (hNT : NearTriangulation M) {d0 : D}
    (r y : {d : D // d ∉ M.deleteVertexSet d0})
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (hy_incident : M.dartFace y.1 ∈ M.vertexFaces d0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    y ∈ (M.deleteVertex d0).faceDartList r := by
  rw [CombMap.faceDartList, Equiv.Perm.mem_toList_iff]
  exact ⟨hmerge r y hr_incident hy_incident,
    Equiv.Perm.mem_support.2
      (phi_ne_self_of_isSimpleGraph (M.deleteVertex d0)
        (ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.deleteVertex_isSimpleGraph
          hNT d0) r)⟩

/-- Conversely, every dart listed in the merged root's `faceDartList` is incident
with the deleted vertex. -/
lemma incident_of_mem_faceDartList_root {d0 : D} (htail0 : M.tail d0 = v0)
    (r y : {d : D // d ∉ M.deleteVertexSet d0})
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (hy : y ∈ (M.deleteVertex d0).faceDartList r) :
    M.dartFace y.1 ∈ M.vertexFaces d0 := by
  rw [CombMap.faceDartList, Equiv.Perm.mem_toList_iff] at hy
  exact (incident_invariant_of_sameCycle htail0 hy.1).1 hr_incident

/-- Route-(b) membership classifier for the merged root's explicit face dart
list: it is exactly the list of surviving darts whose old `M`-face is incident
with the deleted vertex. -/
theorem mem_faceDartList_root_iff_incident
    (hNT : NearTriangulation M) {d0 : D} (htail0 : M.tail d0 = v0)
    (r y : {d : D // d ∉ M.deleteVertexSet d0})
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    y ∈ (M.deleteVertex d0).faceDartList r ↔
      M.dartFace y.1 ∈ M.vertexFaces d0 :=
  ⟨fun hy => incident_of_mem_faceDartList_root htail0 r y hr_incident hy,
    fun hy => incident_survivor_mem_faceDartList_of_mergedOrbit hNT r y
      hr_incident hy hmerge⟩

lemma fanTriangle_edge_face {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.dartFace T.d1 = M.dartFace T.d0 := by
  rw [← T.triangle.1, dartFace_phi]

lemma fanTriangle_edge_ne_outer_dart {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d : D}
    (hdouter : M.dartFace d = hNT.outerFace) :
    T.d1 ≠ d := by
  intro h
  exact T.inner (by
    rw [← hdouter, ← h]
    exact (fanTriangle_edge_face T).symm)

lemma old_outer_predecessor_face {bin oPre : D}
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hoPre_phi : M.φ oPre = bin) :
    M.dartFace oPre = hNT.outerFace := by
  rw [← hNT.outerCycle.dartFace_of_mem_darts hbin_mem, ← hoPre_phi, dartFace_phi]



/-- The last fan-triangle dart points back to the apex. -/
lemma fanTriangle_head2 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d2 = v0 := by
  have hphi : M.φ T.d2 = T.d0 := T.triangle.2.2
  have hh : M.head T.d2 = M.tail T.d0 := by rw [← tail_phi, hphi]
  rw [hh, T.tail0]

/-- The last dart of a fan triangle is deleted by closed-star deletion at the
fan apex. -/
lemma fanTriangle_d2_deleted {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d2 ∈ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]; right
  rw [mem_vertexDarts]
  exact Quotient.exact (show M.tail d0 = M.tail (M.α T.d2) by
    rw [tail_alpha, fanTriangle_head2, htail0])

/-- A surviving dart on a fan-triangle face is the triangle's surviving edge dart. -/
lemma survivor_on_fanTriangle_eq_d1 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hface : M.dartFace x.1 = T.face) :
    x.1 = T.d1 := by
  have hdf1 : M.dartFace T.d1 = T.face := by
    rw [FanTriangle.face, ← T.triangle.1, dartFace_phi]
  have hlen : M.faceLen (M.dartFace T.d1) = 3 := by
    rw [hdf1]; exact T.faceLen_eq_three
  have hsame : M.φ.SameCycle T.d1 x.1 :=
    Quotient.exact (show M.dartFace T.d1 = M.dartFace x.1 by rw [hdf1, hface])
  have hφ : M.φ T.d1 ≠ T.d1 := phi_ne_self_of_isSimpleGraph M hNT.simpleGraph T.d1
  have hsupp : T.d1 ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  have hcard : (M.φ.cycleOf T.d1).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφ, hlen]
  obtain ⟨i, hi, hpow⟩ := hsame.exists_pow_eq_of_mem_support hsupp
  rw [hcard] at hi
  have h01 : M.φ T.d1 = T.d2 := T.triangle.2.1
  have h12 : M.φ T.d2 = T.d0 := T.triangle.2.2
  interval_cases i
  · simpa using hpow.symm
  · exfalso
    have : x.1 = T.d2 := by simpa [h01] using hpow.symm
    exact x.2 (this ▸ fanTriangle_d2_deleted T htail0)
  · exfalso
    have hx0 : x.1 = T.d0 := by
      have h2 : (M.φ ^ 2) T.d1 = T.d0 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ', pow_one]
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, h01, h12]
      rw [h2] at hpow
      exact hpow.symm
    have hd0del : T.d0 ∈ M.deleteVertexSet d0 := by
      rw [mem_deleteVertexSet_iff]; left
      rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail d0 = M.tail T.d0 by rw [htail0, T.tail0])
    exact x.2 (hx0 ▸ hd0del)

/-- Convert membership in `vertexFaces d0` into ordinary face incidence at `v0`. -/
lemma faceIncidentAtVertex_of_incident {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hx : M.dartFace x.1 ∈ M.vertexFaces d0) :
    FaceIncidentAtVertex M (M.dartFace x.1) v0 := by
  rw [vertexFaces, Finset.mem_image] at hx
  obtain ⟨e, he, hef⟩ := hx
  rw [mem_vertexDarts] at he
  refine ⟨e, hef, ?_⟩
  have : M.tail d0 = M.tail e := Quotient.sound he
  exact this ▸ htail0

/-- Every non-outer incident survivor is one of the canonical fan-triangle edge
darts. -/
lemma incident_nonouter_survivor_eq_fan_edge
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hxinc : M.dartFace x.1 ∈ M.vertexFaces d0)
    (hxnonouter : M.dartFace x.1 ≠ hNT.outerFace) :
    ∃ a b : M.Vertex, ∃ hp : (a, b) ∈ consecutivePairs fan.path,
      x.1 = (fan.incident_faces_exact.triangle_of_pair hp).d1 := by
  have hinc : FaceIncidentAtVertex M (M.dartFace x.1) v0 :=
    faceIncidentAtVertex_of_incident htail0 x hxinc
  obtain ⟨a, b, hp, hface⟩ :=
    (fan.incident_faces_exact.exact_faces (M.dartFace x.1) hxnonouter).1 hinc
  refine ⟨a, b, hp, ?_⟩
  exact survivor_on_fanTriangle_eq_d1
    (fan.incident_faces_exact.triangle_of_pair hp) htail0 x hface.symm

/-- In a nodup path, a vertex has at most one predecessor in the consecutive-pair
list. -/
lemma consecutivePairs_left_eq_of_same_right {α : Type u} {xs : List α}
    (hnodup : xs.Nodup) {a c b : α}
    (hab : (a, b) ∈ consecutivePairs xs)
    (hcb : (c, b) ∈ consecutivePairs xs) :
    a = c := by
  obtain ⟨i, hi, hai, hbi⟩ :=
    (ProofsInTheBook.ZinanCh35FanBackward.mem_consecutivePairs_iff xs a b).1 hab
  obtain ⟨j, hj, hcj, hbj⟩ :=
    (ProofsInTheBook.ZinanCh35FanBackward.mem_consecutivePairs_iff xs c b).1 hcb
  have hidx : i + 1 = j + 1 := by
    exact (List.getElem_inj hnodup).1 (by rw [hbi, hbj])
  have hij : i = j := by omega
  have hget : xs[i] = xs[j] := by
    subst hij
    rfl
  exact hai.symm.trans (hget.trans hcj)

/-- Equality of deleted-map vertices lifts to equality of old-map tails for
surviving darts. -/
lemma M_tail_eq_of_deleted_tail_eq {d0 : D}
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hxy : (M.deleteVertex d0).tail x = (M.deleteVertex d0).tail y) :
    M.tail x.1 = M.tail y.1 := by
  have hsc' : (M.deleteVertex d0).σ.SameCycle x y := Quotient.exact hxy
  have hsc : M.σ.SameCycle x.1 y.1 :=
    (deleteVertex_sigma_sameCycle_iff M d0 x y).1 hsc'
  exact Quotient.sound hsc

/-- Tail injectivity on the fan-triangle part of the merged deleted boundary. -/
lemma incident_nonouter_survivor_eq_of_deleted_tail_eq
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hxinc : M.dartFace x.1 ∈ M.vertexFaces d0)
    (hyinc : M.dartFace y.1 ∈ M.vertexFaces d0)
    (hxnonouter : M.dartFace x.1 ≠ hNT.outerFace)
    (hynonouter : M.dartFace y.1 ≠ hNT.outerFace)
    (hxy : (M.deleteVertex d0).tail x = (M.deleteVertex d0).tail y) :
    x = y := by
  obtain ⟨a, b, hp, hxval⟩ :=
    incident_nonouter_survivor_eq_fan_edge fan htail0 x hxinc hxnonouter
  obtain ⟨c, d, hq, hyval⟩ :=
    incident_nonouter_survivor_eq_fan_edge fan htail0 y hyinc hynonouter
  have hMtail : M.tail x.1 = M.tail y.1 :=
    M_tail_eq_of_deleted_tail_eq x y hxy
  have hbd : b = d := by
    have hxb : M.tail x.1 = b := by
      rw [hxval]
      exact (fan.incident_faces_exact.triangle_of_pair hp).tail1
    have hyd : M.tail y.1 = d := by
      rw [hyval]
      exact (fan.incident_faces_exact.triangle_of_pair hq).tail1
    rw [hxb, hyd] at hMtail
    exact hMtail
  subst hbd
  have hac : a = c :=
    consecutivePairs_left_eq_of_same_right
      (fan_path_simple_of_chordless hNT fan hchordless) hp hq
  subst hac
  have hhp : hp = hq := Subsingleton.elim _ _
  subst hhp
  exact Subtype.ext (hxval.trans hyval.symm)

/-- Tail injectivity on the surviving old-outer-arc part. -/
lemma old_outer_survivor_eq_of_deleted_tail_eq {d0 : D}
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hxouter : M.dartFace x.1 = hNT.outerFace)
    (hyouter : M.dartFace y.1 = hNT.outerFace)
    (hxy : (M.deleteVertex d0).tail x = (M.deleteVertex d0).tail y) :
    x = y := by
  have hxmem : x.1 ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff x.1).2 hxouter
  have hymem : y.1 ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff y.1).2 hyouter
  have hMtail : M.tail x.1 = M.tail y.1 :=
    M_tail_eq_of_deleted_tail_eq x y hxy
  exact Subtype.ext
    (hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hxmem hymem hMtail)

/-- In the chordless fan path, the second endpoint of a consecutive pair cannot
be the head endpoint `fan.x`; if it is an old boundary vertex, it is `fan.w`. -/
lemma consecutivePair_second_eq_w_of_boundary
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hb_boundary : hNT.outerCycle.IsBoundaryVertex b) :
    b = fan.w := by
  have hb_path : b ∈ fan.path := by
    obtain ⟨i, hi, _ha, hb⟩ :=
      (ProofsInTheBook.ZinanCh35FanBackward.mem_consecutivePairs_iff
        fan.path a b).1 hp
    exact List.mem_iff_getElem.2 ⟨i + 1, hi, hb⟩
  rcases fan_path_meets_old_boundary_only_at_ends hNT fan hchordless b hb_path
      hb_boundary with hbx | hbw
  · exfalso
    obtain ⟨i, hi, _ha, hb⟩ :=
      (ProofsInTheBook.ZinanCh35FanBackward.mem_consecutivePairs_iff
        fan.path a b).1 hp
    have hpath0 : fan.path[0] = fan.x := by
      simp [BoundaryVertexFan.path, fanPath]
    have hidx : i + 1 = 0 := by
      exact (List.getElem_inj (fan_path_simple_of_chordless hNT fan hchordless)).1
        (by rw [hb, hbx, hpath0])
    omega
  · exact hbw

/-- The tail of any old-outer dart is an old boundary vertex. -/
lemma isBoundaryVertex_tail_of_outer_dart {d : D}
    (hdouter : M.dartFace d = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryVertex (M.tail d) := by
  have hdmem : d ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff d).2 hdouter
  have hmem : M.tail d ∈ hNT.outerCycle.darts.map M.tail :=
    List.mem_map.2 ⟨d, hdmem, rfl⟩
  simpa [BoundaryCycle.IsBoundaryVertex, hNT.outerCycle.vertices_eq] using hmem

/-- A non-outer fan-edge survivor and an old-outer survivor cannot represent the
same deleted boundary vertex. -/
lemma incident_nonouter_not_old_outer_same_deleted_tail
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {d0 bin : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hpₛ : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hxinc : M.dartFace x.1 ∈ M.vertexFaces d0)
    (hxnonouter : M.dartFace x.1 ≠ hNT.outerFace)
    (hyouter : M.dartFace y.1 = hNT.outerFace)
    (hxy : (M.deleteVertex d0).tail x = (M.deleteVertex d0).tail y) :
    False := by
  obtain ⟨a, b, hp, hxval⟩ :=
    incident_nonouter_survivor_eq_fan_edge fan htail0 x hxinc hxnonouter
  have hMtail : M.tail x.1 = M.tail y.1 :=
    M_tail_eq_of_deleted_tail_eq x y hxy
  have hxb : M.tail x.1 = b := by
    rw [hxval]
    exact (fan.incident_faces_exact.triangle_of_pair hp).tail1
  have hyb : M.tail y.1 = b := hMtail.symm.trans hxb
  have hb_boundary : hNT.outerCycle.IsBoundaryVertex b := by
    rw [← hyb]
    exact isBoundaryVertex_tail_of_outer_dart hyouter
  have hb_w : b = fan.w :=
    consecutivePair_second_eq_w_of_boundary fan hchordless hp hb_boundary
  have hbin_boundary : hNT.outerCycle.IsBoundaryVertex bₛ := by
    rw [← hbin_tail]
    exact isBoundaryVertex_tail_of_outer_dart
      (hNT.outerCycle.dartFace_of_mem_darts hbin_mem)
  have hbs_w : bₛ = fan.w :=
    consecutivePair_second_eq_w_of_boundary fan hchordless hpₛ hbin_boundary
  have hy_tail_bin : M.tail y.1 = M.tail bin := by
    rw [hyb, hb_w, hbin_tail, hbs_w]
  have hymem : y.1 ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff y.1).2 hyouter
  have hy_eq_bin : y.1 = bin :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hymem hbin_mem hy_tail_bin
  have hbin_deleted : bin ∈ M.deleteVertexSet d0 :=
    mem_deleteVertexSet_of_head (M := M) (v0 := v0) htail0 hbin_head
  exact y.2 (hy_eq_bin ▸ hbin_deleted)

/-- Route-(b) boundary simplicity for the merged deleted face rooted at the
actual fan-pair seam edge. -/
theorem deleted_outer_simple_of_fan_pair_seam
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hpₛ : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin) :
    ((((M.deleteVertex d0).faceDartList
        (⟨(fan.incident_faces_exact.triangle_of_pair hpₛ).d1,
          ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
            (fan.incident_faces_exact.triangle_of_pair hpₛ) htail0⟩ :
          {d : D // d ∉ M.deleteVertexSet d0})).map
        (M.deleteVertex d0).tail).Nodup) := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hpₛ).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hpₛ) htail0⟩
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0
      hbin_mem hbin_head hpₛ hbin_tail hbout hoPre_surv hoPre_phi
  have hroot_inc : M.dartFace root.1 ∈ M.vertexFaces d0 :=
    fanPairSeamEdge_incident fan htail0 hpₛ
  change (((M.deleteVertex d0).faceDartList root).map
      (M.deleteVertex d0).tail).Nodup
  have hL : ((M.deleteVertex d0).faceDartList root).Nodup := by
    rw [ProofsInTheBook.PlanarMap.CombMap.faceDartList]
    exact Equiv.Perm.nodup_toList _ _
  rw [List.nodup_map_iff_inj_on hL]
  intro x hx y hy htail
  have hxinc : M.dartFace x.1 ∈ M.vertexFaces d0 :=
    (mem_faceDartList_root_iff_incident hNT htail0 root x hroot_inc hmerge).1 hx
  have hyinc : M.dartFace y.1 ∈ M.vertexFaces d0 :=
    (mem_faceDartList_root_iff_incident hNT htail0 root y hroot_inc hmerge).1 hy
  by_cases hxouter : M.dartFace x.1 = hNT.outerFace
  · by_cases hyouter : M.dartFace y.1 = hNT.outerFace
    · exact old_outer_survivor_eq_of_deleted_tail_eq x y hxouter hyouter htail
    · exfalso
      exact incident_nonouter_not_old_outer_same_deleted_tail fan hchordless htail0
        hbin_mem hbin_head hpₛ hbin_tail y x hyinc hyouter hxouter htail.symm
  · by_cases hyouter : M.dartFace y.1 = hNT.outerFace
    · exfalso
      exact incident_nonouter_not_old_outer_same_deleted_tail fan hchordless htail0
        hbin_mem hbin_head hpₛ hbin_tail x y hxinc hxouter hyouter htail
    · exact incident_nonouter_survivor_eq_of_deleted_tail_eq fan hchordless htail0
        x y hxinc hyinc hxouter hyouter htail

/-- Route-(b) `outer_len` for any chosen incident root of the merged deleted
outer face.  It avoids a literal `faceDartList` itinerary: the merged-orbit
classifier puts two fan-edge darts and one surviving old-outer dart in the root
orbit, and they are pairwise distinct. -/
theorem deleted_root_faceDartList_len_ge_three
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (r : {d : D // d ∉ M.deleteVertexSet d0})
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    3 ≤ ((M.deleteVertex d0).faceDartList r).length := by
  classical
  have hfan_nonempty : 1 ≤ fan.t :=
    fan_nonempty_of_chordless_of_not_triangle (hNT := hNT) fan hchordless hbig
  obtain ⟨b0, bs, hInterior⟩ : ∃ b bs, fan.interior = b :: bs := by
    have hne : fan.interior ≠ [] := by
      intro hnil
      have ht0 : fan.t = 0 := by simp [BoundaryVertexFan.t, hnil]
      omega
    cases h : fan.interior with
    | nil => exact False.elim (hne h)
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hpath_head : fan.path = fan.x :: b0 :: (bs ++ [fan.w]) := by
    rw [BoundaryVertexFan.path, fanPath, hInterior]
    rfl
  have hp0 : (fan.x, b0) ∈ consecutivePairs fan.path := by
    rw [hpath_head, consecutivePairs]
    simp
  obtain ⟨aT, hpT⟩ := exists_terminal_fan_pair fan
  set T0 := fan.incident_faces_exact.triangle_of_pair hp0
  set TT := fan.incident_faces_exact.triangle_of_pair hpT
  let y0 : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨T0.d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        T0 htail0⟩
  let yT : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨TT.d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        TT htail0⟩
  let yO : {d : D // d ∉ M.deleteVertexSet d0} := ⟨oPre, hoPre_surv⟩
  have hinc0 : M.dartFace y0.1 ∈ M.vertexFaces d0 := by
    exact fanPairSeamEdge_incident fan htail0 hp0
  have hincT : M.dartFace yT.1 ∈ M.vertexFaces d0 := by
    exact fanPairSeamEdge_incident fan htail0 hpT
  have hoPre_face : M.dartFace oPre = hNT.outerFace :=
    old_outer_predecessor_face (hNT := hNT) hbin_mem hoPre_phi
  have hincO : M.dartFace yO.1 ∈ M.vertexFaces d0 := by
    dsimp [yO]
    rw [hoPre_face]
    exact oldOuterFace_incident_of_seam htail0 hbin_mem hbin_head hbout
  have hmem0 : y0 ∈ (M.deleteVertex d0).faceDartList r :=
    (mem_faceDartList_root_iff_incident hNT htail0 r y0 hr_incident hmerge).2 hinc0
  have hmemT : yT ∈ (M.deleteVertex d0).faceDartList r :=
    (mem_faceDartList_root_iff_incident hNT htail0 r yT hr_incident hmerge).2 hincT
  have hmemO : yO ∈ (M.deleteVertex d0).faceDartList r :=
    (mem_faceDartList_root_iff_incident hNT htail0 r yO hr_incident hmerge).2 hincO
  have hb0_ne_w : b0 ≠ fan.w := by
    have hnodup : fan.path.Nodup :=
      fan_path_simple_of_chordless hNT fan hchordless
    rw [hpath_head] at hnodup
    intro hbw
    subst hbw
    have htail_nodup : (fan.w :: bs ++ [fan.w]).Nodup :=
      (List.nodup_cons.mp hnodup).2
    have hw_not_tail : fan.w ∉ bs ++ [fan.w] :=
      (List.nodup_cons.mp htail_nodup).1
    exact hw_not_tail (by simp)
  have hy0_ne_yT : y0 ≠ yT := by
    intro h
    have htail : M.tail T0.d1 = M.tail TT.d1 := by
      exact congrArg (fun z : {d : D // d ∉ M.deleteVertexSet d0} => M.tail z.1) h
    have hT0_tail : M.tail T0.d1 = b0 := by
      dsimp [T0]
      exact (fan.incident_faces_exact.triangle_of_pair hp0).tail1
    have hTT_tail : M.tail TT.d1 = fan.w := by
      dsimp [TT]
      exact (fan.incident_faces_exact.triangle_of_pair hpT).tail1
    exact hb0_ne_w (by rw [← hT0_tail, htail, hTT_tail])
  have hy0_ne_yO : y0 ≠ yO := by
    intro h
    exact (fanTriangle_edge_ne_outer_dart T0 hoPre_face)
      (Subtype.ext_iff.mp h)
  have hyT_ne_yO : yT ≠ yO := by
    intro h
    exact (fanTriangle_edge_ne_outer_dart TT hoPre_face)
      (Subtype.ext_iff.mp h)
  exact three_le_length_of_three_mem hmem0 hmemT hmemO hy0_ne_yT hy0_ne_yO hyT_ne_yO

/-- Clean-face classification from an independently proved merged orbit.  The
root `r` must be on an old face incident with the deleted vertex, and the selected
`outerFace` must be its deleted-map face. -/
theorem cleanFaceClass_of_mergedOrbit_root {d0 : D}
    (r : {d : D // d ∉ M.deleteVertexSet d0})
    (outerFace : (M.deleteVertex d0).Face)
    (hroot : (M.deleteVertex d0).dartFace r = outerFace)
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (houter_incident : hNT.outerFace ∈ M.vertexFaces d0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    CleanFaceClass (hNT := hNT) outerFace := by
  intro f hf
  obtain ⟨x, rfl⟩ := f.exists_rep
  by_cases hxinc : M.dartFace x.1 ∈ M.vertexFaces d0
  · have hsc : (M.deleteVertex d0).φ.SameCycle r x :=
      hmerge r x hr_incident hxinc
    have hface_eq :
        (M.deleteVertex d0).dartFace r = (M.deleteVertex d0).dartFace x :=
      Quotient.sound hsc
    have hxouter : (M.deleteVertex d0).dartFace x = outerFace := by
      rw [← hface_eq, hroot]
    exact False.elim (hf hxouter)
  · refine ⟨x, rfl, hxinc, ?_⟩
    intro hMouter
    exact hxinc (hMouter ▸ houter_incident)

/-- The clean-face classifier specialized to a canonical fan-pair seam root. -/
theorem cleanFaceClass_of_fan_pair_mergedOrbit
    (fan : BoundaryVertexFan hNT v0) {d0 bin bout : D}
    (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    CleanFaceClass (hNT := hNT)
      ((M.deleteVertex d0).dartFace
        (⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
          ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
            (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩ :
          {d : D // d ∉ M.deleteVertexSet d0})) :=
  cleanFaceClass_of_mergedOrbit_root
    (r := ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩)
    _ rfl
    (fanPairSeamEdge_incident fan htail0 hp)
    (oldOuterFace_incident_of_seam htail0 hbin_mem hbin_head hbout)
    hmerge

/-- Assemble the current Phase-C seam bundle from the proved seam/orbit pieces,
leaving only the route-(b) boundary simplicity (`outer_simple`) as an explicit
input.  The length and clean-face fields are discharged in this file. -/
noncomputable def deletedSeamData_of_fan_pair_seam_of_outer_simple
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (houter_simple :
      ((((M.deleteVertex d0).faceDartList
          (⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
            ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
              (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩ :
            {d : D // d ∉ M.deleteVertexSet d0})).map
          (M.deleteVertex d0).tail).Nodup)) :
    ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData fan hchordless htail0 := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩
  let outerFace : (M.deleteVertex d0).Face := (M.deleteVertex d0).dartFace root
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0
      hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
  refine
    { seamEdge := root
      seamEdge_fan :=
        ProofsInTheBook.ZinanCh35MergedArc.fanPairSeamEdge_is_fan_edge fan htail0 hp
      mergedArc :=
        ProofsInTheBook.ZinanCh35MergedArc.mergedOuterArcData_of_fan_pair_seam
          fan htail0 hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
      outerFace := outerFace
      outerCycle :=
        (M.deleteVertex d0).boundaryCycleOfFace outerFace
          (hNT.deleteVertex_phi_ne_self d0 root) rfl ?_
      outer_simple := ?_
      outer_len_ge_three := ?_
      cleanFaceClass := ?_ }
  · exact houter_simple
  · change ((((M.deleteVertex d0).faceDartList root).map
        (M.deleteVertex d0).tail).Nodup)
    exact houter_simple
  · change 3 ≤ ((M.deleteVertex d0).faceDartList root).length
    exact deleted_root_faceDartList_len_ge_three fan hchordless hbig htail0
      hbin_mem hbin_head hbout hoPre_surv hoPre_phi root
      (fanPairSeamEdge_incident fan htail0 hp) hmerge
  · exact cleanFaceClass_of_fan_pair_mergedOrbit fan htail0 hbin_mem hbin_head
      hbout hp hmerge

/-- PHASE C seam-data closure: the actual fan-pair seam data now supplies the
merged orbit, the route-(b) boundary simplicity, the length bound, and the
clean-face classifier. -/
noncomputable def deletedSeamData_of_fan_pair_seam
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin) :
    ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData fan hchordless htail0 :=
  deletedSeamData_of_fan_pair_seam_of_outer_simple fan hchordless hbig htail0
    hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
    (deleted_outer_simple_of_fan_pair_seam fan hchordless htail0
      hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi)

/-- The corresponding full fan-surgery reconstruction obtained from the closed
seam data.  This is the `ChordlessOracle.recon` field before the list-bookkeeping
stage. -/
noncomputable def chordlessRecon_of_fan_pair_seam
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin) :
    FanSurgeryReconstruction hNT d0 :=
  (deletedSeamData_of_fan_pair_seam fan hchordless hbig htail0 hbin_mem
    hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi).chordlessRecon

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



















/-- **`FanIncidenceData` is now inhabitable from `hNT` + the boundary spoke + the base
count** — no orientation residue.  This is the structure the legacy (buggy) interface
made uninhabitable; the predecessor-orientation fix makes it σ-constructible. -/
noncomputable def fanIncidenceData_sigma_derived {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hbase : ProofsInTheBook.ZinanCh35ChordlessFull.BaseCount hNT (d0 := d0)) :
    NearTriangulation.FanIncidenceData hNT v0 :=
  ProofsInTheBook.ZinanCh35ChordlessClose.fanIncidenceData_of_baseCount
    hσ htail0 hface0 hbase



/-- **The chordless-oracle residual** (the interface-refactor residue).  A uniform
supplier that, on a chordless boundary, produces the full `ThomassenInduction.ChordlessOracle`.
This is precisely the datum blocked by the σ-forward `FanIncidenceData` /
`IncidentNonOuterFacesExactly` encoding bug; once those structures are refactored to the
σ-backward, correctly-parenthesized form (and the surgery re-threaded onto it), this
residual is dischargeable from the σ-derived connectivity + fan triangles.  It is *not*
an unsatisfiable premise: it is applied only under a true chordless witness, and its
content is the same fan/deletion datum the recursion already carries and recurses on. -/
structure ChordlessOracleResidual (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- For each near-triangulation with the Thomassen lists and a chordless boundary,
  the chordless fan oracle. -/
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), 3 < M.V → ThomassenLists hNT p q L cp cq →
      BoundaryChordless hNT.outerCycle →
        ChordlessOracle hNT p q L cp cq

variable {α : Type u} [DecidableEq α]

/-- **The chordless-branch supplier from the interface residual.**  The
`ChordlessBranchSupplier` of `ZinanCh35Dichotomy` is exactly the oracle residual
repackaged — the routing adds no content: it forwards the same chordless witness and
returns the same `ChordlessOracle`.  This is the maximal constructor: combined with
`ZinanCh35ChordBranch.chordBranchSupplier_of_residual`, it completes both
`ChordRecursiveDichotomy` suppliers, conditional on exactly the two named residuals
(chord side, and this chordless interface-refactor residue). -/
def chordlessBranchSupplier_of_residual (R : ChordlessOracleResidual α) :
    ChordlessBranchSupplier α where
  supply hNT p q L cp cq hV hT hchordless := R.supply hNT p q L cp cq hV hT hchordless









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



/-- Every listed boundary dart has a cyclic predecessor in the same dart list. -/
 lemma exists_phi_pred (C : BoundaryCycle M f) {bout : D} (hbout : bout ∈ C.darts) :
    ∃ bin : D, bin ∈ C.darts ∧ M.φ bin = bout ∧ M.head bin = M.tail bout := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  rw [List.mem_iff_getElem] at hbout
  obtain ⟨q, hq, hgetq⟩ := hbout
  set p : ℕ := (q + L - 1) % L with hp
  have hpL : p < L := by rw [hp]; exact Nat.mod_lt _ hLpos
  have hcyc : (cyclicNext C.normalized.length_pos ⟨p, hpL⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext
    show (p + 1) % L = q
    rw [hp]
    rw [Nat.mod_add_mod, show q + L - 1 + 1 = q + L from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  refine ⟨C.darts[p]'hpL, List.getElem_mem hpL, ?_, ?_⟩
  · have hcp := C.consecutive_phi ⟨p, hpL⟩
    rw [hcyc] at hcp
    have hq' : C.darts.get ⟨q, hq⟩ = C.darts[q]'hq := rfl
    have hp' : C.darts.get ⟨p, hpL⟩ = C.darts[p]'hpL := rfl
    rw [hq', hp', hgetq] at hcp
    exact hcp.symm
  · have hcv := C.consecutive_vertex ⟨p, hpL⟩
    rw [hcyc] at hcv
    have hq' : C.darts.get ⟨q, hq⟩ = C.darts[q]'hq := rfl
    have hp' : C.darts.get ⟨p, hpL⟩ = C.darts[p]'hpL := rfl
    rw [hq', hp', hgetq] at hcv
    exact hcv.symm

/-- `C.darts` is closed under the face successor. -/
 lemma phi_mem_darts (C : BoundaryCycle M f) {d : D} (hd : d ∈ C.darts) :
    M.φ d ∈ C.darts := by
  rw [C.mem_darts_iff] at hd ⊢
  rw [dartFace_phi, hd]

/-- A boundary edge is represented by a listed dart. -/
 lemma exists_dart_of_boundaryEdge (C : BoundaryCycle M f)
    {a b : M.Vertex} (h : C.IsBoundaryEdge s(a, b)) :
    ∃ d : D, d ∈ C.darts ∧ M.dartEdge d = s(a, b) := by
  rw [BoundaryCycle.IsBoundaryEdge, C.edges_eq, List.mem_map] at h
  exact h

end BoundaryCycle

namespace NearTriangulation

variable {v : M.Vertex}

/-- The unique outer dart with a prescribed boundary tail. -/
 lemma exists_unique_outer_tail (hNT : NearTriangulation M)
    (hv : hNT.outerCycle.IsBoundaryVertex v) :
    ∃! bout : D, bout ∈ hNT.outerCycle.darts ∧ M.tail bout = v := by
  classical
  obtain ⟨p, hp⟩ := hNT.outerCycle.exists_pos_of_isBoundaryVertex hv
  refine ⟨hNT.outerCycle.darts[p.1]'p.2, ⟨List.getElem_mem p.2, hp⟩, ?_⟩
  rintro b ⟨hbmem, hbtail⟩
  exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hbmem
    (List.getElem_mem p.2) (by rw [hbtail, hp])

/-- The unique outer dart with a prescribed boundary head. -/
 lemma exists_unique_outer_head (hNT : NearTriangulation M)
    (hv : hNT.outerCycle.IsBoundaryVertex v) :
    ∃! bin : D, bin ∈ hNT.outerCycle.darts ∧ M.head bin = v := by
  classical
  obtain ⟨bout, ⟨hboutmem, hbouttail⟩, _⟩ := exists_unique_outer_tail hNT hv
  obtain ⟨bin, hbinmem, _hphi, hhead⟩ := BoundaryCycle.exists_phi_pred hNT.outerCycle hboutmem
  have hbinhead : M.head bin = v := by rw [hhead, hbouttail]
  refine ⟨bin, ⟨hbinmem, hbinhead⟩, ?_⟩
  rintro b ⟨hbmem, hbhead⟩
  have hφb : M.φ b ∈ hNT.outerCycle.darts := BoundaryCycle.phi_mem_darts hNT.outerCycle hbmem
  have hφbin : M.φ bin ∈ hNT.outerCycle.darts := BoundaryCycle.phi_mem_darts hNT.outerCycle hbinmem
  have htails : M.tail (M.φ b) = M.tail (M.φ bin) := by
    rw [tail_phi, tail_phi, hbhead, hbinhead]
  have hφeq : M.φ b = M.φ bin :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφb hφbin htails
  exact M.φ.injective hφeq

/-- The two outer darts incident with a boundary vertex, in cyclic order. -/
 theorem outer_darts_consecutive (hNT : NearTriangulation M)
    (hv : hNT.outerCycle.IsBoundaryVertex v) :
    ∃ bin bout : D,
      (bin ∈ hNT.outerCycle.darts ∧ M.head bin = v) ∧
      (∀ b, b ∈ hNT.outerCycle.darts → M.head b = v → b = bin) ∧
      (bout ∈ hNT.outerCycle.darts ∧ M.tail bout = v) ∧
      (∀ b, b ∈ hNT.outerCycle.darts → M.tail b = v → b = bout) ∧
      M.φ bin = bout := by
  classical
  obtain ⟨bout, ⟨hboutmem, hbouttail⟩, hboutuniq⟩ := exists_unique_outer_tail hNT hv
  obtain ⟨bin, ⟨hbinmem, hbinhead⟩, hbinuniq⟩ := exists_unique_outer_head hNT hv
  obtain ⟨bpred, hbpredmem, hphi, hhead⟩ := BoundaryCycle.exists_phi_pred hNT.outerCycle hboutmem
  have hpredhead : M.head bpred = v := by rw [hhead, hbouttail]
  have hpred_eq_bin : bpred = bin := hbinuniq bpred ⟨hbpredmem, hpredhead⟩
  refine ⟨bin, bout, ⟨hbinmem, hbinhead⟩, ?_, ⟨hboutmem, hbouttail⟩, ?_, ?_⟩
  · intro b hbmem hbhead; exact hbinuniq b ⟨hbmem, hbhead⟩
  · intro b hbmem hbtail; exact hboutuniq b ⟨hbmem, hbtail⟩
  · rw [← hpred_eq_bin]; exact hphi

end NearTriangulation

/-- A boundary vertex and an outgoing outer dart into one of the precolored
endpoints, suitable for the chordless deletion branch. -/
structure ChordlessDeletionSite (hNT : NearTriangulation M) (p q : M.Vertex) where
  v0 : M.Vertex
  d0 : D
  hv0_boundary : hNT.outerCycle.IsBoundaryVertex v0
  d0_tail : M.tail d0 = v0
  d0_face : M.dartFace d0 = hNT.outerFace
  d0_head_precolored : M.head d0 = p ∨ M.head d0 = q
  v0_ne_p : v0 ≠ p
  v0_ne_q : v0 ≠ q
  edge_precolored :
    hNT.outerCycle.IsBoundaryEdge s(v0, p) ∨ hNT.outerCycle.IsBoundaryEdge s(v0, q)

/-- The predecessor and successor boundary neighbors of `p` are distinct. -/
 lemma boundary_neighbors_distinct {bin bout : D}
    (hbin_mem : bin ∈ hNT.outerCycle.darts) (hbout_mem : bout ∈ hNT.outerCycle.darts)
    (hbin_phi : M.φ bin = bout) :
    M.tail bin ≠ M.head bout := by
  intro hxy
  have hφbout_mem : M.φ bout ∈ hNT.outerCycle.darts :=
    BoundaryCycle.phi_mem_darts hNT.outerCycle hbout_mem
  have htail : M.tail bin = M.tail (M.φ bout) := by
    rw [tail_phi, hxy]
  have hbin_eq_phi_bout : bin = M.φ bout :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hbin_mem hφbout_mem htail
  have hφ2 : M.φ (M.φ bout) = bout := by
    rw [← hbin_eq_phi_bout, hbin_phi]
  have hφ : M.φ bout ≠ bout :=
    phi_ne_self_of_isSimpleGraph M hNT.simpleGraph bout
  have hcard2 :
      (M.φ.cycleOf bout).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hbout_face : M.dartFace bout = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff bout).mp hbout_mem
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [hbout_face, hcard2] at hsupport
    exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega

/-- A `ThomassenLists` boundary edge at `p q` determines a deletion site at the
other boundary neighbor of `p`. -/
theorem exists_chordlessDeletionSite_nonempty {p q : M.Vertex} {L : M.Vertex → Finset α}
    {cp cq : α} (hTL : ThomassenLists hNT p q L cp cq) :
    Nonempty (ChordlessDeletionSite hNT p q) := by
  classical
  obtain ⟨bin, bout, hbin, hbin_unique, hbout, hbout_unique, hbin_phi⟩ :=
    NearTriangulation.outer_darts_consecutive hNT hTL.p_boundary
  rcases hbin with ⟨hbin_mem, hbin_head⟩
  rcases hbout with ⟨hbout_mem, hbout_tail⟩
  let x : M.Vertex := M.tail bin
  let y : M.Vertex := M.head bout
  have hx_boundary : hNT.outerCycle.IsBoundaryVertex x := by
    show M.tail bin ∈ hNT.outerCycle.vertices
    rw [hNT.outerCycle.vertices_eq]
    exact List.mem_map_of_mem hbin_mem
  have hy_boundary : hNT.outerCycle.IsBoundaryVertex y := by
    have hφbout_mem : M.φ bout ∈ hNT.outerCycle.darts :=
      BoundaryCycle.phi_mem_darts hNT.outerCycle hbout_mem
    show M.head bout ∈ hNT.outerCycle.vertices
    rw [hNT.outerCycle.vertices_eq]
    rw [← M.tail_phi bout]
    exact List.mem_map_of_mem hφbout_mem
  have hx_ne_p : x ≠ p := by
    intro h
    exact hNT.simpleGraph.no_loop bin (by simp [x, h, hbin_head])
  have hy_ne_p : y ≠ p := by
    intro h
    exact hNT.simpleGraph.no_loop bout (by rw [hbout_tail]; exact h.symm)
  have hxy : x ≠ y := by
    simpa [x, y] using
      boundary_neighbors_distinct (hNT := hNT) hbin_mem hbout_mem hbin_phi
  have hedge_xp : hNT.outerCycle.IsBoundaryEdge s(x, p) := by
    show s(x, p) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bin = s(x, p) := by
      simp [CombMap.dartEdge, x, hbin_head]
    rw [← hedge]
    exact List.mem_map_of_mem hbin_mem
  have hedge_yp : hNT.outerCycle.IsBoundaryEdge s(y, p) := by
    show s(y, p) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bout = s(y, p) := by
      simp [CombMap.dartEdge, y, hbout_tail, Sym2.eq_swap]
    rw [← hedge]
    exact List.mem_map_of_mem hbout_mem
  obtain ⟨e, he_mem, he_edge⟩ :=
    BoundaryCycle.exists_dart_of_boundaryEdge hNT.outerCycle hTL.pq_boundary_edge
  have hq_is_neighbor : x = q ∨ y = q := by
    rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge
    rcases he_edge with ⟨hetail, hehead⟩ | ⟨hetail, hehead⟩
    · have he_eq_bout : e = bout := hbout_unique e he_mem hetail
      right
      rw [← hehead, he_eq_bout]
    · have he_eq_bin : e = bin := hbin_unique e he_mem hehead
      left
      rw [← hetail, he_eq_bin]
  rcases hq_is_neighbor with hxq | hyq
  · obtain ⟨qbin, qbout, hqbin, hqbin_unique, hqbout, hqbout_unique, hqbin_phi⟩ :=
      NearTriangulation.outer_darts_consecutive hNT hTL.q_boundary
    rcases hqbin with ⟨hqbin_mem, hqbin_head⟩
    rcases hqbout with ⟨hqbout_mem, hqbout_tail⟩
    have hbin_eq_qbout : bin = qbout := by
      exact hqbout_unique bin hbin_mem (by
        show M.tail bin = q
        exact hxq)
    have hq_tail_ne_p : M.tail qbin ≠ p := by
      have hne := boundary_neighbors_distinct hqbin_mem hqbout_mem hqbin_phi
      intro hp
      apply hne
      rw [hp, ← hbin_eq_qbout, hbin_head]
    have hq_tail_ne_q : M.tail qbin ≠ q := by
      intro hq
      exact hNT.simpleGraph.no_loop qbin (by simp [hq, hqbin_head])
    have hq_tail_boundary : hNT.outerCycle.IsBoundaryVertex (M.tail qbin) := by
      show M.tail qbin ∈ hNT.outerCycle.vertices
      rw [hNT.outerCycle.vertices_eq]
      exact List.mem_map_of_mem hqbin_mem
    have hedge_q : hNT.outerCycle.IsBoundaryEdge s(M.tail qbin, q) := by
      show s(M.tail qbin, q) ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]
      have hedge : M.dartEdge qbin = s(M.tail qbin, q) := by
        simp [CombMap.dartEdge, hqbin_head]
      rw [← hedge]
      exact List.mem_map_of_mem hqbin_mem
    refine ⟨
      { v0 := M.tail qbin
        d0 := qbin
        hv0_boundary := hq_tail_boundary
        d0_tail := rfl
        d0_face := hNT.outerCycle.dartFace_of_mem_darts hqbin_mem
        d0_head_precolored := by
          right
          exact hqbin_head
        v0_ne_p := hq_tail_ne_p
        v0_ne_q := hq_tail_ne_q
        edge_precolored := by
          right
          exact hedge_q }⟩
  · refine ⟨
      { v0 := x
        d0 := bin
        hv0_boundary := hx_boundary
        d0_tail := rfl
        d0_face := hNT.outerCycle.dartFace_of_mem_darts hbin_mem
        d0_head_precolored := by
          left
          exact hbin_head
        v0_ne_p := hx_ne_p
        v0_ne_q := ?_
        edge_precolored := by
          left
          exact hedge_xp }⟩
    intro hxq
    exact hxy (hxq.trans hyq.symm)

/-- A concrete deletion-site witness, extracted from the nonempty theorem. -/
noncomputable def exists_chordlessDeletionSite {p q : M.Vertex} {L : M.Vertex → Finset α}
    {cp cq : α} (hTL : ThomassenLists hNT p q L cp cq) :
    ChordlessDeletionSite hNT p q :=
  Classical.choice (exists_chordlessDeletionSite_nonempty (hNT := hNT) hTL)

/-- Two colors different from `cp` can be reserved from any list of size at least
three. -/
lemma exists_two_reserved_colors {s : Finset α} {cp : α} (hcard : 3 ≤ s.card) :
    ∃ γ δ : α, γ ∈ s ∧ δ ∈ s ∧ γ ≠ δ ∧ cp ≠ γ ∧ cp ≠ δ := by
  classical
  let S := s.erase cp
  have hScard : 1 < S.card := by
    by_cases hcp : cp ∈ s
    · have hS : S.card = s.card - 1 := by
        simp [S, Finset.card_erase_of_mem hcp]
      omega
    · have hS : S.card = s.card := by
        simp [S, Finset.erase_eq_of_notMem hcp]
      omega
  obtain ⟨γ, hγS, δ, hδS, hγδ⟩ := Finset.one_lt_card.mp hScard
  have hγ : γ ∈ s := (Finset.mem_erase.mp hγS).2
  have hδ : δ ∈ s := (Finset.mem_erase.mp hδS).2
  have hcpγ : cp ≠ γ := by
    exact (Finset.mem_erase.mp hγS).1.symm
  have hcpδ : cp ≠ δ := by
    exact (Finset.mem_erase.mp hδS).1.symm
  exact ⟨γ, δ, hγ, hδ, hγδ, hcpγ, hcpδ⟩



/-- The fan path has a terminal consecutive pair ending at `fan.w`. -/
 lemma exists_terminal_fan_pair (fan : BoundaryVertexFan hNT v0) :
    ∃ a : M.Vertex, (a, fan.w) ∈ consecutivePairs fan.path := by
  classical
  have hterm : ∀ (x : M.Vertex) (l : List M.Vertex),
      ∃ a : M.Vertex, (a, fan.w) ∈ consecutivePairs (x :: l ++ [fan.w]) := by
    intro x l
    induction l generalizing x with
    | nil =>
        refine ⟨x, ?_⟩
        simp [consecutivePairs]
    | cons z zs ih =>
        rcases ih z with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        simp [consecutivePairs] at ha ⊢
        exact Or.inr ha
  rw [BoundaryVertexFan.path, fanPath]
  exact hterm fan.x fan.interior

/-- The terminal boundary endpoint of a certified fan is not the apex. -/
lemma fan_w_ne_v0 (fan : BoundaryVertexFan hNT v0) : fan.w ≠ v0 := by
  obtain ⟨a, ha⟩ := exists_terminal_fan_pair (hNT := hNT) (v0 := v0) fan
  have T : FanTriangle hNT v0 fan.w a := fan.incident_faces_exact.triangle_of_pair ha
  exact T.vertices_pairwiseDistinct.1.symm

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

/-- Boundary-cycle vertices are exactly tails of listed boundary darts. -/
theorem boundary_vertex_iff_exists_dart_tail {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) (W : K.Vertex) :
    C.IsBoundaryVertex W ↔ ∃ d : D, d ∈ C.darts ∧ K.tail d = W := by
  constructor
  · intro hW
    rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq] at hW
    simpa [List.mem_map] using hW
  · rintro ⟨d, hd, rfl⟩
    rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq]
    exact List.mem_map_of_mem hd

/-- Boundary-cycle edges are exactly dart edges of listed boundary darts. -/
theorem boundary_edge_iff_exists_dart_edge {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) (e : Sym2 K.Vertex) :
    C.IsBoundaryEdge e ↔ ∃ d : D, d ∈ C.darts ∧ K.dartEdge d = e := by
  constructor
  · intro he
    rw [BoundaryCycle.IsBoundaryEdge, C.edges_eq] at he
    simpa [List.mem_map] using he
  · rintro ⟨d, hd, rfl⟩
    rw [BoundaryCycle.IsBoundaryEdge, C.edges_eq]
    exact List.mem_map_of_mem hd

/-- An endpoint of a listed boundary edge is a boundary vertex. -/
lemma boundary_vertex_of_boundary_edge_left {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) {x y : K.Vertex}
    (he : C.IsBoundaryEdge s(x, y)) :
    C.IsBoundaryVertex x := by
  classical
  obtain ⟨d, hd, hdedge⟩ := (boundary_edge_iff_exists_dart_edge C s(x, y)).1 he
  rw [CombMap.dartEdge, Sym2.eq_iff] at hdedge
  rcases hdedge with ⟨htail, _hhead⟩ | ⟨_htail, hhead⟩
  · exact (boundary_vertex_iff_exists_dart_tail C x).2 ⟨d, hd, htail⟩
  · have hφd : K.φ d ∈ C.darts := C.phi_mem_darts hd
    exact (boundary_vertex_iff_exists_dart_tail C x).2
      ⟨K.φ d, hφd, by rw [K.tail_phi, hhead]⟩

/-- Consecutive in/out darts at a simple boundary vertex have distinct other
endpoints. -/
lemma boundary_neighbors_distinct_public {bin bout : D}
    (hbin_mem : bin ∈ hNT.outerCycle.darts) (hbout_mem : bout ∈ hNT.outerCycle.darts)
    (hbin_phi : M.φ bin = bout) :
    M.tail bin ≠ M.head bout := by
  intro hxy
  have hφbout_mem : M.φ bout ∈ hNT.outerCycle.darts :=
    hNT.outerCycle.phi_mem_darts hbout_mem
  have htail : M.tail bin = M.tail (M.φ bout) := by
    rw [tail_phi, hxy]
  have hbin_eq_phi_bout : bin = M.φ bout :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hbin_mem hφbout_mem htail
  have hφ2 : M.φ (M.φ bout) = bout := by
    rw [← hbin_eq_phi_bout, hbin_phi]
  have hφ : M.φ bout ≠ bout :=
    phi_ne_self_of_isSimpleGraph M hNT.simpleGraph bout
  have hcard2 :
      (M.φ.cycleOf bout).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hbout_face : M.dartFace bout = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff bout).mp hbout_mem
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [hbout_face, hcard2] at hsupport
    exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega

/-- Any old boundary vertex that survives a vertex deletion has an old boundary
edge incident with it whose other endpoint also survives. -/
lemma old_boundary_vertex_has_surviving_boundary_edge
    {d0 : D} (htail0 : M.tail d0 = v0)
    {u : M.Vertex}
    (hu_old : hNT.outerCycle.IsBoundaryVertex u)
    (hu_ne : u ≠ M.tail d0) :
    ∃ w : M.Vertex, w ≠ M.tail d0 ∧ hNT.outerCycle.IsBoundaryEdge s(u, w) := by
  classical
  obtain ⟨bin, bout, hbin, _hbin_unique, hbout, _hbout_unique, hbin_phi⟩ :=
    hNT.outer_v0_darts_consecutive hu_old
  rcases hbin with ⟨hbin_mem, hbin_head⟩
  rcases hbout with ⟨hbout_mem, hbout_tail⟩
  by_cases hsucc_ne : M.head bout ≠ M.tail d0
  · refine ⟨M.head bout, hsucc_ne, ?_⟩
    show s(u, M.head bout) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bout = s(u, M.head bout) := by
      simp [CombMap.dartEdge, hbout_tail]
    rw [← hedge]
    exact List.mem_map_of_mem hbout_mem
  · have hsucc_eq : M.head bout = M.tail d0 := by simpa using not_not.mp hsucc_ne
    have hpred_ne : M.tail bin ≠ M.tail d0 := by
      intro hpred_eq
      exact boundary_neighbors_distinct_public (hNT := hNT) hbin_mem hbout_mem hbin_phi
        (by rw [hpred_eq, hsucc_eq])
    refine ⟨M.tail bin, hpred_ne, ?_⟩
    show s(u, M.tail bin) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bin = s(u, M.tail bin) := by
      simp [CombMap.dartEdge, hbin_head, Sym2.eq_swap]
    rw [← hedge]
    exact List.mem_map_of_mem hbin_mem

/-- If a dart is on the outer face, its reverse is not also on the outer face.
This is the local no-digon consequence of the simple outer boundary. -/
theorem alpha_dartFace_ne_outer_of_outer_local {e : D}
    (he : M.dartFace e = hNT.outerFace) :
    M.dartFace (M.α e) ≠ hNT.outerFace := by
  intro hαe
  have he_mem : e ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff e).2 he
  have hαe_mem : M.α e ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff (M.α e)).2 hαe
  have hφe_mem : M.φ e ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ e) = hNT.outerFace
    rw [M.dartFace_phi]; exact he
  have htail_eq : M.tail (M.φ e) = M.tail (M.α e) := by
    rw [M.tail_phi, M.tail_alpha]
  have hφα : M.φ e = M.α e :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφe_mem hαe_mem htail_eq
  have htail2 : M.tail (M.φ (M.φ e)) = M.tail e := by
    rw [hφα, M.tail_phi, M.head_alpha]
  have hφ2_mem : M.φ (M.φ e) ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ (M.φ e)) = hNT.outerFace
    rw [M.dartFace_phi, M.dartFace_phi]; exact he
  have hφ2 : M.φ (M.φ e) = e :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφ2_mem he_mem htail2
  have hφ : M.φ e ≠ e :=
    phi_ne_self_of_isSimpleGraph M hNT.simpleGraph e
  have hcard2 : (M.φ.cycleOf e).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [he, hcard2] at hsupport
    exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega

lemma mem_of_sigma_sameCycle_of_closed
    (S : Finset D)
    (hσS : ∀ ⦃d : D⦄, d ∈ S → M.σ d ∈ S)
    {a b : D} (ha : a ∈ S) (hab : M.σ.SameCycle a b) :
    b ∈ S := by
  obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ n : ℕ, (M.σ ^ n) a ∈ S := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hσS ih
  simpa [hn] using hpow n

lemma univ_subset_of_connected_closed
    (S : Finset D) {base : D}
    (hbase : base ∈ S)
    (hαS : ∀ ⦃d : D⦄, d ∈ S → M.α d ∈ S)
    (hσS : ∀ ⦃d : D⦄, d ∈ S → M.σ d ∈ S)
    (hconn : M.Connected) :
    ∀ d : D, d ∈ S := by
  intro d
  have hreach : Relation.ReflTransGen M.dartStep base d := hconn base d
  induction hreach with
  | refl => exact hbase
  | tail hreach hstep ih =>
      rcases hstep with hsame | halpha
      · exact mem_of_sigma_sameCycle_of_closed (M := M) S hσS ih hsame
      · rw [halpha]
        exact hαS ih

lemma alpha_outer_of_inner_boundary_edge {e : D}
    (hinner : M.dartFace e ≠ hNT.outerFace)
    (hedge : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)) :
    M.dartFace (M.α e) = hNT.outerFace := by
  classical
  obtain ⟨b, hbmem, hbedge⟩ :=
    (boundary_edge_iff_exists_dart_edge hNT.outerCycle (M.dartEdge e)).1 hedge
  have hbface : M.dartFace b = hNT.outerFace :=
    hNT.outerCycle.dartFace_of_mem_darts hbmem
  have hsc : M.α.SameCycle b e :=
    hNT.simpleGraph.no_parallel hbedge
  have hcases := (M.alpha_sameCycle_iff e b).mp hsc.symm
  rcases hcases with rfl | hb
  · exact False.elim (hinner hbface)
  · rw [hb] at hbface
    exact hbface

lemma phi_outer_eq_of_same_tail {e b : D}
    (he : M.dartFace e = hNT.outerFace)
    (hb : M.dartFace b = hNT.outerFace)
    (htail : M.tail (M.φ e) = M.tail b) :
    M.φ e = b := by
  have hφe_mem : M.φ e ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ e) = hNT.outerFace
    rw [M.dartFace_phi]; exact he
  have hb_mem : b ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff b).2 hb
  exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφe_mem hb_mem htail

lemma length_le_two_of_tail_dropLast_nil {β : Type*} (l : List β)
    (h : l.tail.dropLast = []) : l.length ≤ 2 := by
  cases l with
  | nil => simp
  | cons a l =>
      cases l with
      | nil => simp
      | cons b l =>
          cases l with
          | nil => simp
          | cons c l =>
              simp at h

lemma tail_dropLast_nil_of_length_le_two {β : Type*} (l : List β)
    (h : l.length ≤ 2) : l.tail.dropLast = [] := by
  cases l with
  | nil => simp
  | cons a l =>
      cases l with
      | nil => simp
      | cons b l =>
          cases l with
          | nil => simp
          | cons c l =>
              simp at h

/-- Reverse half of the canonical base count: on a base triangle, the canonical
strict middle of any nontrivial vertex star is empty. -/
theorem canonInterior_empty_of_baseTriangle
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hbase : hNT.IsBaseTriangle) :
    ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = [] := by
  classical
  let hlist : List M.Vertex := (M.vertexDartList d0).map M.head
  have hnodup : hlist.Nodup := by
    dsimp [hlist]
    exact ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.vertexDartList_heads_nodup
      hNT hσ rfl
  have hsub : hlist.toFinset ⊆ (Finset.univ.erase (M.tail d0) : Finset M.Vertex) := by
    intro z hz
    rw [List.mem_toFinset] at hz
    obtain ⟨e, he_mem, rfl⟩ := List.mem_map.mp hz
    rw [Finset.mem_erase]
    constructor
    · have htail_e : M.tail e = M.tail d0 :=
        M.vertexDartList_tail hσ he_mem
      intro h
      exact hNT.simpleGraph.no_loop e (by rw [h, htail_e])
    · simp
  have herase_card : (Finset.univ.erase (M.tail d0) : Finset M.Vertex).card = 2 := by
    have hcard : Fintype.card M.Vertex = 3 := by
      unfold NearTriangulation.IsBaseTriangle at hbase
      exact hbase
    rw [Finset.card_erase_of_mem (by simp), Finset.card_univ, hcard]
  have hlen_le : hlist.length ≤ 2 := by
    have hcard_le := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnodup, herase_card] at hcard_le
    exact hcard_le
  apply tail_dropLast_nil_of_length_le_two
  simpa [ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior, hlist] using hlen_le

/-- Empty canonical fan interior means the `v0` star has exactly two darts. -/
lemma vertexDartList_length_eq_two_of_canonInterior_empty
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = []) :
    (M.vertexDartList d0).length = 2 := by
  set hlist := (M.vertexDartList d0).map M.head with hlistdef
  have hle : hlist.length ≤ 2 := by
    apply length_le_two_of_tail_dropLast_nil
    simpa [ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior, hlistdef] using hempty
  have hge : 2 ≤ hlist.length := by
    rw [hlistdef, List.length_map]
    exact ProofsInTheBook.ZinanCh35ChordlessFull.vertexDartList_length_ge_two hσ
  have hlen : hlist.length = 2 := le_antisymm hle hge
  simpa [hlistdef] using hlen

/-- With an empty canonical interior, the two boundary spokes are the same
non-root star dart: `σ d0 = σ⁻¹ d0`. -/
lemma sigma_eq_symm_of_canonInterior_empty
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = []) :
    M.σ d0 = M.σ.symm d0 := by
  have hlen := vertexDartList_length_eq_two_of_canonInterior_empty
    (M := M) hσ hempty
  have hpow := M.vertexDartList_pow_length hσ
  rw [hlen] at hpow
  apply M.σ.injective
  rw [Equiv.apply_symm_apply]
  simpa [pow_succ, pow_one, Equiv.Perm.coe_mul, Function.comp_apply] using hpow

/-- If the canonical fan interior is empty, the two old boundary neighbours of
`v0` are adjacent through the unique inner triangle incident with the outgoing
boundary edge. -/
lemma boundary_neighbours_adj_of_canonInterior_empty
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = []) :
    M.toSimpleGraph.Adj (M.head d0) (M.head (M.σ.symm d0)) := by
  classical
  let d2 : D := M.φ (M.φ (M.α d0))
  have hinner : M.dartFace (M.α d0) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer_local (hNT := hNT) hface0
  have hcube : M.φ (M.φ (M.φ (M.α d0))) = M.α d0 :=
    faceLen_three_phi_cube_eq_self M hNT.simpleGraph
      (hNT.inner_tri (M.dartFace (M.α d0)) hinner)
  have hsigsym : M.σ d0 = M.σ.symm d0 :=
    sigma_eq_symm_of_canonInterior_empty (M := M) hσ hempty
  have htail_d2 : M.tail d2 = M.head (M.σ.symm d0) := by
    dsimp [d2]
    have hφα : M.φ (M.α d0) = M.σ d0 := by
      show (M.σ * M.α) (M.α d0) = M.σ d0
      simp [Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
    rw [hφα, M.tail_phi, hsigsym]
  have hhead_d2 : M.head d2 = M.head d0 := by
    dsimp [d2]
    rw [← M.tail_phi, hcube, M.tail_alpha]
  have hadj : M.toSimpleGraph.Adj (M.tail d2) (M.head d2) :=
    M.toSimpleGraph_adj_of_dart hNT.simpleGraph d2
  have hadj' : M.toSimpleGraph.Adj (M.head (M.σ.symm d0)) (M.head d0) := by
    simpa [htail_d2, hhead_d2] using hadj
  exact hadj'.symm

/-- If the two neighbours from the empty canonical fan are not already joined by
an outer-boundary edge, they form a boundary chord. -/
lemma chord_of_canonInterior_empty_of_not_boundary_edge
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = [])
    (hnot :
      ¬ hNT.outerCycle.IsBoundaryEdge s(M.head d0, M.head (M.σ.symm d0))) :
    hNT.outerCycle.Chord (M.head d0) (M.head (M.σ.symm d0)) := by
  refine
    { endpoints_ne := ?_
      left_boundary := ProofsInTheBook.ZinanCh35Chordless.head_outgoing_boundary hNT hface0
      right_boundary := ProofsInTheBook.ZinanCh35Chordless.head_incoming_boundary hNT hface0
      adj := boundary_neighbours_adj_of_canonInterior_empty
        (hNT := hNT) hσ hface0 hempty
      not_boundary_edge := hnot }
  intro h
  have hinner : M.dartFace (M.α d0) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer_local (hNT := hNT) hface0
  have hdistinct :=
    hNT.inner_face_vertices_pairwiseDistinct (d := M.α d0) hinner
  have hsigsym : M.σ d0 = M.σ.symm d0 :=
    sigma_eq_symm_of_canonInterior_empty (M := M) hσ hempty
  have hφeq : M.φ (M.α d0) = M.σ d0 := by
    show (M.σ * M.α) (M.α d0) = M.σ d0
    simp [Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
  have htail1 : M.tail (M.α d0) = M.head d0 := by rw [M.tail_alpha]
  have htail3 : M.tail (M.φ (M.φ (M.α d0))) = M.head (M.σ.symm d0) := by
    rw [hφeq, M.tail_phi, hsigsym]
  exact hdistinct.2.2 (by rw [htail3, htail1, h])

lemma alpha_sigmaSymm_outer_of_outer {d0 : D}
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    M.dartFace (M.α (M.σ.symm d0)) = hNT.outerFace := by
  have hkey :
      M.dartFace (M.σ (M.σ.symm d0)) =
        M.dartFace (M.α (M.σ.symm d0)) :=
    ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M) (M.σ.symm d0)
  rw [Equiv.apply_symm_apply] at hkey
  rw [← hkey]
  exact hface0

/-- Six-dart closure for the empty-fan base count: once the third edge is also
on the outer boundary, the six darts of the two triangular faces are closed under
`α` and `σ`; connectedness then forces them to be all darts, hence only three
vertex orbits. -/
theorem baseTriangle_of_canonInterior_empty_of_third_boundary_edge
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = [])
    (hbedge :
      hNT.outerCycle.IsBoundaryEdge s(M.head d0, M.head (M.σ.symm d0))) :
    hNT.IsBaseTriangle := by
  classical
  let e1 : D := M.σ.symm d0
  let e2 : D := M.φ (M.φ (M.α d0))
  let S : Finset D := {d0, M.α d0, e1, M.α e1, e2, M.α e2}
  have htail_e1 : M.tail e1 = M.tail d0 := by
    dsimp [e1]
    have h := M.tail_sigma (M.σ.symm d0)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have hsigsym : M.σ d0 = e1 := by
    dsimp [e1]
    exact sigma_eq_symm_of_canonInterior_empty (M := M) hσ hempty
  have hφeq : M.φ (M.α d0) = e1 := by
    dsimp [e1]
    show (M.σ * M.α) (M.α d0) = M.σ.symm d0
    rw [show (M.σ * M.α) (M.α d0) = M.σ d0 by
      simp [Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]]
    exact hsigsym
  have hinner : M.dartFace (M.α d0) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer_local (hNT := hNT) hface0
  have hcube : M.φ (M.φ (M.φ (M.α d0))) = M.α d0 :=
    faceLen_three_phi_cube_eq_self M hNT.simpleGraph
      (hNT.inner_tri (M.dartFace (M.α d0)) hinner)
  have htail_e2 : M.tail e2 = M.head e1 := by
    dsimp [e2]
    rw [hφeq, M.tail_phi]
  have hhead_e2 : M.head e2 = M.head d0 := by
    dsimp [e2]
    rw [← M.tail_phi, hcube, M.tail_alpha]
  have hedge_e2 : M.dartEdge e2 = s(M.head d0, M.head e1) := by
    rw [CombMap.dartEdge, htail_e2, hhead_e2, Sym2.eq_swap]
  have hbedge_e2 : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e2) := by
    simpa [hedge_e2, e1] using hbedge
  have hαe2_outer : M.dartFace (M.α e2) = hNT.outerFace :=
    alpha_outer_of_inner_boundary_edge (hNT := hNT) (e := e2) (by
      dsimp [e2]
      rw [M.dartFace_phi, M.dartFace_phi]
      exact hinner) hbedge_e2
  have hαe1_outer : M.dartFace (M.α e1) = hNT.outerFace := by
    dsimp [e1]
    exact alpha_sigmaSymm_outer_of_outer (hNT := hNT) hface0
  have hφd0 : M.φ d0 = M.α e2 := by
    apply phi_outer_eq_of_same_tail (hNT := hNT) hface0 hαe2_outer
    rw [M.tail_phi, M.tail_alpha, hhead_e2]
  have hφαe2 : M.φ (M.α e2) = M.α e1 := by
    apply phi_outer_eq_of_same_tail (hNT := hNT) hαe2_outer hαe1_outer
    rw [M.tail_phi, M.head_alpha, M.tail_alpha, htail_e2]
  have hσS : ∀ ⦃d : D⦄, d ∈ S → M.σ d ∈ S := by
    intro d hd
    simp [S] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl hsigsym))
    · have : M.σ (M.α d0) = M.α e2 := by
        rw [← hφd0]
        rfl
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr this))))
    · dsimp [e1]
      simp
    · have : M.σ (M.α e1) = e2 := by
        rw [← hφeq]
        rfl
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl this))))
    · have : M.σ e2 = M.α e1 := by
        rw [← hφαe2]
        show M.σ e2 = M.φ (M.α e2)
        simp [CombMap.φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
      exact Or.inr (Or.inr (Or.inr (Or.inl this)))
    · have : M.σ (M.α e2) = M.α d0 := by
        rw [← hcube]
        rfl
      exact Or.inr (Or.inl this)
  have hαS : ∀ ⦃d : D⦄, d ∈ S → M.α d ∈ S := by
    intro d hd
    simp [S] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S, M.alpha_alpha]
  have hall : ∀ d : D, d ∈ S :=
    univ_subset_of_connected_closed (M := M) S (base := d0)
      (by simp [S]) hαS hσS hNT.sphere.1
  let A : M.Vertex := M.tail d0
  let B : M.Vertex := M.head d0
  let C : M.Vertex := M.head e1
  have hver : ∀ Q : M.Vertex,
      Q ∈ ({A, B, C} : Finset M.Vertex) := by
    intro Q
    induction Q using Quotient.inductionOn with
    | h d =>
        have hd := hall d
        simp [S] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
        · change A ∈ ({A, B, C} : Finset M.Vertex)
          simp
        · change M.tail (M.α d0) ∈ ({A, B, C} : Finset M.Vertex)
          rw [M.tail_alpha]
          simp [B]
        · change M.tail e1 ∈ ({A, B, C} : Finset M.Vertex)
          rw [htail_e1]
          simp [A]
        · change M.tail (M.α e1) ∈ ({A, B, C} : Finset M.Vertex)
          rw [M.tail_alpha]
          simp [C]
        · change M.tail e2 ∈ ({A, B, C} : Finset M.Vertex)
          rw [htail_e2]
          simp [C]
        · change M.tail (M.α e2) ∈ ({A, B, C} : Finset M.Vertex)
          rw [M.tail_alpha, hhead_e2]
          simp [B]
  have hVle : M.V ≤ 3 := by
    calc
      M.V = (Finset.univ : Finset M.Vertex).card := rfl
      _ ≤ ({A, B, C} : Finset M.Vertex).card :=
        Finset.card_le_card (by intro Q _; exact hver Q)
      _ ≤ 3 := by
        simpa using
          (List.toFinset_card_le (l := [A, B, C]))
  have hVge : 3 ≤ M.V := ProofsInTheBook.ThomassenInduction.three_le_V hNT
  unfold NearTriangulation.IsBaseTriangle
  omega

/-- Forward half of the canonical `BaseCount` for an outgoing outer spoke. -/
theorem baseTriangle_of_canonInterior_empty_of_chordless
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = []) :
    hNT.IsBaseTriangle := by
  by_cases hbedge :
      hNT.outerCycle.IsBoundaryEdge s(M.head d0, M.head (M.σ.symm d0))
  · exact baseTriangle_of_canonInterior_empty_of_third_boundary_edge
      (hNT := hNT) hσ hface0 hempty hbedge
  · exact False.elim
      (hchordless (chord_of_canonInterior_empty_of_not_boundary_edge
        (hNT := hNT) hσ hface0 hempty hbedge))

/-- The canonical `BaseCount` required by the σ-derived fan constructor, for an
outgoing outer spoke. -/
theorem baseCount_of_outer_spoke
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    ProofsInTheBook.ZinanCh35ChordlessFull.BaseCount hNT (d0 := d0) := by
  intro hchordless
  constructor
  · intro hempty
    exact baseTriangle_of_canonInterior_empty_of_chordless
      (hNT := hNT) hσ hface0 hchordless hempty
  · intro hbase
    exact canonInterior_empty_of_baseTriangle (hNT := hNT) hσ hbase

/-- The second vertex of a fan consecutive pair is either exposed-interior or
the terminal endpoint. -/
lemma consecutivePair_second_mem_interior_or_w
    (fan : BoundaryVertexFan hNT v0) {a b : M.Vertex}
    (hp : (a, b) ∈ consecutivePairs fan.path) :
    b ∈ fan.interior ∨ b = fan.w := by
  have hb_tail : b ∈ fan.path.tail := by
    rw [consecutivePairs] at hp
    exact (List.of_mem_zip hp).2
  rw [BoundaryVertexFan.path, fanPath] at hb_tail
  simpa using hb_tail

/-- Any listed interior fan vertex has a predecessor in the fan path. -/
lemma fan_interior_exists_predecessor_pair
    (fan : BoundaryVertexFan hNT v0) {z : M.Vertex}
    (hz : z ∈ fan.interior) :
    ∃ a : M.Vertex, (a, z) ∈ consecutivePairs fan.path := by
  classical
  have aux : ∀ (x : M.Vertex) (l : List M.Vertex),
      z ∈ l → ∃ a : M.Vertex, (a, z) ∈ consecutivePairs (x :: l ++ [fan.w]) := by
    intro x l
    induction l generalizing x with
    | nil =>
        intro hz
        simp at hz
    | cons y ys ih =>
        intro hz
        rw [List.mem_cons] at hz
        rcases hz with rfl | hz
        · refine ⟨x, ?_⟩
          simp [consecutivePairs]
        · obtain ⟨a, ha⟩ := ih y hz
          refine ⟨a, ?_⟩
          simp [consecutivePairs] at ha ⊢
          exact Or.inr ha
  rw [BoundaryVertexFan.path, fanPath]
  exact aux fan.x fan.interior hz



/-- A surviving dart whose old face was incident with the deleted vertex has its
tail over either an old boundary vertex or an exposed fan-interior vertex. -/
theorem incident_survivor_tail_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hyinc : M.dartFace y.1 ∈ M.vertexFaces d0) :
    hNT.outerCycle.IsBoundaryVertex (M.tail y.1) ∨
      M.tail y.1 ∈ fan.interior.toFinset := by
  classical
  by_cases hyouter : M.dartFace y.1 = hNT.outerFace
  · left
    exact ProofsInTheBook.ZinanCh35DeletedAssembly.isBoundaryVertex_tail_of_outer_dart
      (hNT := hNT) hyouter
  ·
    obtain ⟨a, b, hp, hy_eq⟩ :=
      ProofsInTheBook.ZinanCh35DeletedAssembly.incident_nonouter_survivor_eq_fan_edge
        fan htail0 y hyinc hyouter
    have htail_b : M.tail y.1 = b := by
      rw [hy_eq]
      exact (fan.incident_faces_exact.triangle_of_pair hp).tail1
    rcases consecutivePair_second_mem_interior_or_w fan hp with hbint | hbw
    · right
      simpa [htail_b] using hbint
    · left
      rw [htail_b, hbw]
      exact fan.w_boundary

/-- Forward half of deleted-boundary classification, abstracted over any deleted
boundary cycle whose darts are known to be old faces incident with the deleted
vertex. -/
theorem deleted_boundary_vertex_oldBoundary_or_fanInterior_of_incident_darts
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    {outerFace : (M.deleteVertex d0).Face}
    (C : BoundaryCycle (M.deleteVertex d0) outerFace)
    (hinc : ∀ y : {d : D // d ∉ M.deleteVertexSet d0},
      y ∈ C.darts → M.dartFace y.1 ∈ M.vertexFaces d0)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' : C.IsBoundaryVertex u') :
    hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
      deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  classical
  obtain ⟨y, hy, hy_tail⟩ := (boundary_vertex_iff_exists_dart_tail C u').1 hu'
  have hclass := incident_survivor_tail_oldBoundary_or_fanInterior fan htail0 y (hinc y hy)
  have htoM : deletedVertexToM M d0 u' = M.tail y.1 := by
    rw [← hy_tail]
    exact deletedVertexToM_tail M d0 y
  simpa [htoM] using hclass

/-- Darts on the produced fan-pair deleted outer cycle are exactly old faces
incident with the deleted vertex, forward direction. -/
theorem fan_pair_deleted_outerCycle_dart_incident
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hy : y ∈
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.darts)) :
    M.dartFace y.1 ∈ M.vertexFaces d0 := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0 hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
  have hroot_inc : M.dartFace root.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp
  change y ∈ (M.deleteVertex d0).faceDartList root at hy
  exact (ProofsInTheBook.ZinanCh35DeletedAssembly.mem_faceDartList_root_iff_incident
    hNT htail0 root y hroot_inc hmerge).1 hy

/-- Any survivor whose old face is incident with the deleted vertex is listed on
the produced fan-pair deleted outer cycle. -/
theorem fan_pair_incident_survivor_mem_deleted_outerCycle
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hyinc : M.dartFace y.1 ∈ M.vertexFaces d0) :
    y ∈
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.darts) := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0 hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
  have hroot_inc : M.dartFace root.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp
  change y ∈ (M.deleteVertex d0).faceDartList root
  exact (ProofsInTheBook.ZinanCh35DeletedAssembly.mem_faceDartList_root_iff_incident
    hNT htail0 root y hroot_inc hmerge).2 hyinc

/-- Forward half of `DeletedBoundaryClassification.boundary_iff` for the closed
fan-pair seam assembly. -/
theorem fan_pair_deleted_boundary_vertex_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' :
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u')) :
    hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
      deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  exact deleted_boundary_vertex_oldBoundary_or_fanInterior_of_incident_darts
    fan htail0
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle)
    (fun y hy => fan_pair_deleted_outerCycle_dart_incident
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi y hy)
    hu'

/-- A deleted vertex whose old image is an exposed fan-interior vertex is on the
produced deleted outer boundary. -/
theorem fan_pair_fanInterior_deleted_boundary_vertex
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu'fan : deletedVertexToM M d0 u' ∈ fan.interior.toFinset) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') := by
  classical
  rw [List.mem_toFinset] at hu'fan
  obtain ⟨a₀, hp₀⟩ := fan_interior_exists_predecessor_pair fan hu'fan
  let T := fan.incident_faces_exact.triangle_of_pair hp₀
  let y : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨T.d1, ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
      T htail0⟩
  have hyinc : M.dartFace y.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp₀
  have hy_mem := fan_pair_incident_survivor_mem_deleted_outerCycle
    fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
    hoPre_surv hoPre_phi y hyinc
  have htail_old : M.tail y.1 = deletedVertexToM M d0 u' := by
    dsimp [y, T]
    rw [(fan.incident_faces_exact.triangle_of_pair hp₀).tail1]
  have htail_deleted : (M.deleteVertex d0).tail y = u' := by
    apply deletedVertexToM_injective M d0
    rw [deletedVertexToM_tail, htail_old]
  exact (boundary_vertex_iff_exists_dart_tail
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle) u').2
    ⟨y, hy_mem, htail_deleted⟩

/-- The canonical section is the unique deleted vertex with the prescribed old
image. -/
lemma deleted_vertex_eq_sectionToDeleted_of_toM_eq
    {d0 : D} (R : FanSurgeryReconstruction hNT d0)
    {W : (M.deleteVertex d0).Vertex} {x : M.Vertex}
    (hx : x ≠ M.tail d0)
    (hW : deletedVertexToM M d0 W = x) :
    W = sectionToDeleted R x hx := by
  apply deletedVertexToM_injective M d0
  rw [hW, deletedVertexToM_sectionToDeleted]

/-- Old boundary edges whose endpoints survive the deletion remain boundary
edges of the produced deleted outer cycle. -/
theorem fan_pair_old_boundary_edge_survives
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {x y : M.Vertex}
    (hx : x ≠ M.tail d0) (hy : y ≠ M.tail d0)
    (hedge : hNT.outerCycle.IsBoundaryEdge s(x, y)) :
    let R :=
      (ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon
    R.nearTriangulation.outerCycle.IsBoundaryEdge
      s(sectionToDeleted R x hx, sectionToDeleted R y hy) := by
  classical
  intro R
  obtain ⟨e, he_mem, he_edge⟩ :=
    (boundary_edge_iff_exists_dart_edge hNT.outerCycle s(x, y)).1 hedge
  have he_face : M.dartFace e = hNT.outerFace :=
    hNT.outerCycle.dartFace_of_mem_darts he_mem
  have htail_ne : M.tail e ≠ M.tail d0 := by
    rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge
    rcases he_edge with ⟨ht, _hh⟩ | ⟨ht, _hh⟩
    · rw [ht]; exact hx
    · rw [ht]; exact hy
  have hhead_ne : M.head e ≠ M.tail d0 := by
    rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge
    rcases he_edge with ⟨_ht, hh⟩ | ⟨_ht, hh⟩
    · rw [hh]; exact hy
    · rw [hh]; exact hx
  have hsurv : e ∉ M.deleteVertexSet d0 :=
    dart_notMem_deleteVertexSet_of_endpoints_ne M d0 htail_ne hhead_ne
  let e' : {d : D // d ∉ M.deleteVertexSet d0} := ⟨e, hsurv⟩
  have houter_inc : hNT.outerFace ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.oldOuterFace_incident_of_seam
      htail0 hbin_mem hbin_head hbout
  have he_inc : M.dartFace e'.1 ∈ M.vertexFaces d0 := by
    dsimp [e']
    rw [he_face]
    exact houter_inc
  have he'_mem := fan_pair_incident_survivor_mem_deleted_outerCycle
    fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
    hoPre_surv hoPre_phi e' he_inc
  refine (boundary_edge_iff_exists_dart_edge R.nearTriangulation.outerCycle
    s(sectionToDeleted R x hx, sectionToDeleted R y hy)).2 ⟨e', he'_mem, ?_⟩
  have he_edge_saved : M.dartEdge e = s(x, y) := he_edge
  rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge_saved ⊢
  rcases he_edge_saved with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · left
    constructor
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hx (by
        rw [deletedVertexToM_tail]
        exact ht)
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hy (by
        rw [deletedVertexToM_head]
        exact hh)
  · right
    constructor
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hy (by
        rw [deletedVertexToM_tail]
        exact ht)
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hx (by
        rw [deletedVertexToM_head]
        exact hh)

/-- Old boundary vertices that survive the deletion lie on the produced deleted
outer boundary. -/
theorem fan_pair_oldBoundary_deleted_boundary_vertex
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu_old : hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u')) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') := by
  classical
  let R :=
    (ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon
  let u := deletedVertexToM M d0 u'
  have hu_ne : u ≠ M.tail d0 := by
    dsimp [u]
    exact deletedVertexToM_ne_v0 M d0 u'
  obtain ⟨w, hw_ne, hedge⟩ :=
    old_boundary_vertex_has_surviving_boundary_edge
      (hNT := hNT) (v0 := v0) htail0 hu_old hu_ne
  have hedge' :
      R.nearTriangulation.outerCycle.IsBoundaryEdge
        s(sectionToDeleted R u hu_ne, sectionToDeleted R w hw_ne) := by
    simpa [R] using
      (fan_pair_old_boundary_edge_survives
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hu_ne hw_ne hedge)
  have hsec_boundary :
      R.nearTriangulation.outerCycle.IsBoundaryVertex
        (sectionToDeleted R u hu_ne) :=
    boundary_vertex_of_boundary_edge_left R.nearTriangulation.outerCycle hedge'
  have hu'_eq : u' = sectionToDeleted R u hu_ne :=
    deleted_vertex_eq_sectionToDeleted_of_toM_eq R hu_ne (by rfl)
  simpa [R, hu'_eq]
    using hsec_boundary

/-- Full vertex-level deleted-boundary classification for the produced
fan-pair seam assembly. -/
theorem fan_pair_deleted_boundary_iff_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (u' : (M.deleteVertex d0).Vertex) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') ↔
      hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
        deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  constructor
  · intro hu'
    exact fan_pair_deleted_boundary_vertex_oldBoundary_or_fanInterior
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hu'
  · intro hclass
    rcases hclass with hold | hfan
    · exact fan_pair_oldBoundary_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hold
    · exact fan_pair_fanInterior_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hfan

/-- Deleted non-boundary vertices map to old non-boundary vertices and are not
exposed fan-interior vertices. -/
theorem fan_pair_deleted_nonboundary_old_interior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' :
      ¬ ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u')) :
    ¬ hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∧
      deletedVertexToM M d0 u' ∉ fan.interior.toFinset := by
  constructor
  · intro hold
    exact hu' (fan_pair_oldBoundary_deleted_boundary_vertex
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hold)
  · intro hfan
    exact hu' (fan_pair_fanInterior_deleted_boundary_vertex
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hfan)

/-- Thomassen-list transport for the produced fan-pair deletion.  The deleted
precolored edge is the surviving copy of the original precolored edge. -/
noncomputable def fan_pair_deleted_thomassenLists
    (fan : BoundaryVertexFan hNT v0)
    (hTL : ThomassenLists hNT p q L cp cq)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (hp_ne_v0 : p ≠ M.tail d0) (hq_ne_v0 : q ≠ M.tail d0)
    (γ δ : α) :
    let R :=
      (ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon
    ThomassenLists R.nearTriangulation
      (sectionToDeleted R p hp_ne_v0) (sectionToDeleted R q hq_ne_v0)
      (deleteFanLists M d0 fan.interior.toFinset L γ δ) cp cq := by
  classical
  intro R
  let p' : (M.deleteVertex d0).Vertex := sectionToDeleted R p hp_ne_v0
  let q' : (M.deleteVertex d0).Vertex := sectionToDeleted R q hq_ne_v0
  have hp'_toM : deletedVertexToM M d0 p' = p := by
    simpa [p'] using deletedVertexToM_sectionToDeleted R p hp_ne_v0
  have hq'_toM : deletedVertexToM M d0 q' = q := by
    simpa [q'] using deletedVertexToM_sectionToDeleted R q hq_ne_v0
  have hp_not_fan : deletedVertexToM M d0 p' ∉ fan.interior.toFinset := by
    rw [hp'_toM, List.mem_toFinset]
    intro hpint
    exact (fan.interior_not_boundary_of_chordless hchordless p hpint) hTL.p_boundary
  have hq_not_fan : deletedVertexToM M d0 q' ∉ fan.interior.toFinset := by
    rw [hq'_toM, List.mem_toFinset]
    intro hqint
    exact (fan.interior_not_boundary_of_chordless hchordless q hqint) hTL.q_boundary
  refine
    { p_boundary := ?_
      q_boundary := ?_
      pq_boundary_edge := ?_
      colors_ne := hTL.colors_ne
      list_p := ?_
      list_q := ?_
      boundary_ge_three := ?_
      interior_ge_five := ?_ }
  · simpa [R, p', hp'_toM] using
      (fan_pair_oldBoundary_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi (u' := p') (by simpa [hp'_toM] using hTL.p_boundary))
  · simpa [R, q', hq'_toM] using
      (fan_pair_oldBoundary_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi (u' := q') (by simpa [hq'_toM] using hTL.q_boundary))
  · simpa [R, p', q'] using
      (fan_pair_old_boundary_edge_survives
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hp_ne_v0 hq_ne_v0 hTL.pq_boundary_edge)
  · rw [deleteFanLists_other M d0 fan.interior.toFinset L γ δ hp_not_fan, hp'_toM]
    exact hTL.list_p
  · rw [deleteFanLists_other M d0 fan.interior.toFinset L γ δ hq_not_fan, hq'_toM]
    exact hTL.list_q
  · intro u' hu' hu'p hu'q
    have hclass :=
      (fan_pair_deleted_boundary_iff_oldBoundary_or_fanInterior
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi u').1 hu'
    rcases hclass with hold | hfan
    · have hu_ne_p : deletedVertexToM M d0 u' ≠ p := by
        intro hup
        apply hu'p
        apply deletedVertexToM_injective M d0
        rw [hup, hp'_toM]
      have hu_ne_q : deletedVertexToM M d0 u' ≠ q := by
        intro huq
        apply hu'q
        apply deletedVertexToM_injective M d0
        rw [huq, hq'_toM]
      have hnotfan : deletedVertexToM M d0 u' ∉ fan.interior.toFinset := by
        rw [List.mem_toFinset]
        intro hint
        exact (fan.interior_not_boundary_of_chordless hchordless
          (deletedVertexToM M d0 u') hint) hold
      rw [deleteFanLists_other M d0 fan.interior.toFinset L γ δ hnotfan]
      exact hTL.boundary_ge_three (deletedVertexToM M d0 u') hold hu_ne_p hu_ne_q
    · have h5 : 5 ≤ (L (deletedVertexToM M d0 u')).card :=
        hTL.interior_ge_five (deletedVertexToM M d0 u')
          (fan.interior_not_boundary_of_chordless hchordless
            (deletedVertexToM M d0 u') (by simpa [List.mem_toFinset] using hfan))
      exact deleteFanLists_card_ge_three M d0 fan.interior.toFinset L hfan h5
  · intro u' hu'
    have hnon :=
      fan_pair_deleted_nonboundary_old_interior
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hu'
    rw [deleteFanLists_other M d0 fan.interior.toFinset L γ δ hnon.2]
    exact hTL.interior_ge_five (deletedVertexToM M d0 u') hnon.1

/-- The chordless oracle residual is supplied by the canonical endpoint-aware
deletion site, the σ-derived fan data, the closed seam reconstruction, and the
deleted-list transport above. -/
noncomputable def canonicalChordlessOracleResidual :
    ProofsInTheBook.ZinanCh35ChordlessOracle.ChordlessOracleResidual α where
  supply := by
    intro D _ _ M hNT p q L cp cq hbig hTL hchordless
    classical
    let site :=
      ProofsInTheBook.ZinanCh35ChordlessSite.exists_chordlessDeletionSite
        (hNT := hNT) hTL
    have hσ : M.σ site.d0 ≠ site.d0 :=
      ProofsInTheBook.ZinanCh35Chordless.outgoingOuterDart_sigma_ne hNT site.d0_face
    let fanData :
        NearTriangulation.FanIncidenceData hNT site.v0 :=
      ProofsInTheBook.ZinanCh35ChordlessOracle.fanIncidenceData_sigma_derived
        hσ site.d0_tail site.d0_face
        (baseCount_of_outer_spoke (hNT := hNT) hσ site.d0_face)
    let fan : BoundaryVertexFan hNT site.v0 :=
      NearTriangulation.boundaryVertexFan_of_incidenceData fanData
    let bin : D := Classical.choose (hNT.outer_v0_darts_consecutive site.hv0_boundary)
    let bout : D :=
      Classical.choose (Classical.choose_spec
        (hNT.outer_v0_darts_consecutive site.hv0_boundary))
    have hout :=
      Classical.choose_spec (Classical.choose_spec
        (hNT.outer_v0_darts_consecutive site.hv0_boundary))
    rcases hout with ⟨hbin, _hbin_unique, hbout, hbout_unique, hbin_phi⟩
    rcases hbin with ⟨hbin_mem, hbin_head⟩
    rcases hbout with ⟨hbout_mem, hbout_tail⟩
    have hbout_eq_d0 : bout = site.d0 := by
      exact (hbout_unique site.d0 ((hNT.outerCycle.mem_darts_iff site.d0).2 site.d0_face)
        site.d0_tail).symm
    have hphi_bin_d0 : M.φ bin = site.d0 := by
      exact hbin_phi.trans hbout_eq_d0
    have htail_bin_fan_w : M.tail bin = fan.w := by
      have htail_sigma :=
        ProofsInTheBook.ZinanCh35MergedArc.incoming_outer_tail_eq_head_sigma_symm
          (hNT := hNT) site.d0_face site.d0_tail hbin_mem hbin_head hphi_bin_d0
      have hfan_w : fan.w = M.head (M.σ.symm site.d0) := by
        change fanData.w = M.head (M.σ.symm site.d0)
        simp [fanData,
          ProofsInTheBook.ZinanCh35ChordlessOracle.fanIncidenceData_sigma_derived,
          ProofsInTheBook.ZinanCh35ChordlessClose.fanIncidenceData_of_baseCount,
          ProofsInTheBook.ZinanCh35ChordlessFull.fanIncidenceData_of_orientation]
      exact htail_sigma.trans hfan_w.symm
    have htail_bin_boundary : hNT.outerCycle.IsBoundaryVertex (M.tail bin) := by
      show M.tail bin ∈ hNT.outerCycle.vertices
      rw [hNT.outerCycle.vertices_eq]
      exact List.mem_map_of_mem hbin_mem
    let oPre : D := Classical.choose (hNT.outer_v0_darts_consecutive htail_bin_boundary)
    let oPost : D :=
      Classical.choose (Classical.choose_spec
        (hNT.outer_v0_darts_consecutive htail_bin_boundary))
    have houtPre :=
      Classical.choose_spec (Classical.choose_spec
        (hNT.outer_v0_darts_consecutive htail_bin_boundary))
    rcases houtPre with ⟨hoPreIn, _hoPre_unique, hoPostOut, hoPost_unique, hoPre_phi0⟩
    rcases hoPreIn with ⟨hoPre_mem, _hoPre_head⟩
    rcases hoPostOut with ⟨hoPost_mem, hoPost_tail⟩
    have hbin_eq_oPost : bin = oPost := by
      exact hoPost_unique bin hbin_mem rfl
    have hoPre_phi : M.φ oPre = bin := by
      exact hoPre_phi0.trans hbin_eq_oPost.symm
    have hoPre_surv : oPre ∉ M.deleteVertexSet site.d0 :=
      ProofsInTheBook.ZinanCh35MergedArc.old_outer_predecessor_survives
        (hNT := hNT) site.d0_tail hbin_mem hbin_head hbin_phi.symm
        hoPre_mem hoPre_phi
    let aT : M.Vertex :=
      Classical.choose (ProofsInTheBook.ZinanCh35DeletedAssembly.exists_terminal_fan_pair fan)
    have hpT :
        (aT, fan.w) ∈ consecutivePairs fan.path :=
      Classical.choose_spec
        (ProofsInTheBook.ZinanCh35DeletedAssembly.exists_terminal_fan_pair fan)
    have hp_ne_v0 : p ≠ M.tail site.d0 := by
      intro hpv
      exact site.v0_ne_p (by rw [← site.d0_tail, ← hpv])
    have hq_ne_v0 : q ≠ M.tail site.d0 := by
      intro hqv
      exact site.v0_ne_q (by rw [← site.d0_tail, ← hqv])
    let recon : FanSurgeryReconstruction hNT site.d0 :=
      ProofsInTheBook.ZinanCh35DeletedAssembly.chordlessRecon_of_fan_pair_seam
        fan hchordless hbig site.d0_tail hbin_mem hbin_head hpT htail_bin_fan_w
        hbin_phi.symm hoPre_surv hoPre_phi
    have hx_head : fan.x = M.head site.d0 := by
      simpa [fan, fanData] using
        NearTriangulation.fan_first_spoke_head (hNT := hNT) fanData
    let avoidColor : α := if M.head site.d0 = p then cp else cq
    let colorWitness :=
      ProofsInTheBook.ZinanCh35ChordlessSite.exists_two_reserved_colors
        (cp := avoidColor)
        (hTL.boundary_ge_three site.v0 site.hv0_boundary site.v0_ne_p site.v0_ne_q
          : 3 ≤ (L site.v0).card)
    let γ : α := Classical.choose colorWitness
    let δ : α := Classical.choose (Classical.choose_spec colorWitness)
    have hcolors := Classical.choose_spec (Classical.choose_spec colorWitness)
    rcases hcolors with ⟨hγ, hδ, hγδ, havoidγ, havoidδ⟩
    refine
      { chordless := hchordless
        v0 := site.v0
        fanData := fanData
        recon := recon
        hd0 := site.d0_tail
        γ := γ
        δ := δ
        γ_mem := hγ
        δ_mem := hδ
        γδ_ne := hγδ
        x_ne := ?_
        w_ne := ?_
        x_precolored := ?_
        deleted_lists := ?_ }
    · rcases site.d0_head_precolored with hphead | hqhead
      · rw [hx_head, hphead]
        exact site.v0_ne_p.symm
      · rw [hx_head, hqhead]
        exact site.v0_ne_q.symm
    · exact ProofsInTheBook.ZinanCh35ChordlessSite.fan_w_ne_v0 fan
    · by_cases hphead : M.head site.d0 = p
      · left
        have hcpγ : cp ≠ γ := by
          change cp ≠ Classical.choose colorWitness
          simpa [avoidColor, hphead] using havoidγ
        have hcpδ : cp ≠ δ := by
          change cp ≠ Classical.choose (Classical.choose_spec colorWitness)
          simpa [avoidColor, hphead] using havoidδ
        exact ⟨hx_head.trans hphead, hcpγ, hcpδ⟩
      · right
        have hqhead : M.head site.d0 = q := by
          rcases site.d0_head_precolored with hp | hq
          · exact False.elim (hphead hp)
          · exact hq
        have hcqγ : cq ≠ γ := by
          change cq ≠ Classical.choose colorWitness
          simpa [avoidColor, hphead] using havoidγ
        have hcqδ : cq ≠ δ := by
          change cq ≠ Classical.choose (Classical.choose_spec colorWitness)
          simpa [avoidColor, hphead] using havoidδ
        exact ⟨hx_head.trans hqhead, hcqγ, hcqδ⟩
    · refine ⟨sectionToDeleted recon p hp_ne_v0, sectionToDeleted recon q hq_ne_v0,
        cp, cq, ?_⟩
      simpa [recon] using
        (fan_pair_deleted_thomassenLists
          fan hTL hchordless hbig site.d0_tail hbin_mem hbin_head hpT
          htail_bin_fan_w hbin_phi.symm hoPre_surv hoPre_phi
          hp_ne_v0 hq_ne_v0 γ δ)

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

































/-- The canonical chordless branch supplier produced by the Phase-C deletion
assembly. -/
noncomputable def canonicalChordlessBranchSupplier (α : Type u) [DecidableEq α] :
    ChordlessBranchSupplier α :=
  chordlessBranchSupplier_of_residual
    (ProofsInTheBook.ZinanCh35ChordlessSupplier.canonicalChordlessOracleResidual
      (α := α))





end ProofsInTheBook.ZinanCh35Final














end


