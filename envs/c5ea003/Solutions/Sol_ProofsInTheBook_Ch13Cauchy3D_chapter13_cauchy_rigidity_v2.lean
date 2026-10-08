-- Prove2me | solution 1 for ProofsInTheBook.Ch13Cauchy3D.chapter13_cauchy_rigidity_v2
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T21:08:54.551462+00:00
-- url     : https://prove2.me/submissions/e13cab19-e6d0-4eff-97ae-ccf2b604029b

import Init
import Mathlib
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Fin.Rev
import Mathlib.Geometry.Euclidean.Triangle
import Definitions.Def_P2MAssembly_Chapter13V2

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



























/-- Every `α`-class (edge) has exactly two darts. -/
lemma alpha_class_card (M : CombMap D)
    (q : Quotient (cycleSetoid M.α)) :
    (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.α) x = q)).card = 2 := by
  obtain ⟨d, rfl⟩ := q.exists_rep
  have hset :
      (Finset.univ.filter
          (fun x => Quotient.mk (cycleSetoid M.α) x = Quotient.mk (cycleSetoid M.α) d))
        = {d, M.α d} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Quotient.eq]
    show M.α.SameCycle x d ↔ x = d ∨ x = M.α d
    constructor
    · intro h; exact (alpha_sameCycle_iff M d x).mp h.symm
    · intro h; exact ((alpha_sameCycle_iff M d x).mpr h).symm
  rw [hset, Finset.card_insert_of_notMem (by
    simp only [Finset.mem_singleton]
    exact fun hcontra => M.α_no_fixed d hcontra.symm), Finset.card_singleton]

/-- Every edge has exactly two darts: `2 * E = |D|`. -/
lemma two_mul_E_eq_card (M : CombMap D) : 2 * M.E = Fintype.card D := by
  have hsum : Fintype.card D
      = ∑ q : Quotient (cycleSetoid M.α),
          (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.α) x = q)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  rw [hsum, Finset.sum_congr rfl (fun q _ => alpha_class_card M q),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, E, Nat.mul_comm]

/-- Orbit sizes of any permutation sum to the dart count. -/
lemma sum_class_card (p : Equiv.Perm D) :
    ∑ Q : Quotient (cycleSetoid p),
        (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid p) x = Q)).card
      = Fintype.card D := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)).symm













end CombMap

end ProofsInTheBook.PlanarMap

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
open ProofsInTheBook.SphericalOpeningProcess (StuckWitnessExists)

/-- **The genuine fixed-chord arm contradiction.**  Two strictly convex spherical arms `A`, `B` with
equal side lengths and nondecreasing joints, where SOME joint of `B` is strictly wider, cannot have an
equal endpoint chord: the strict arm lemma forces `sDist (A 0)(A last) < sDist (B 0)(B last)`,
contradicting equality.  This is exactly the content the Cauchy 0/2-sign-change vertex link supplies —
DERIVED from `armMono_strict_of_stuckWitness`, not posited.  Conditional only on `StuckWitnessExists`. -/
theorem cauchy_arm_fixed_chord_contradiction (h : StuckWitnessExists)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i)
    (hchord : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))) :
    False :=
  absurd hchord (ne_of_lt (armMono_strict_of_stuckWitness h hn A B hA hB hside hangle hstrict))







/-- **The genuine fixed-chord arm contradiction — UNCONDITIONAL.**  This is the honest, derived
replacement for `Chapter13.CauchyArmOpeningObstruction.arm_conclusion` (which posited it). -/
theorem cauchy_arm_fixed_chord_contradiction_uncond
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i)
    (hchord : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))) :
    False :=
  cauchy_arm_fixed_chord_contradiction ProofsInTheBook.ZinanFFCT113.stuckWitnessExists_holds
    hn A B hA hB hside hangle hstrict hchord

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

theorem contradiction (obs : CauchyArmOpeningObstruction) : False :=
  ZinanFFCT112.cauchy_arm_fixed_chord_contradiction_uncond obs.hn obs.A obs.B obs.hA obs.hB
    obs.equal_sides obs.opened obs.some_angle_strictly_opened obs.fixed_chord

end CauchyArmOpeningObstruction



namespace CauchyArmClosingObstruction

theorem contradiction (obs : CauchyArmClosingObstruction) : False :=
  ZinanFFCT112.cauchy_arm_fixed_chord_contradiction_uncond obs.hn obs.B obs.A obs.hB obs.hA
    (fun i => (obs.equal_sides i).symm) obs.closed obs.some_angle_strictly_closed
    obs.fixed_chord.symm

end CauchyArmClosingObstruction



namespace CauchyArmFixedChordObstruction

theorem contradiction : CauchyArmFixedChordObstruction → False
  | opening obs => obs.contradiction
  | closing obs => obs.contradiction

end CauchyArmFixedChordObstruction









theorem four_le_of_even_ne_zero_ne_two {m : ℕ}
    (heven : Even m) (hzero : m ≠ 0) (htwo : m ≠ 2) :
    4 ≤ m := by
  rcases heven with ⟨k, rfl⟩
  omega







namespace CauchyArmVertex

theorem arm_lemma_no_zero_sign_changes (v : CauchyArmVertex) :
    v.signChanges ≠ 0 := by
  intro hzero
  exact (v.zero_sign_changes_obstruction hzero).contradiction

theorem arm_lemma_no_two_sign_changes (v : CauchyArmVertex) :
    v.signChanges ≠ 2 := by
  intro htwo
  exact (v.two_sign_changes_obstruction htwo).contradiction

theorem four_le_signChanges (v : CauchyArmVertex) :
    4 ≤ v.signChanges :=
  four_le_of_even_ne_zero_ne_two v.signChanges_even
    v.arm_lemma_no_zero_sign_changes v.arm_lemma_no_two_sign_changes

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













/-- For a two-valued alphabet, the inequality indicator equals the `ZMod 2` sum of
the two values: `[a ≠ b] = valZ a + valZ b`. -/
theorem indicator_eq_valZ_add (a b : StrictEdgeSign) :
    ((if a ≠ b then 1 else 0 : ℕ) : ZMod 2) = StrictEdgeSign.valZ a + StrictEdgeSign.valZ b := by
  cases a <;> cases b <;> decide











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









/-- **Corner double-count (exact).**  For an edge-invariant strict signing, the
number of vertex-side corner changes equals the number of face-side corner changes.
Proof: the edge involution `α` is a bijection carrying one set onto the other, using
`φ (α d) = σ d` and `s (α d) = s d`. -/
theorem corner_double_count (M : CombMap D) (s : D → StrictEdgeSign)
    (hs : EdgeInvariant M s) :
    (vertexChangeSet M s).card = (faceChangeSet M s).card := by
  -- `φ (α d) = σ d`, since `φ = σ α` and `α` is an involution.
  have hφα : ∀ d, M.φ (M.α d) = M.σ d := by
    intro d
    show (M.σ * M.α) (M.α d) = M.σ d
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    have : M.α (M.α d) = d := by
      have := congrArg (fun p => p d) M.α_invol
      simpa using this
    rw [this]
  refine Finset.card_bij (fun d _ => M.α d) ?_ ?_ ?_
  · -- maps vertexChangeSet into faceChangeSet
    intro d hd
    simp only [vertexChangeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    simp only [faceChangeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hs d, hφα d]
    exact hd
  · -- injective on the set
    intro a _ b _ hab
    exact M.α.injective hab
  · -- surjective onto faceChangeSet
    intro b hb
    simp only [faceChangeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨M.α b, ?_, ?_⟩
    · simp only [vertexChangeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      -- want: s (α b) ≠ s (σ (α b)); use hs and hφα: σ(αb) = φ(α(αb))? compute directly
      have hαα : M.α (M.α b) = b := by
        have := congrArg (fun p => p b) M.α_invol
        simpa using this
      -- s (α b) = s b ; s (σ (α b)) = ?  σ (α b) = φ (α (α b)) = φ b
      have hσαb : M.σ (M.α b) = M.φ b := by
        have := hφα (M.α b)
        rw [hαα] at this
        exact this.symm
      rw [hs b, hσαb]
      exact hb
    · have hαα : M.α (M.α b) = b := by
        have := congrArg (fun p => p b) M.α_invol
        simpa using this
      exact hαα







/-- Summing the vertex flip counts over all vertices recovers the total number of
vertex-side corner changes. -/
theorem sum_vertexFlip (M : CombMap D) (s : D → StrictEdgeSign) :
    (∑ Q : Quotient (cycleSetoid M.σ), vertexFlip M s Q) = (vertexChangeSet M s).card := by
  rw [eq_comm]
  apply Finset.card_eq_sum_card_fiberwise
  intro d _
  exact Finset.mem_univ _

/-- Summing the face flip counts over all faces recovers the total number of
face-side corner changes. -/
theorem sum_faceFlip (M : CombMap D) (s : D → StrictEdgeSign) :
    (∑ Q : Quotient (cycleSetoid M.φ), faceFlip M s Q) = (faceChangeSet M s).card := by
  rw [eq_comm]
  apply Finset.card_eq_sum_card_fiberwise
  intro d _
  exact Finset.mem_univ _

/-- **The double-count, as a sum equality**: total vertex flips = total face flips. -/
theorem sum_vertexFlip_eq_sum_faceFlip (M : CombMap D) (s : D → StrictEdgeSign)
    (hs : EdgeInvariant M s) :
    (∑ Q : Quotient (cycleSetoid M.σ), vertexFlip M s Q)
      = ∑ Q : Quotient (cycleSetoid M.φ), faceFlip M s Q := by
  rw [sum_vertexFlip, sum_faceFlip, corner_double_count M s hs]



/-- The fiber of a `p`-orbit is closed under `p`. -/
theorem mem_fiber_apply_gen (p : Equiv.Perm D) (Q : Quotient (cycleSetoid p)) {x : D}
    (hx : Quotient.mk (cycleSetoid p) x = Q) :
    Quotient.mk (cycleSetoid p) (p x) = Q := by
  rw [← hx]
  apply Quotient.sound
  show p.SameCycle (p x) x
  exact (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- **Per-orbit parity (general).**  For any permutation `p` and any strict signing
`s`, the number of darts in a single `p`-orbit `Q` whose corner is a change
(`s x ≠ s (p x)`) is even.  Proof: in `ZMod 2` the indicator sum telescopes to
`2 ∑ valZ (s x) = 0` because `p` is a bijection of the orbit. -/
theorem orbitFlip_even (p : Equiv.Perm D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid p)) :
    Even ((Finset.univ.filter
      (fun x => Quotient.mk (cycleSetoid p) x = Q ∧ s x ≠ s (p x))).card) := by
  classical
  set B := Finset.univ.filter (fun x => Quotient.mk (cycleSetoid p) x = Q) with hB
  have hcount : (Finset.univ.filter
      (fun x => Quotient.mk (cycleSetoid p) x = Q ∧ s x ≠ s (p x))).card
      = (B.filter (fun x => s x ≠ s (p x))).card := by
    congr 1
    ext x
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hcount, ← ZMod.natCast_eq_zero_iff_even]
  have hcard_sum : ((B.filter (fun x => s x ≠ s (p x))).card : ZMod 2)
      = ∑ x ∈ B, ((if s x ≠ s (p x) then 1 else 0 : ℕ) : ZMod 2) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hcard_sum]
  have hind : ∀ x, ((if s x ≠ s (p x) then 1 else 0 : ℕ) : ZMod 2)
      = StrictEdgeSign.valZ (s x) + StrictEdgeSign.valZ (s (p x)) :=
    fun x => indicator_eq_valZ_add (s x) (s (p x))
  simp only [hind]
  rw [Finset.sum_add_distrib]
  have hbij : (∑ x ∈ B, StrictEdgeSign.valZ (s (p x)))
      = ∑ x ∈ B, StrictEdgeSign.valZ (s x) := by
    apply Finset.sum_bij (fun x _ => p x)
    · intro x hx
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact mem_fiber_apply_gen p Q hx
    · intro a _ b _ hab; exact p.injective hab
    · intro b hb
      refine ⟨p.symm b, ?_, ?_⟩
      · simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        have : Quotient.mk (cycleSetoid p) (p (p.symm b)) = Q := by
          rw [Equiv.apply_symm_apply]; exact hb
        rw [← this]
        apply Quotient.sound
        show p.SameCycle (p.symm b) (p (p.symm b))
        exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
      · rw [Equiv.apply_symm_apply]
    · intro x _; rfl
  rw [hbij, ← two_mul]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]





/-- `vertexFlip` is even (per-orbit parity for `σ`). -/
theorem vertexFlip_even (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.σ)) :
    Even (vertexFlip M s Q) := by
  have h := orbitFlip_even M.σ s Q
  convert h using 2
  rw [vertexFlip, vertexChangeSet]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- **Per-face parity.**  The face flip count at any face is even, because the
change-indicator summed over a `φ`-orbit telescopes to `0` in `ZMod 2`: `φ` is a
bijection of the orbit, so `∑ valZ (s (φ x)) = ∑ valZ (s x)`, and the sum of
indicators is `2 ∑ valZ (s x) = 0`. -/
theorem faceFlip_even (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.φ)) :
    Even (faceFlip M s Q) := by
  have h := orbitFlip_even M.φ s Q
  convert h using 2
  rw [faceFlip, faceChangeSet]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

























































end ProofsInTheBook.Ch13MarkedSphere

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMap
-/
/- Source module: ProofsInTheBook.PlanarMapEuler -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap.CombMap

open ProofsInTheBook.PlanarMap



















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



















































lemma dartEdge_eq_mk_tail_tail_phi (M : CombMap D) (d : D) :
    M.dartEdge d = s(M.tail d, M.tail (M.φ d)) := by
  simp [dartEdge]





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



@[simp]
lemma deleteSet_apply_coe (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    ((deleteSet p S x : {d : D // d ∉ S}) : D) =
      (p ^ firstOutside p S x) x.1 :=
  rfl







end Equiv.Perm

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



































































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















namespace BoundaryPath













end BoundaryPath







namespace BoundaryCycle









































namespace Chord





end Chord

end BoundaryCycle





namespace BoundaryArcSplit











end BoundaryArcSplit



namespace BoundaryCycle













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







lemma phi_ne_self_of_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (d : D) :
    M.φ d ≠ d := by
  intro h
  have htail : M.head d = M.tail d := by
    calc
      M.head d = M.tail (M.φ d) := (M.tail_phi d).symm
      _ = M.tail d := by rw [h]
  exact hM.no_loop d htail.symm







namespace BoundaryCycle







end BoundaryCycle







namespace NearTriangulation































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

























namespace ContiguousInterval



















end ContiguousInterval



section FreshDart





















































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



namespace NearTriangulation





section ChordDarts





















end ChordDarts



























namespace ChordSplitData















































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











namespace BoundaryPath











end BoundaryPath

namespace NearTriangulation



namespace ChordSplitData































































































































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



namespace NearTriangulation











namespace ChordSplitData





















end ChordSplitData



namespace ChordSplitData











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



namespace NearTriangulation













namespace FanTriangle











end FanTriangle







namespace BoundaryVertexFan











end BoundaryVertexFan





















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



namespace NearTriangulation


















namespace BoundaryDeletionData

















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



namespace NearTriangulation













namespace NeighborRotationOrder















end NeighborRotationOrder







namespace FanSurgeryReconstruction



















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





















section Glue







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




namespace CombMap

open ProofsInTheBook.PlanarMap.CombMap





namespace ThomassenLists











end ThomassenLists





namespace ChordSplitRegions

















end ChordSplitRegions



section Deletion





































































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






















section Reduction









end Reduction



namespace NearTriangulation





































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









namespace NearTriangulation













































































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



















namespace NearTriangulation















































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





namespace BoundaryCycleData















end BoundaryCycleData









namespace DataDartArc





















end DataDartArc



namespace BoundaryCycleData











end BoundaryCycleData



section Casts













end Casts





















namespace BoundaryPath









end BoundaryPath



section BPOfDartArc





















end BPOfDartArc



namespace BoundaryCycleData









end BoundaryCycleData



namespace BoundaryCycleData







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























namespace NearTriangulation












namespace DeletedMergedBoundaryCertificate













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



namespace NearTriangulation






namespace MergedOuterArcData









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

























namespace NearTriangulation





































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







end Base



section Chord







end Chord



section Chordless



















end Chordless



section Induction









end Induction



section Corollaries








end Corollaries



section FiveColor






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










namespace ChordSideReconstruction



















end ChordSideReconstruction





namespace ChordRecursionData











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











section VertexCount

























end VertexCount



section EulerReduction







end EulerReduction



section ChordApplication

















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





section Connectivity


















end Connectivity



section SphereAssembly





end SphereAssembly



section ChordApplication













end ChordApplication



section JordanData







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







namespace SimplePrimalCycle





































































end SimplePrimalCycle









namespace SimplePrimalCycle





  -- c_i^- ↦ α (dart i)





















end SimplePrimalCycle





namespace CutCapSurgery











end CutCapSurgery



namespace NearTriangulation













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



namespace SimplePrimalCycle





















































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



lemma mergeRel_refl (p : Equiv.Perm D) (a b x : D) :
    mergeRel p a b x x := by
  exact Or.inl SameCycle.rfl

lemma mergeRel_symm {p : Equiv.Perm D} {a b x y : D} :
    mergeRel p a b x y → mergeRel p a b y x := by
  rintro (h | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨hyb, hxa⟩)
  · exact Or.inr (Or.inl ⟨hya, hxb⟩)

lemma mergeRel_trans {p : Equiv.Perm D} {a b x y z : D} :
    mergeRel p a b x y → mergeRel p a b y z → mergeRel p a b x z := by
  intro hxy hyz
  rcases hxy with hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
  · rcases hyz with hyz | ⟨hya, hzb⟩ | ⟨hyb, hza⟩
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr (Or.inl ⟨hxy.trans hya, hzb⟩)
    · exact Or.inr (Or.inr ⟨hxy.trans hyb, hza⟩)
  · rcases hyz with hyz | ⟨hya, hzb⟩ | ⟨hyb', hza⟩
    · exact Or.inr (Or.inl ⟨hxa, hyz.symm.trans hyb⟩)
    · exact Or.inr (Or.inl ⟨hxa, hzb⟩)
    · exact Or.inl (hxa.trans hza.symm)
  · rcases hyz with hyz | ⟨hya', hzb⟩ | ⟨hyb, hza⟩
    · exact Or.inr (Or.inr ⟨hxb, hyz.symm.trans hya⟩)
    · exact Or.inl (hxb.trans hzb.symm)
    · exact Or.inr (Or.inr ⟨hxb, hza⟩)

lemma mergeRel_step (p : Equiv.Perm D) (a b z : D) :
    mergeRel p a b z ((p * Equiv.swap a b) z) := by
  by_cases hza : z = a
  · subst hza
    refine Or.inr (Or.inl ⟨SameCycle.rfl, ?_⟩)
    rw [mul_apply, Equiv.swap_apply_left]
    exact sameCycle_apply_left.mpr SameCycle.rfl
  · by_cases hzb : z = b
    · subst hzb
      refine Or.inr (Or.inr ⟨SameCycle.rfl, ?_⟩)
      rw [mul_apply, Equiv.swap_apply_right]
      exact sameCycle_apply_left.mpr SameCycle.rfl
    · refine Or.inl ?_
      rw [mul_apply, Equiv.swap_apply_of_ne_of_ne hza hzb]
      exact sameCycle_apply_right.mpr SameCycle.rfl

lemma mergeRel_pow_apply (p : Equiv.Perm D) (a b x : D) (n : ℕ) :
    mergeRel p a b x (((p * Equiv.swap a b) ^ n) x) := by
  induction n with
  | zero =>
      simpa using mergeRel_refl p a b x
  | succ n ih =>
      rw [pow_succ', mul_apply]
      exact mergeRel_trans ih (mergeRel_step p a b (((p * Equiv.swap a b) ^ n) x))

lemma mergeRel_of_sameCycle_mul_swap {p : Equiv.Perm D} {a b x y : D} :
    (p * Equiv.swap a b).SameCycle x y → mergeRel p a b x y := by
  rintro ⟨i, hi⟩
  cases i with
  | ofNat n =>
      rw [← hi]
      exact mergeRel_pow_apply p a b x n
  | negSucc n =>
      have hxy : ((p * Equiv.swap a b) ^ (n + 1)) y = x := by
        rw [← hi]
        simp [zpow_negSucc, pow_succ]
      have hyx : mergeRel p a b y x := by
        simpa [hxy] using mergeRel_pow_apply p a b y (n + 1)
      exact mergeRel_symm hyx

lemma mergeRel_of_base_sameCycle {p : Equiv.Perm D} {a b x y : D}
    (hab : p.SameCycle a b) :
    mergeRel p a b x y → p.SameCycle x y := by
  rintro (h | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
  · exact h
  · exact hxa.trans (hab.trans hyb.symm)
  · exact hxb.trans (hab.symm.trans hya.symm)

lemma mul_swap_pow_succ_apply_left_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hnsc : ¬ p.SameCycle a b) :
    ∀ n : ℕ, n < orderOf (p.cycleOf b) →
      (((p * Equiv.swap a b) ^ (n + 1)) a = (p ^ (n + 1)) b)
  | 0, _ => by
      simp [mul_apply]
  | n + 1, hnlt => by
      have hnlt' : n < orderOf (p.cycleOf b) := lt_trans (Nat.lt_succ_self n) hnlt
      have ih := mul_swap_pow_succ_apply_left_of_not_sameCycle p hnsc n hnlt'
      rw [pow_succ', mul_apply, ih, mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · rw [pow_succ', mul_apply]
        simp [pow_succ', mul_apply]
      · intro ha
        apply hnsc
        have hba : p.SameCycle b a :=
          ⟨((n + 1 : ℕ) : ℤ), by simpa [zpow_natCast] using ha⟩
        exact hba.symm
      · intro hb
        have hpbn : p b ≠ b := by
          intro hpb
          have hcycle : p.cycleOf b = 1 := (cycleOf_eq_one_iff p).mpr hpb
          rw [hcycle, orderOf_one] at hnlt
          omega
        have hcb : p.cycleOf b b ≠ b := by
          simpa using hpbn
        have hcyclePow : (p.cycleOf b ^ (n + 1)) b = b := by
          simpa using hb
        have hpowOne : p.cycleOf b ^ (n + 1) = 1 :=
          ((isCycle_cycleOf p hpbn).pow_eq_one_iff' hcb).mpr hcyclePow
        exact pow_ne_one_of_lt_orderOf (by omega : n + 1 ≠ 0) hnlt hpowOne

lemma sameCycle_mul_swap_self_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hnsc : ¬ p.SameCycle a b) :
    (p * Equiv.swap a b).SameCycle a b := by
  let m := orderOf (p.cycleOf b)
  have hmpos : 0 < m := orderOf_pos (p.cycleOf b)
  cases hm : m with
  | zero =>
      omega
  | succ n =>
      refine ⟨((n + 1 : ℕ) : ℤ), ?_⟩
      have hnlt : n < orderOf (p.cycleOf b) := by
        simpa [m, hm] using Nat.lt_succ_self n
      have hq := mul_swap_pow_succ_apply_left_of_not_sameCycle p hnsc n hnlt
      have hp : (p ^ (n + 1)) b = b := by
        have hc : (p.cycleOf b ^ (n + 1)) b = b := by
          have : p.cycleOf b ^ orderOf (p.cycleOf b) = 1 := pow_orderOf_eq_one _
          simpa [m, hm] using congrFun (congrArg DFunLike.coe this) b
        simpa using hc
      change ((p * Equiv.swap a b) ^ (n + 1 : ℕ)) a = b
      exact hq.trans hp

lemma sameCycle_le_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b x y : D} (hnsc : ¬ p.SameCycle a b)
    (hxy : p.SameCycle x y) :
    (p * Equiv.swap a b).SameCycle x y := by
  let q := p * Equiv.swap a b
  have hqab : q.SameCycle a b := sameCycle_mul_swap_self_of_not_sameCycle p hnsc
  have hstep : ∀ z : D, q.SameCycle z (p z) := by
    intro z
    by_cases hza : z = a
    · subst z
      exact hqab.trans (by simpa [q, mul_apply] using (SameCycle.rfl : q.SameCycle b b).apply_right)
    · by_cases hzb : z = b
      · subst z
        exact hqab.symm.trans
          (by simpa [q, mul_apply] using (SameCycle.rfl : q.SameCycle a a).apply_right)
      · have hz : q z = p z := by simp [q, mul_apply, Equiv.swap_apply_of_ne_of_ne hza hzb]
        exact hz ▸ SameCycle.rfl.apply_right
  have hpow : ∀ n : ℕ, q.SameCycle x ((p ^ n) x) := by
    intro n
    induction n with
    | zero =>
        exact SameCycle.rfl
    | succ n ih =>
        rw [pow_succ', mul_apply]
        exact ih.trans (hstep ((p ^ n) x))
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  simpa [hn] using hpow n

lemma sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle
    (p : Equiv.Perm D) {a b x y : D} (hnsc : ¬ p.SameCycle a b) :
    (p * Equiv.swap a b).SameCycle x y ↔ mergeRel p a b x y := by
  constructor
  · exact mergeRel_of_sameCycle_mul_swap
  · intro h
    let q := p * Equiv.swap a b
    have hqab : q.SameCycle a b := sameCycle_mul_swap_self_of_not_sameCycle p hnsc
    rcases h with hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · exact sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxy
    · exact (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxa).trans
        (hqab.trans (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hyb.symm))
    · exact (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxb).trans
        (hqab.symm.trans (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hya.symm))



lemma numCycles_eq_fixed_add_cycleType_card (p : Equiv.Perm D) :
    numCycles p =
      Fintype.card (Function.fixedPoints p) + Multiset.card p.cycleType := by
  classical
  unfold numCycles
  calc
    Fintype.card (Quotient (SameCycle.setoid p))
        = Fintype.card (Function.fixedPoints p ⊕ p.cycleFactorsFinset) :=
          Fintype.card_congr (orbitEquivFixedOrCycles p)
    _ = Fintype.card (Function.fixedPoints p) + Fintype.card p.cycleFactorsFinset := by
          simp
    _ = Fintype.card (Function.fixedPoints p) + Multiset.card p.cycleType := by
          rw [cycleType_def]
          simp



theorem numCycles_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) (hnsc : ¬ p.SameCycle a b) :
    numCycles (p * Equiv.swap a b) + 1 = numCycles p := by
  classical
  let q : Equiv.Perm D := p * Equiv.swap a b
  let P := Quotient (SameCycle.setoid p)
  let Q := Quotient (SameCycle.setoid q)
  let A : P := Quotient.mk (SameCycle.setoid p) a
  let B : P := Quotient.mk (SameCycle.setoid p) b
  have hAB : A ≠ B := by
    intro h
    exact hnsc (Quotient.exact h)
  have hpq : ∀ {x y : D}, p.SameCycle x y → q.SameCycle x y := by
    intro x y hxy
    exact sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxy
  let mergeMap : P → Q := Quotient.map' id (fun x y hxy => hpq hxy)
  let f : {u : P // u ≠ B} → Q := fun u => mergeMap u.1
  have hsurj : Function.Surjective f := by
    intro v
    refine Quotient.inductionOn v ?_
    intro x
    by_cases hxB : (Quotient.mk (SameCycle.setoid p) x : P) = B
    · refine ⟨⟨A, hAB⟩, ?_⟩
      have hxb : p.SameCycle x b := Quotient.exact hxB
      have hqxa : q.SameCycle x a :=
        (hpq hxb).trans (sameCycle_mul_swap_self_of_not_sameCycle p hnsc).symm
      apply Quotient.sound hqxa.symm
    · refine ⟨⟨Quotient.mk (SameCycle.setoid p) x, hxB⟩, ?_⟩
      rfl
  have hinj : Function.Injective f := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    apply Subtype.ext
    dsimp [f, mergeMap] at huv
    revert hu hv huv
    refine Quotient.inductionOn₂ u v ?_
    intro x y hxB hyB hxy
    simp only [Quotient.map'_mk'', id_eq] at hxy
    have hqxy : q.SameCycle x y := Quotient.exact hxy
    have hR : mergeRel p a b x y :=
      (sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle p hnsc).mp hqxy
    rcases hR with hpxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · exact Quotient.sound hpxy
    · exfalso
      exact hyB (Quotient.sound hyb)
    · exfalso
      exact hxB (Quotient.sound hxb)
  have hcard_equiv : Fintype.card {u : P // u ≠ B} = Fintype.card Q :=
    Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  have hsub_card : Fintype.card {u : P // u ≠ B} + 1 = Fintype.card P := by
    have hcompl :
        Fintype.card {u : P // u ≠ B} = Fintype.card P - 1 := by
      simpa [Fintype.card_subtype_eq B] using
        (Fintype.card_subtype_compl (fun u : P => u = B))
    have hpos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨B⟩
    omega
  unfold numCycles
  change Fintype.card Q + 1 = Fintype.card P
  rw [← hcard_equiv]
  exact hsub_card

lemma sign_eq_of_numCycles_eq (p q : Equiv.Perm D)
    (hnum : numCycles p = numCycles q) :
    Equiv.Perm.sign p = Equiv.Perm.sign q := by
  classical
  have hpnum :
      numCycles p = Fintype.card D - p.cycleType.sum + Multiset.card p.cycleType := by
    rw [numCycles_eq_fixed_add_cycleType_card, Equiv.Perm.card_fixedPoints]
  have hqnum :
      numCycles q = Fintype.card D - q.cycleType.sum + Multiset.card q.cycleType := by
    rw [numCycles_eq_fixed_add_cycleType_card, Equiv.Perm.card_fixedPoints]
  have hmod :
      (p.cycleType.sum + Multiset.card p.cycleType) % 2 =
        (q.cycleType.sum + Multiset.card q.cycleType) % 2 := by
    have hp_le := p.sum_cycleType_le
    have hq_le := q.sum_cycleType_le
    omega
  apply Units.ext
  rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sign_of_cycleType]
  simp [neg_one_pow_eq_pow_mod_two, hmod]

lemma numCycles_mul_swap_ne (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) ≠ numCycles p := by
  intro hnum
  have hsign_eq := sign_eq_of_numCycles_eq (p * Equiv.swap a b) p hnum
  have hsign_neg :
      Equiv.Perm.sign (p * Equiv.swap a b) = -Equiv.Perm.sign p := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
    simp
  rw [hsign_neg] at hsign_eq
  have hself : Equiv.Perm.sign p = -Equiv.Perm.sign p := hsign_eq.symm
  have hone : (1 : ℤˣ) = -1 := by
    calc
      (1 : ℤˣ) = (Equiv.Perm.sign p)⁻¹ * Equiv.Perm.sign p := by simp
      _ = (Equiv.Perm.sign p)⁻¹ * (-Equiv.Perm.sign p) := by
        exact congrArg ((Equiv.Perm.sign p)⁻¹ * ·) hself
      _ = -1 := by
        rw [mul_neg, inv_mul_cancel]
  have hval := congrArg Units.val hone
  norm_num at hval

lemma numCycles_le_mul_swap_of_sameCycle
    (p : Equiv.Perm D) {a b : D} (hsc : p.SameCycle a b) :
    numCycles p ≤ numCycles (p * Equiv.swap a b) := by
  classical
  let q : Equiv.Perm D := p * Equiv.swap a b
  let P := Quotient (SameCycle.setoid p)
  let Q := Quotient (SameCycle.setoid q)
  have hrel : ∀ {x y : D}, q.SameCycle x y → p.SameCycle x y := by
    intro x y hxy
    exact mergeRel_of_base_sameCycle hsc (mergeRel_of_sameCycle_mul_swap hxy)
  let g : Q → P := Quotient.map' id (fun x y hxy => hrel hxy)
  have hsurj : Function.Surjective g := by
    intro u
    refine Quotient.inductionOn u ?_
    intro x
    exact ⟨Quotient.mk (SameCycle.setoid q) x, rfl⟩
  unfold numCycles
  change Fintype.card P ≤ Fintype.card Q
  exact Fintype.card_le_of_surjective g hsurj

theorem numCycles_mul_swap_dichotomy
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) = numCycles p + 1 ∨
    numCycles (p * Equiv.swap a b) + 1 = numCycles p := by
  by_cases hnsc : ¬ p.SameCycle a b
  · exact Or.inr (numCycles_mul_swap_of_not_sameCycle p hab hnsc)
  · have hsc : p.SameCycle a b := by simpa using Classical.not_not.mp hnsc
    let q : Equiv.Perm D := p * Equiv.swap a b
    have hp_le_q : numCycles p ≤ numCycles q :=
      numCycles_le_mul_swap_of_sameCycle p hsc
    by_cases hqsc : q.SameCycle a b
    · have hq_le_p : numCycles q ≤ numCycles p := by
        have h := numCycles_le_mul_swap_of_sameCycle q hqsc
        simpa [q, mul_assoc] using h
      have heq : numCycles q = numCycles p := le_antisymm hq_le_p hp_le_q
      exact False.elim (numCycles_mul_swap_ne p hab heq)
    · have h := numCycles_mul_swap_of_not_sameCycle q hab hqsc
      exact Or.inl (by simpa [q, mul_assoc] using h.symm)

end PermTranspositionCycleCount

theorem numCycles_mul_swap_dichotomy
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) = numCycles p + 1 ∨
    numCycles (p * Equiv.swap a b) + 1 = numCycles p :=
  PermTranspositionCycleCount.numCycles_mul_swap_dichotomy p hab

theorem numCycles_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) (hnsc : ¬ p.SameCycle a b) :
    numCycles (p * Equiv.swap a b) + 1 = numCycles p :=
  PermTranspositionCycleCount.numCycles_mul_swap_of_not_sameCycle p hab hnsc

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

















omit [Fintype V] in
private theorem eqvGen_mono {r s : V → V → Prop}
    (h : ∀ ⦃x y : V⦄, r x y → s x y) {x y : V} :
    Relation.EqvGen r x y → Relation.EqvGen s x y := by
  intro hxy
  induction hxy with
  | rel x y hxy =>
      exact Relation.EqvGen.rel x y (h hxy)
  | refl x =>
      exact Relation.EqvGen.refl x
  | symm x y _ ih =>
      exact Relation.EqvGen.symm x y ih
  | trans x y z _ _ ihxy ihyz =>
      exact Relation.EqvGen.trans x y z ihxy ihyz

omit [Fintype V] in
private theorem eqvGen_le_addEdge (r : V → V → Prop) (a b : V) {x y : V} :
    Relation.EqvGen r x y → Relation.EqvGen (addEdge r a b) x y := by
  intro hxy
  exact eqvGen_mono (s := addEdge r a b) (fun {x y} hr => Or.inl hr) hxy

omit [Fintype V] in
private theorem eqvGen_addEdge_iff_pairRel (r : V → V → Prop) (a b x y : V) :
    Relation.EqvGen (addEdge r a b) x y ↔
      pairRel (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)
        (Quotient.mk (compSetoid r) x) (Quotient.mk (compSetoid r) y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel x y hxy =>
        rcases hxy with hr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (Quotient.sound (Relation.EqvGen.rel x y hr))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | refl x =>
        exact pairRel_refl _ _ _
    | symm x y _ ih =>
        exact pairRel_symm _ _ ih
    | trans x y z _ _ ihxy ihyz =>
        exact pairRel_trans _ _ ihxy ihyz
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact eqvGen_le_addEdge r a b (Quotient.exact hxy)
    · rcases hxab with ⟨hxa, hyb⟩
      have hxa' : Relation.EqvGen (addEdge r a b) x a :=
        eqvGen_le_addEdge r a b (Quotient.exact hxa)
      have hby' : Relation.EqvGen (addEdge r a b) b y :=
        Relation.EqvGen.symm y b (eqvGen_le_addEdge r a b (Quotient.exact hyb))
      have hab' : Relation.EqvGen (addEdge r a b) a b :=
        Relation.EqvGen.rel a b (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact Relation.EqvGen.trans x a y hxa'
        (Relation.EqvGen.trans a b y hab' hby')
    · rcases hxba with ⟨hxb, hya⟩
      have hxb' : Relation.EqvGen (addEdge r a b) x b :=
        eqvGen_le_addEdge r a b (Quotient.exact hxb)
      have hay' : Relation.EqvGen (addEdge r a b) a y :=
        Relation.EqvGen.symm y a (eqvGen_le_addEdge r a b (Quotient.exact hya))
      have hba' : Relation.EqvGen (addEdge r a b) b a :=
        Relation.EqvGen.rel b a (Or.inr (Or.inr ⟨rfl, rfl⟩))
      exact Relation.EqvGen.trans x b y hxb'
        (Relation.EqvGen.trans b a y hba' hay')

omit [Fintype V] in
private theorem eqvGen_addEdge_iff (r : V → V → Prop) (a b x y : V) :
    Relation.EqvGen (addEdge r a b) x y ↔
      Relation.EqvGen r x y
        ∨ (Relation.EqvGen r x a ∧ Relation.EqvGen r y b)
        ∨ (Relation.EqvGen r x b ∧ Relation.EqvGen r y a) := by
  rw [eqvGen_addEdge_iff_pairRel]
  constructor
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact Or.inl (Quotient.exact hxy)
    · exact Or.inr (Or.inl ⟨Quotient.exact hxab.1, Quotient.exact hxab.2⟩)
    · exact Or.inr (Or.inr ⟨Quotient.exact hxba.1, Quotient.exact hxba.2⟩)
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact Or.inl (Quotient.sound hxy)
    · exact Or.inr (Or.inl ⟨Quotient.sound hxab.1, Quotient.sound hxab.2⟩)
    · exact Or.inr (Or.inr ⟨Quotient.sound hxba.1, Quotient.sound hxba.2⟩)

private def quotientEquivOfRelIff {α : Type u} (s t : Setoid α)
    (h : ∀ x y : α, s.r x y ↔ t.r x y) :
    Quotient s ≃ Quotient t where
  toFun := Quotient.map id (by
    intro x y hxy
    exact (h x y).1 hxy)
  invFun := Quotient.map id (by
    intro x y hxy
    exact (h x y).2 hxy)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl

private def pairRep {α : Type u} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (x : α) : {x : α // x ≠ b} :=
  if hx : x = b then ⟨a, hab⟩ else ⟨x, hx⟩

private def pairQuotEquivSubtypeNe {α : Type u} [DecidableEq α] {a b : α}
    (hab : a ≠ b) :
    Quotient (pairSetoid a b) ≃ {x : α // x ≠ b} where
  toFun := Quotient.lift (pairRep hab) (by
    intro x y hxy
    change pairRel a b x y at hxy
    rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simp [pairRep, hab]
    · simp [pairRep, hab])
  invFun := fun x => Quotient.mk (pairSetoid a b) x.1
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    dsimp
    by_cases hx : x = b
    · subst x
      simp [pairRep]
      exact Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · simp [pairRep, hx]
  right_inv := by
    intro x
    ext
    simp [pairRep, x.2]

private theorem pairSetoid_card_add_one {α : Type u} [Fintype α] [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    Nat.card (Quotient (pairSetoid a b)) + 1 = Nat.card α := by
  classical
  haveI : Fintype (Quotient (pairSetoid a b)) := Quotient.fintype (pairSetoid a b)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcardEquiv :
      Fintype.card (Quotient (pairSetoid a b)) = Fintype.card {x : α // x ≠ b} :=
    Fintype.card_congr (pairQuotEquivSubtypeNe hab)
  rw [hcardEquiv]
  have hcompl := Fintype.card_subtype_compl (fun x : α => x = b)
  have hsingle : Fintype.card {x : α // x = b} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨b, rfl⟩, ?_⟩
    intro y
    ext
    exact y.2
  rw [hcompl, hsingle]
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨b⟩
  omega

private def compAddQuotEquivPairQuot (r : V → V → Prop) (a b : V) :
    Quotient (compSetoid (addEdge r a b)) ≃
      Quotient
        (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)) where
  toFun := Quotient.lift
    (fun x =>
      Quotient.mk
        (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b))
        (Quotient.mk (compSetoid r) x))
    (by
      intro x y hxy
      exact Quotient.sound ((eqvGen_addEdge_iff_pairRel r a b x y).1 hxy))
  invFun :=
    Quotient.lift
      (Quotient.map id (by
        intro x y hxy
        exact eqvGen_le_addEdge r a b hxy))
      (by
        intro x y hxy
        change pairRel (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b) x y
          at hxy
        rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Quotient.sound (Relation.EqvGen.rel a b (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        · exact Quotient.sound (Relation.EqvGen.rel b a (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    refine Quotient.inductionOn x ?_
    intro v
    rfl

omit [Fintype V] in
theorem numComp_addEdge_of_eqvGen (r : V → V → Prop) {a b : V}
    (h : Relation.EqvGen r a b) :
    numComp (addEdge r a b) = numComp r := by
  unfold numComp
  apply Nat.card_congr
  refine quotientEquivOfRelIff (compSetoid (addEdge r a b)) (compSetoid r) ?_
  intro x y
  constructor
  · intro hxy
    change Relation.EqvGen (addEdge r a b) x y at hxy
    rw [eqvGen_addEdge_iff] at hxy
    rcases hxy with hxy | hxab | hxba
    · exact hxy
    · exact Relation.EqvGen.trans x a y hxab.1
        (Relation.EqvGen.trans a b y h (Relation.EqvGen.symm y b hxab.2))
    · exact Relation.EqvGen.trans x b y hxba.1
        (Relation.EqvGen.trans b a y (Relation.EqvGen.symm a b h)
          (Relation.EqvGen.symm y a hxba.2))
  · intro hxy
    exact eqvGen_le_addEdge r a b hxy

theorem numComp_addEdge_of_not_eqvGen (r : V → V → Prop) {a b : V}
    (h : ¬ Relation.EqvGen r a b) :
    numComp (addEdge r a b) + 1 = numComp r := by
  classical
  let Q := Quotient (compSetoid r)
  let A : Q := Quotient.mk (compSetoid r) a
  let B : Q := Quotient.mk (compSetoid r) b
  haveI : Fintype Q := Quotient.fintype (compSetoid r)
  have hAB : A ≠ B := by
    intro hq
    exact h (Quotient.exact hq)
  unfold numComp
  change Nat.card (Quotient (compSetoid (addEdge r a b))) + 1 = Nat.card Q
  have hcard :
      Nat.card
          (Quotient
            (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)))
          + 1 =
        Nat.card Q := by
    simpa [Q, A, B] using pairSetoid_card_add_one hAB
  rw [Nat.card_congr (compAddQuotEquivPairQuot r a b)]
  exact hcard

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



open scoped Classical in
/-- The repo's orbit count (`Fintype.card (Quotient (cycleSetoid p))`) agrees with
`_root_.numCycles p` (built from `SameCycle.setoid`): the two setoids
carry the identical relation `p.SameCycle`. -/
lemma card_cycleSetoid_eq_numCycles (p : Equiv.Perm D) :
    Fintype.card (Quotient (cycleSetoid p)) = _root_.numCycles p := by
  classical
  unfold _root_.numCycles
  exact Fintype.card_congr
    (Quotient.congr (Equiv.refl D) (fun x y => by rfl))

lemma V_eq_numCycles (M : CombMap D) : M.V = _root_.numCycles M.σ :=
  card_cycleSetoid_eq_numCycles M.σ

lemma F_eq_numCycles (M : CombMap D) : M.F = _root_.numCycles M.φ :=
  card_cycleSetoid_eq_numCycles M.φ





omit [Fintype D] [DecidableEq D] in
lemma dartStepRel_symm {σ α : Equiv.Perm D} (hα : α * α = 1) {a b : D}
    (h : dartStepRel σ α a b) : dartStepRel σ α b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    subst h
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ.symm



omit [Fintype D] [DecidableEq D] in
/-- `ReflTransGen` of a symmetric relation is symmetric. -/
lemma reflTransGen_symm {r : D → D → Prop} (hsymm : ∀ a b, r a b → r b a)
    {a b : D} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

omit [Fintype D] [DecidableEq D] in
/-- For a symmetric relation, the equivalence closure is the reflexive-transitive
closure (the repo's `Connected` is phrased with `ReflTransGen`). -/
lemma eqvGen_iff_reflTransGen {r : D → D → Prop} (hsymm : ∀ a b, r a b → r b a)
    (a b : D) :
    Relation.EqvGen r a b ↔ Relation.ReflTransGen r a b := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact Relation.ReflTransGen.single hxy
    | refl x => exact Relation.ReflTransGen.refl
    | symm x y _ ih => exact reflTransGen_symm hsymm ih
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl a
    | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)







/-- Removing the transposition `{a, b}` (with `α a = b`, `a ≠ b`) from an
involution `α`: the support loses exactly `a` and `b`. -/
lemma support_mul_swap_of_apply (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    Equiv.Perm.support (α * Equiv.swap a b) = (Equiv.Perm.support α) \ {a, b} := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have : α (α a) = a := by
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at this; exact this
  ext x
  simp only [Equiv.Perm.mem_support, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton, ne_eq]
  constructor
  · intro hx
    rcases eq_or_ne x a with rfl | hxa
    · exact absurd (by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb]) hx
    · rcases eq_or_ne x b with rfl | hxb
      · exact absurd (by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa]) hx
      · refine ⟨?_, fun h => by rcases h with h | h <;> simp_all⟩
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb] at hx
        exact hx
  · rintro ⟨hx, hx2⟩
    push_neg at hx2
    obtain ⟨hxa, hxb⟩ := hx2
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    exact hx

/-- `a` and `b` are distinct elements of `support α` when `α a = b`. -/
lemma mem_support_of_apply_ne {α : Equiv.Perm D} {a b : D} (hab : a ≠ b)
    (hαa : α a = b) : a ∈ Equiv.Perm.support α ∧ b ∈ Equiv.Perm.support α := by
  classical
  constructor
  · rw [Equiv.Perm.mem_support, hαa]; exact hab.symm
  · rw [Equiv.Perm.mem_support]
    intro hb
    -- if `α b = b` then `α a = b` and injectivity force `a = b`
    exact hab (α.injective (by rw [hαa, hb]))

/-- Deleting one transposition drops `Ehalf` by exactly one. -/
lemma Ehalf_mul_swap (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    Ehalf (α * Equiv.swap a b) + 1 = Ehalf α := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have : α (α a) = a := by
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at this; exact this
  have hsupp := support_mul_swap_of_apply α hα hab hαa
  obtain ⟨ha, hb⟩ := mem_support_of_apply_ne hab hαa
  have hpair : ({a, b} : Finset D) ⊆ Equiv.Perm.support α := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard2 : ({a, b} : Finset D).card = 2 := by
    rw [Finset.card_pair hab]
  have hinter : ({a, b} : Finset D) ∩ Equiv.Perm.support α = {a, b} :=
    Finset.inter_eq_left.mpr hpair
  have hcards : (Equiv.Perm.support (α * Equiv.swap a b)).card
      = (Equiv.Perm.support α).card - 2 := by
    rw [hsupp, Finset.card_sdiff, hinter, hcard2]
  -- `support α` has even cardinality (involution), and contains the 2-element pair.
  have heven : 2 ∣ (Equiv.Perm.support α).card :=
    Equiv.Perm.two_dvd_card_support (by
      have : α ^ 2 = 1 := by rw [pow_two]; exact hα
      exact this)
  have h2le : 2 ≤ (Equiv.Perm.support α).card := by
    have := Finset.card_le_card hpair
    rwa [hcard2] at this
  unfold Ehalf
  rw [hcards]
  omega



open Relation in
/-- One application of `σ * α` is a 2-step `dartStepRel` walk `x → α x → σ(α x)`. -/
lemma reflTransGen_dartStepRel_mul_apply (σ α : Equiv.Perm D) (x : D) :
    ReflTransGen (dartStepRel σ α) x ((σ * α) x) := by
  have h1 : dartStepRel σ α x (α x) := Or.inr rfl
  have h2 : dartStepRel σ α (α x) ((σ * α) x) := by
    refine Or.inl ?_
    have hmul : (σ * α) x = σ (α x) := rfl
    rw [hmul]
    exact ⟨1, by simp⟩
  exact (ReflTransGen.single h1).tail h2

open Relation in
/-- A `σα`-power walk lifts to a `dartStepRel` reflexive-transitive walk. -/
lemma reflTransGen_dartStepRel_of_pow (σ α : Equiv.Perm D) :
    ∀ (k : ℕ) (x : D), ReflTransGen (dartStepRel σ α) x (((σ * α) ^ k) x) := by
  intro k
  induction k with
  | zero => intro x; simpa using ReflTransGen.refl
  | succ k ih =>
      intro x
      have hstep := reflTransGen_dartStepRel_mul_apply σ α (((σ * α) ^ k) x)
      have hpow : ((σ * α) ^ (k + 1)) x = (σ * α) (((σ * α) ^ k) x) := by
        rw [pow_succ']; rfl
      rw [hpow]
      exact (ih x).trans hstep

open Relation in
/-- Same `σα`-cycle implies the two darts are `dartStepRel`-connected. -/
lemma eqvGen_dartStepRel_of_sameCycle_mul (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (h : (σ * α).SameCycle a b) :
    EqvGen (dartStepRel σ α) a b := by
  rw [eqvGen_iff_reflTransGen (fun x y => dartStepRel_symm hα)]
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  exact reflTransGen_dartStepRel_of_pow σ α k a



/-- With `α a = b`, `α b = a`, `a ≠ b`, the dart relation of `α` is the dart
relation of `α' = α * swap a b` (which fixes `a, b`) with the single edge `{a, b}`
re-added. -/
lemma dartStepRel_eq_addEdge (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    dartStepRel σ α
      = _root_.addEdge (dartStepRel σ (α * Equiv.swap a b)) a b := by
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  funext x y
  simp only [dartStepRel, _root_.addEdge, eq_iff_iff]
  have hrefl : σ.SameCycle x x := Equiv.Perm.SameCycle.refl σ x
  rcases eq_or_ne x a with rfl | hxa
  · -- `x = a`: `a` is eliminated, the surviving name is `x`
    have hα' : (α * Equiv.swap x b) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb]
    rw [hαa, hα']
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rintro ((h | h) | ⟨_, h⟩ | ⟨hxb, _⟩)
      · exact Or.inl h
      · exact Or.inl (h ▸ hrefl)
      · exact Or.inr h
      · exact absurd hxb hab
  · rcases eq_or_ne x b with rfl | hxb
    · -- `x = b`: surviving name is `x`
      have hα' : (α * Equiv.swap a x) x = x := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa]
      rw [hαb, hα']
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · subst h; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · rintro ((h | h) | ⟨hxa', _⟩ | ⟨_, h⟩)
        · exact Or.inl h
        · exact Or.inl (h ▸ hrefl)
        · exact absurd hxa' hxa
        · exact Or.inr h
    · have hα' : (α * Equiv.swap a b) x = α x := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
      rw [hα']
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
      · rintro ((h | h) | ⟨hxa', _⟩ | ⟨hxb', _⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd hxa' hxa
        · exact absurd hxb' hxb



/-- Removing one transposition from an involution leaves an involution. -/
lemma mul_swap_involutive (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hαa : α a = b) (hαb : α b = a) :
    (α * Equiv.swap a b) * (α * Equiv.swap a b) = 1 := by
  ext x
  simp only [Equiv.Perm.coe_one, id_eq]
  have hαα : ∀ z, α (α z) = z := by
    intro z
    have happ := congrArg (fun f : Equiv.Perm D => f z) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
  rcases eq_or_ne x a with rfl | hxa
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb, Equiv.swap_apply_right,
      hαa]
  · rcases eq_or_ne x b with rfl | hxb
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa, Equiv.swap_apply_left,
        hαb]
    · have hαxa : α x ≠ a := by
        intro h
        apply hxb
        have : x = α a := by rw [← hαα x, h]
        rw [this, hαa]
      have hαxb : α x ≠ b := by
        intro h
        apply hxa
        have : x = α b := by rw [← hαα x, h]
        rw [this, hαb]
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb,
        Equiv.swap_apply_of_ne_of_ne hαxa hαxb, hαα]





lemma numComponents_def (σ α : Equiv.Perm D) :
    numComponents σ α = _root_.numComp (dartStepRel σ α) := rfl




open scoped Classical in
/-- For `α = 1` the dart relation is just `σ.SameCycle`. -/
lemma dartStepRel_one (σ : Equiv.Perm D) :
    dartStepRel σ 1 = fun x y => σ.SameCycle x y := by
  funext x y
  simp only [dartStepRel, Equiv.Perm.coe_one, id_eq, eq_iff_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact h ▸ Equiv.Perm.SameCycle.refl σ x
  · intro h; exact Or.inl h

open scoped Classical in
/-- For `α = 1` the components are exactly the `σ`-orbits. -/
lemma numComponents_one (σ : Equiv.Perm D) :
    numComponents σ 1 = numCycles σ := by
  classical
  rw [numComponents_def, dartStepRel_one]
  unfold _root_.numComp _root_.numCycles
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl D) ?_
  intro x y
  simp only [Equiv.refl_apply]
  have hrel : Relation.EqvGen (fun x y => σ.SameCycle x y) x y ↔ σ.SameCycle x y :=
    Equivalence.eqvGen_iff (Equiv.Perm.SameCycle.equivalence σ)
  exact hrel



/-- **Genus nonnegativity.** For every involution `α`, `genusSlack σ α ≥ 0`. -/
lemma genusSlack_nonneg (σ : Equiv.Perm D) :
    ∀ α : Equiv.Perm D, α * α = 1 → 0 ≤ genusSlack σ α := by
  intro α
  induction hn : (Equiv.Perm.support α).card using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    intro hα
    rcases eq_or_ne (Equiv.Perm.support α) ∅ with hemp | hemp
    · -- base case: α = 1
      have hα1 : α = 1 := Equiv.Perm.support_eq_empty_iff.mp hemp
      subst hα1
      have hEhalf : Ehalf (1 : Equiv.Perm D) = 0 := by simp [Ehalf]
      have hmul : (σ * 1) = σ := mul_one σ
      have hcomp : numComponents σ 1 = numCycles σ := numComponents_one σ
      unfold genusSlack
      rw [hEhalf, hmul, hcomp]
      push_cast
      ring_nf
      positivity
    · -- inductive step: delete one transposition {a, b}
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hane : α a ≠ a := Equiv.Perm.mem_support.mp ha
      obtain ⟨b, hαa⟩ : ∃ b, α a = b := ⟨α a, rfl⟩
      have hab : a ≠ b := fun h => hane (by rw [hαa, ← h])
      have hαb : α b = a := by
        have happ := congrArg (fun f : Equiv.Perm D => f a) hα
        have hh : α (α a) = a := by
          simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
        rw [hαa] at hh; exact hh
      set α' := α * Equiv.swap a b with hα'def
      have hα'invol : α' * α' = 1 := mul_swap_involutive α hα hαa hαb
      have hsupp' : Equiv.Perm.support α' = (Equiv.Perm.support α) \ {a, b} :=
        support_mul_swap_of_apply α hα hab hαa
      have hcard' : (Equiv.Perm.support α').card < n := by
        rw [← hn, hsupp']
        apply Finset.card_lt_card
        refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨a, ha, ?_⟩
        simp
      have IHα' := ih _ hcard' α' rfl hα'invol
      have hEhalf : Ehalf α' + 1 = Ehalf α := Ehalf_mul_swap α hα hab hαa
      have hface : σ * α = (σ * α') * Equiv.swap a b := by
        rw [hα'def, mul_assoc, mul_assoc, Equiv.swap_mul_self, mul_one]
      have hrel : dartStepRel σ α = _root_.addEdge (dartStepRel σ α') a b :=
        dartStepRel_eq_addEdge σ α hα hab hαa
      have hcompEq : numComponents σ α
          = _root_.numComp (_root_.addEdge (dartStepRel σ α') a b) := by
        rw [numComponents_def, hrel]
      have hdich := _root_.numCycles_mul_swap_dichotomy (σ * α') hab
      rw [← hface] at hdich
      have hEz : (Ehalf α : ℤ) = (Ehalf α' : ℤ) + 1 := by
        have h := hEhalf; push_cast [← h]; ring
      by_cases hsame : Relation.EqvGen (dartStepRel σ α') a b
      · -- same component: numComponents unchanged
        have hC : numComponents σ α = numComponents σ α' := by
          rw [hcompEq, numComponents_def]
          exact _root_.numComp_addEdge_of_eqvGen _ hsame
        unfold genusSlack at IHα' ⊢
        rw [hC, hEz]
        rcases hdich with hd | hd
        · rw [hd]; push_cast; linarith [IHα']
        · have hF : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
            have h := hd; push_cast [← h]; ring
          rw [hF]; linarith [IHα']
      · -- different components: merge, count drops by 1; faces also merge
        have hC : numComponents σ α + 1 = numComponents σ α' := by
          rw [hcompEq, numComponents_def]
          exact _root_.numComp_addEdge_of_not_eqvGen _ hsame
        have hnsc : ¬ (σ * α').SameCycle a b := fun h =>
          hsame (eqvGen_dartStepRel_of_sameCycle_mul σ α' hα'invol h)
        have hmerge : numCycles (σ * α) + 1 = numCycles (σ * α') := by
          have h := _root_.numCycles_mul_swap_of_not_sameCycle
            (σ * α') hab hnsc
          rw [← hface] at h; exact h
        unfold genusSlack at IHα' ⊢
        have hCz : (numComponents σ α : ℤ) = (numComponents σ α' : ℤ) - 1 := by
          have h := hC; push_cast [← h]; ring
        have hFz : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
          have h := hmerge; push_cast [← h]; ring
        rw [hCz, hEz, hFz]
        linarith [IHα']



/-- For a fixed-point-free involution, every dart is in the support. -/
lemma support_eq_univ_of_no_fixed (M : CombMap D) :
    Equiv.Perm.support M.α = Finset.univ := by
  classical
  rw [Finset.eq_univ_iff_forall]
  intro d
  rw [Equiv.Perm.mem_support]
  exact M.α_no_fixed d

/-- For the (fixed-point-free) edge involution of a `CombMap`, `Ehalf = E`. -/
lemma Ehalf_eq_E (M : CombMap D) : Ehalf M.α = M.E := by
  classical
  have h2E : 2 * M.E = Fintype.card D := two_mul_E_eq_card M
  unfold Ehalf
  rw [support_eq_univ_of_no_fixed M, Finset.card_univ]
  omega

/-- `M.dartStep` is exactly `dartStepRel M.σ M.α`. -/
lemma dartStep_eq_dartStepRel (M : CombMap D) :
    M.dartStep = dartStepRel M.σ M.α := rfl

open scoped Classical in
/-- A connected map on a nonempty dart set has exactly one component. -/
lemma numComponents_eq_one_of_connected (M : CombMap D) (hconn : M.Connected)
    (d₀ : D) : numComponents M.σ M.α = 1 := by
  classical
  rw [numComponents_def]
  unfold _root_.numComp
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨?_, ⟨Quotient.mk (_root_.compSetoid (dartStepRel M.σ M.α)) d₀⟩⟩
  -- subsingleton: any two quotient points are equal
  constructor
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a c
  apply Quotient.sound
  show Relation.EqvGen (dartStepRel M.σ M.α) a c
  rw [eqvGen_iff_reflTransGen (fun u v => dartStepRel_symm M.α_invol)]
  have h := hconn a c
  rw [dartStep_eq_dartStepRel] at h
  exact h




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





namespace CutCapCount

















section SumCongr





















end SumCongr

end CutCapCount



namespace SimplePrimalCycle



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



namespace SimplePrimalCycle



open CutCapCount
































end SimplePrimalCycle

namespace CutCapCount















end CutCapCount

namespace SimplePrimalCycle



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



namespace CutCapCount







end CutCapCount

namespace SimplePrimalCycle



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





section FacePerm















end FacePerm



section FaceBijection







































end FaceBijection



section Dichotomy













end Dichotomy



section Genus0











end Genus0



section SphereAssembly







end SphereAssembly



section NonVacuity







end NonVacuity



section ChordApplication









end ChordApplication



section Headline







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





section Facts







end Facts



section LowerHalf







end LowerHalf



section Threading









end Threading



section ChordApplication





















end ChordApplication



section NonVacuity











end NonVacuity



section Headline







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



/-- **Single-edge removal does not increase the genus slack.**  If `α a = b` with `a ≠ b`
(so `{a, b}` is an edge of the involution `α`), then deleting it
(`α' = α * swap a b`, which fixes `a, b`) gives `genusSlack σ α' ≤ genusSlack σ α`. -/
theorem genusSlack_remove_le (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    genusSlack σ (α * Equiv.swap a b) ≤ genusSlack σ α := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  set α' := α * Equiv.swap a b with hα'def
  have hα'invol : α' * α' = 1 := mul_swap_involutive α hα hαa hαb
  -- Edge count: `Ehalf α' + 1 = Ehalf α`.
  have hEhalf : Ehalf α' + 1 = Ehalf α := Ehalf_mul_swap α hα hab hαa
  have hEz : (Ehalf α : ℤ) = (Ehalf α' : ℤ) + 1 := by
    have h := hEhalf; push_cast [← h]; ring
  -- Face permutation: `σ * α = (σ * α') * swap a b`.
  have hface : σ * α = (σ * α') * Equiv.swap a b := by
    rw [hα'def, mul_assoc, mul_assoc, Equiv.swap_mul_self, mul_one]
  -- Component relation via `addEdge`.
  have hrel : dartStepRel σ α = _root_.addEdge (dartStepRel σ α') a b :=
    dartStepRel_eq_addEdge σ α hα hab hαa
  have hcompEq : numComponents σ α
      = _root_.numComp (_root_.addEdge (dartStepRel σ α') a b) := by
    rw [numComponents_def, hrel]
  -- Face cycle-count dichotomy.
  have hdich := _root_.numCycles_mul_swap_dichotomy (σ * α') hab
  rw [← hface] at hdich
  by_cases hsame : Relation.EqvGen (dartStepRel σ α') a b
  · -- Same component: `c` unchanged; `F` either unchanged (slack +1) or drops (slack +2).
    have hC : numComponents σ α = numComponents σ α' := by
      rw [hcompEq, numComponents_def]
      exact _root_.numComp_addEdge_of_eqvGen _ hsame
    unfold genusSlack at *
    rw [hC, hEz]
    rcases hdich with hd | hd
    · rw [hd]; push_cast; linarith
    · have hF : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
        have h := hd; push_cast [← h]; ring
      rw [hF]; linarith
  · -- Different components: `c` drops by one; faces merge (`F` drops by one); slack unchanged.
    have hC : numComponents σ α + 1 = numComponents σ α' := by
      rw [hcompEq, numComponents_def]
      exact _root_.numComp_addEdge_of_not_eqvGen _ hsame
    have hnsc : ¬ (σ * α').SameCycle a b := fun h =>
      hsame (eqvGen_dartStepRel_of_sameCycle_mul σ α' hα'invol h)
    have hmerge : numCycles (σ * α) + 1 = numCycles (σ * α') := by
      have h := _root_.numCycles_mul_swap_of_not_sameCycle (σ * α') hab hnsc
      rw [← hface] at h; exact h
    unfold genusSlack at *
    have hCz : (numComponents σ α : ℤ) = (numComponents σ α' : ℤ) - 1 := by
      have h := hC; push_cast [← h]; ring
    have hFz : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
      have h := hmerge; push_cast [← h]; ring
    rw [hCz, hEz, hFz]; linarith





/-- A sub-involution's support is contained in `α`'s support. -/
lemma SubInvolution.support_subset {α α' : Equiv.Perm D} (h : SubInvolution α α') :
    Equiv.Perm.support α' ⊆ Equiv.Perm.support α := by
  classical
  intro x hx
  rw [Equiv.Perm.mem_support] at hx ⊢
  rw [h.2 x hx] at hx
  exact hx

/-- **Removing one edge from `α` keeps `α'` a sub-involution** when that edge is disjoint from
`α'`'s support.  This is the inductive step bridge. -/
lemma SubInvolution.remove_edge {α α' : Equiv.Perm D} (hα : α * α = 1)
    (h : SubInvolution α α') {a b : D} (hab : a ≠ b) (hαa : α a = b)
    (ha : a ∉ Equiv.Perm.support α') (hb : b ∉ Equiv.Perm.support α') :
    SubInvolution (α * Equiv.swap a b) α' := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  rw [Equiv.Perm.notMem_support] at ha hb
  refine ⟨h.1, ?_⟩
  intro x hx
  have hax : x ≠ a := by rintro rfl; exact hx ha
  have hbx : x ≠ b := by rintro rfl; exact hx hb
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hax hbx]
  exact h.2 x hx

/-- **Iterated monotonicity.**  Every edge-deletion sub-involution `α'` of an involution `α`
has genus slack at most that of `α`.  Proved by strong induction on the number of deleted
edges (`(support α).card`), peeling one `α`-edge disjoint from `support α'` at a time. -/
theorem genusSlack_le_of_subInvolution (σ : Equiv.Perm D) :
    ∀ α : Equiv.Perm D, α * α = 1 → ∀ α' : Equiv.Perm D, SubInvolution α α' →
      genusSlack σ α' ≤ genusSlack σ α := by
  intro α
  induction hn : (Equiv.Perm.support α).card using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    intro hα α' hsub
    classical
    -- Either `α'` already equals `α` (no edge left to delete) or there is an `α`-edge
    -- disjoint from `support α'`.
    by_cases hdone : Equiv.Perm.support α ⊆ Equiv.Perm.support α'
    · -- supports equal ⇒ `α = α'` ⇒ slacks equal.
      have hsupp_eq : Equiv.Perm.support α = Equiv.Perm.support α' :=
        le_antisymm hdone hsub.support_subset
      have heq : α = α' := by
        ext x
        by_cases hx : x ∈ Equiv.Perm.support α
        · have hx' : x ∈ Equiv.Perm.support α' := hsupp_eq ▸ hx
          rw [Equiv.Perm.mem_support] at hx'
          exact (hsub.2 x hx').symm
        · have hx' : x ∉ Equiv.Perm.support α' := hsupp_eq ▸ hx
          rw [Equiv.Perm.notMem_support] at hx hx'
          rw [hx, hx']
      rw [heq]
    · -- there is `a ∈ support α \ support α'`; let `b = α a` (also outside `support α'`).
      obtain ⟨a, ha_in, ha_out⟩ := Finset.not_subset.mp hdone
      have hane : α a ≠ a := Equiv.Perm.mem_support.mp ha_in
      set b := α a with hbdef
      have hab : a ≠ b := fun h => hane h.symm
      have hαa : α a = b := hbdef.symm
      have hαb : α b = a := by
        have happ := congrArg (fun f : Equiv.Perm D => f a) hα
        have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
        rw [hαa] at hh; exact hh
      have hb_in : b ∈ Equiv.Perm.support α := by
        rw [Equiv.Perm.mem_support, hαb]; exact hab
      -- `b` is also outside `support α'` (else `α' b = b'` would force the edge `{a,b}` into `α'`).
      have hb_out : b ∉ Equiv.Perm.support α' := by
        intro hb'
        rw [Equiv.Perm.mem_support] at hb'
        have := hsub.2 b hb'
        rw [hαb] at this
        -- `α' b = a`, so `α' a = b ≠ a` by the involution, putting `a` in `support α'`.
        have hα'a : α' a = b := by
          have happ := congrArg (fun f : Equiv.Perm D => f b) hsub.1
          have hh : α' (α' b) = b := by
            simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
          rw [this] at hh; exact hh
        exact ha_out (Equiv.Perm.mem_support.mpr (by rw [hα'a]; exact hab.symm))
      -- Delete `{a, b}` from `α`.
      set α'' := α * Equiv.swap a b with hα''def
      have hα''invol : α'' * α'' = 1 := mul_swap_involutive α hα hαa hαb
      have hsub'' : SubInvolution α'' α' :=
        hsub.remove_edge hα hab hαa ha_out hb_out
      have hsupp'' : Equiv.Perm.support α'' = (Equiv.Perm.support α) \ {a, b} :=
        support_mul_swap_of_apply α hα hab hαa
      have hcard'' : (Equiv.Perm.support α'').card < n := by
        rw [← hn, hsupp'']
        apply Finset.card_lt_card
        refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨a, ha_in, ?_⟩
        simp
      -- Recurse: slack α' ≤ slack α'' ≤ slack α.
      have hstep : genusSlack σ α'' ≤ genusSlack σ α :=
        genusSlack_remove_le σ α hα hab hαa
      have hrec : genusSlack σ α' ≤ genusSlack σ α'' :=
        ih _ hcard'' α'' rfl hα''invol α' hsub''
      exact le_trans hrec hstep



/-- **A sphere map has genus slack zero.**  For a connected map with `eulerChar = 2` and at
least one dart, `genusSlack M.σ M.α = 0` (`c = 1`, `χ = 2`). -/
theorem genusSlack_sphere_eq_zero (M : CombMap D) (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack M.σ M.α = 0 := by
  classical
  have hc : numComponents M.σ M.α = 1 :=
    numComponents_eq_one_of_connected M hsphere.1 d₀
  have hVc : (M.V : ℤ) = (numCycles M.σ : ℤ) := by rw [V_eq_numCycles]
  have hEc : (M.E : ℤ) = (Ehalf M.α : ℤ) := by rw [Ehalf_eq_E]
  have hFc : (M.F : ℤ) = (numCycles (M.σ * M.α) : ℤ) := by
    rw [F_eq_numCycles]; rfl
  have heuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hsphere.2
  unfold genusSlack
  rw [hc]
  rw [hVc, hEc, hFc] at heuler
  push_cast
  linarith



section OrbitSplit

variable (p : Equiv.Perm D) (S : Finset D)

open scoped Classical





@[simp] lemma keptToFull_mk (x : {d : D // d ∉ S}) :
    keptToFull p S (Quotient.mk (cycleSetoid (Equiv.Perm.deleteSet p S)) x)
      = Quotient.mk (cycleSetoid p) (x.1 : D) := rfl

/-- `keptToFull` is injective: two filtered orbits mapping to the same `p`-orbit are equal. -/
lemma keptToFull_injective : Function.Injective (keptToFull p S) := by
  classical
  intro a b hab
  refine Quotient.inductionOn₂ a b (fun x y hxy => ?_) hab
  simp only [keptToFull_mk] at hxy
  apply Quotient.sound
  have hsc : p.SameCycle x.1 y.1 := Quotient.exact hxy
  exact (Equiv.Perm.sameCycle_deleteSet_iff p S x y).2 hsc

/-- The image of `keptToFull` is exactly the non-deleted `p`-orbits. -/
lemma keptToFull_range_iff (q : Quotient (cycleSetoid p)) :
    (∃ a, keptToFull p S a = q) ↔ ¬ DeletedOrbit p S q := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    refine Quotient.inductionOn a (fun x => ?_)
    simp only [keptToFull_mk, DeletedOrbit, not_forall]
    exact ⟨x.1, rfl, x.2⟩
  · intro hq
    -- some dart of the orbit is kept; lift it.
    simp only [DeletedOrbit, not_forall] at hq
    obtain ⟨x, hxq, hxS⟩ := hq
    refine ⟨Quotient.mk (cycleSetoid (Equiv.Perm.deleteSet p S)) ⟨x, hxS⟩, ?_⟩
    rw [keptToFull_mk]; exact hxq



/-- **Orbit-count splitting.**  `numCycles p = numCycles (deleteSet p S) + numDeletedOrbits`.
Every `p`-orbit is either deleted or has a kept representative; the kept ones biject with the
filtered orbits via `keptToFull`. -/
theorem numCycles_eq_kept_add_deleted :
    _root_.numCycles p
      = _root_.numCycles (Equiv.Perm.deleteSet p S) + numDeletedOrbits p S := by
  classical
  -- `keptToFull` is a bijection onto the non-deleted orbits.
  have hbij : Function.Bijective
      (fun a => (⟨keptToFull p S a, by
        rw [← keptToFull_range_iff]; exact ⟨a, rfl⟩⟩ :
        {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q})) := by
    constructor
    · intro a b hab
      exact keptToFull_injective p S (Subtype.ext_iff.mp hab)
    · rintro ⟨q, hq⟩
      obtain ⟨a, ha⟩ := (keptToFull_range_iff p S q).2 hq
      exact ⟨a, Subtype.ext ha⟩
  have hcard_kept : _root_.numCycles (Equiv.Perm.deleteSet p S)
      = Fintype.card {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q} := by
    rw [← card_cycleSetoid_eq_numCycles]
    exact Fintype.card_of_bijective hbij
  have hcompl : Fintype.card {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q}
      = Fintype.card (Quotient (cycleSetoid p))
        - Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q}
      ≤ Fintype.card (Quotient (cycleSetoid p)) := Fintype.card_subtype_le _
  rw [← card_cycleSetoid_eq_numCycles p, hcard_kept, numDeletedOrbits, hcompl]
  omega

end OrbitSplit





section RawRestrict

variable (M : CombMap D) (Del : Finset D)

open scoped Classical









/-- `rawAlpha` is an involution as a permutation. -/
lemma rawAlpha_invol (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) :
    rawAlpha M Del hclosed * rawAlpha M Del hclosed = 1 := by
  ext d
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
  exact rawAlphaFun_involutive M Del hclosed d

/-- `rawAlpha` fixes deleted darts. -/
lemma rawAlpha_eq_self_of_mem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {d : D}
    (hd : d ∈ Del) : rawAlpha M Del hclosed d = d := by simp [rawAlpha_apply, hd]



/-- **Trajectory identity.**  Starting from a kept dart `x`, applying `M.α` and then iterating
`M.σ` through a run of deleted darts matches iterating `p := M.σ * rawAlpha`: for every `k`,
if the intermediate `σ`-iterates `(M.σ)^j (M.α x)` (`1 ≤ j ≤ k`) are all deleted, then
`p^(k+1) x = (M.σ)^(k+1) (M.α x)`.  (`rawAlpha` fixes the deleted darts visited.) -/
lemma rawFace_traj (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (x : {d : D // d ∉ Del}) :
    ∀ k : ℕ, (∀ j : ℕ, 1 ≤ j → j ≤ k → ((M.σ ^ j) (M.α x.1)) ∈ Del) →
      ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x.1 = (M.σ ^ (k+1)) (M.α x.1) := by
  classical
  set p := M.σ * rawAlpha M Del hclosed with hp
  intro k
  induction k with
  | zero =>
      intro _
      simp only [zero_add, pow_one, hp]
      rw [Equiv.Perm.mul_apply, rawAlpha_eq_alpha_of_notMem M Del hclosed x.2]
  | succ k ih =>
      intro hdel
      have ihk : (p ^ (k+1)) x.1 = (M.σ ^ (k+1)) (M.α x.1) :=
        ih (fun j hj1 hjk => hdel j hj1 (by omega))
      have hmemk : (M.σ ^ (k+1)) (M.α x.1) ∈ Del := hdel (k+1) (by omega) (by omega)
      have hstep : ((p ^ (k+1+1)) x.1) = p ((p ^ (k+1)) x.1) := by
        rw [pow_succ']; rfl
      rw [hstep, ihk, hp, Equiv.Perm.mul_apply,
        rawAlpha_eq_self_of_mem M Del hclosed hmemk, ← Equiv.Perm.mul_apply, ← pow_succ']







/-- **The kept face permutation equals the deleted raw face permutation.**  As permutations on
the kept subtype, `keptFacePerm = deleteSet (M.σ * rawAlpha) Del`.  Both send a kept dart `x`
to the first kept dart reached from `M.α x` by iterating `M.σ` through the deleted run; the raw
face permutation `M.σ * rawAlpha` walks the same trajectory because `rawAlpha` fixes the deleted
darts it passes through. -/
theorem keptFacePerm_eq_deleteSet_rawFace (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    keptFacePerm M Del hclosed hsub = Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del := by
  classical
  ext x
  -- It suffices to prove the underlying dart values agree.
  set y : {d : D // d ∉ Del} := ⟨M.α x.1, fun hc => x.2 ((hsub x.1).2 hc)⟩ with hy
  -- LHS value: `(deleteSet M.σ Del) y = (M.σ)^m (M.α x)` with `m = firstOutside M.σ Del y`.
  set m := Equiv.Perm.DeleteSet.firstOutside M.σ Del y with hm
  have hmpos : 0 < m := Equiv.Perm.DeleteSet.firstOutside_pos M.σ Del y
  have hlhs : ((keptFacePerm M Del hclosed hsub) x : {d : D // d ∉ Del}).1
      = (M.σ ^ m) (M.α x.1) := by
    show ((Equiv.Perm.deleteSet M.σ Del) y : {d : D // d ∉ Del}).1 = _
    rw [Equiv.Perm.deleteSet_apply_coe]
  -- intermediate σ-iterates of `M.α x` (before step `m`) are deleted (firstOutside min).
  have hinter : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → ((M.σ ^ j) (M.α x.1)) ∈ Del := by
    intro j hj1 hjm
    by_contra hnot
    exact Equiv.Perm.DeleteSet.firstOutside_min M.σ Del y (by omega : j < m)
      ⟨by omega, by show (M.σ ^ j) y.1 ∉ Del; rw [hy]; exact hnot⟩
  -- the `m`-th σ-iterate is kept.
  have hmkept : (M.σ ^ m) (M.α x.1) ∉ Del := by
    have := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ Del y
    rwa [hy] at this
  -- trajectory: `(M.σ * rawAlpha)^m x = (M.σ)^m (M.α x)`.
  have htraj := rawFace_traj M Del hclosed x (m - 1) hinter
  have hmsucc : (m - 1) + 1 = m := by omega
  rw [hmsucc] at htraj
  -- RHS value: `deleteSet (M.σ*rawAlpha) Del x = (M.σ*rawAlpha)^M x`, `M = firstOutside …`.
  set P := M.σ * rawAlpha M Del hclosed with hP
  have hrhs : ((Equiv.Perm.deleteSet P Del) x : {d : D // d ∉ Del}).1
      = (P ^ (Equiv.Perm.DeleteSet.firstOutside P Del x)) x.1 :=
    Equiv.Perm.deleteSet_apply_coe P Del x
  -- The firstOutside of `P` at `x` is exactly `m`: the `P`-trajectory equals the σ-trajectory
  -- of `M.α x`, deleted before step `m`, kept at step `m`.
  have hPtraj : ∀ j : ℕ, 1 ≤ j → j ≤ m → (P ^ j) x.1 = (M.σ ^ j) (M.α x.1) := by
    intro j hj1 hjm
    have hjsub : ∀ i : ℕ, 1 ≤ i → i ≤ j - 1 → ((M.σ ^ i) (M.α x.1)) ∈ Del :=
      fun i hi1 hij => hinter i hi1 (by omega)
    have := rawFace_traj M Del hclosed x (j - 1) hjsub
    rwa [Nat.sub_add_cancel hj1] at this
  have hPm_kept : (P ^ m) x.1 ∉ Del := by rw [hPtraj m hmpos le_rfl]; exact hmkept
  have hPm_min : ∀ i : ℕ, i < m → ¬ (0 < i ∧ (P ^ i) x.1 ∉ Del) := by
    intro i him ⟨hipos, hinotmem⟩
    rw [hPtraj i hipos (by omega)] at hinotmem
    exact hinotmem (hinter i hipos (by omega))
  have hMeq : Equiv.Perm.DeleteSet.firstOutside P Del x = m := by
    apply le_antisymm
    · exact Nat.find_min' _ ⟨hmpos, hPm_kept⟩
    · by_contra hlt
      rw [not_le] at hlt
      exact hPm_min _ hlt
        ⟨Equiv.Perm.DeleteSet.firstOutside_pos P Del x,
         Equiv.Perm.DeleteSet.firstOutside_notMem P Del x⟩
  rw [hlhs, hrhs, hMeq, hPtraj m hmpos le_rfl]





/-- The face count of the kept map equals `numCycles (deleteSet (M.σ * rawAlpha) Del)`. -/
lemma numCycles_keptFacePerm_eq (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    _root_.numCycles (keptFacePerm M Del hclosed hsub)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del) := by
  rw [keptFacePerm_eq_deleteSet_rawFace M Del hclosed hsub]



/-- On the deleted set, `M.σ` and `M.σ * rawAlpha` agree, hence have the same `SameCycle`
relation among deleted darts; combined with the kept-orbit splitting this forces the deleted
orbit counts to be equal. -/
lemma sameCycle_sigma_rawFace_of_mem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    {x : D} (hx : x ∈ Del) :
    (M.σ * rawAlpha M Del hclosed) x = M.σ x := by
  rw [Equiv.Perm.mul_apply, rawAlpha_eq_self_of_mem M Del hclosed hx]



variable (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
  (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)

open scoped Classical















/-- The raw dart-step relation is symmetric (`rawAlpha` is an involution). -/
lemma rawStepRel_symm {a b : D}
    (h : dartStepRel M.σ (rawAlpha M Del hclosed) a b) :
    dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
  dartStepRel_symm (rawAlpha_invol M Del hclosed) h

/-- **Descent witness (forward walk).**  Every dart `z` raw-reachable from a kept dart `x`
(via `ReflTransGen`) is `M.σ`-`SameCycle` to a kept dart `w` in the same *kept* component as
`x`.  The only raw steps that can land in `Del` are `M.σ`-`SameCycle` steps; `M.σ`-`SameCycle`
is transitive, so deleted intermediates collapse, and the `rawAlpha`-edge from a kept dart lands
kept (`α`-closure), giving a genuine kept dart-step. -/
lemma raw_reach_kept_witness {x : {d : D // d ∉ Del}} {z : D}
    (h : Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 z) :
    ∃ w : {d : D // d ∉ Del},
      Relation.ReflTransGen (keptStepRel M Del hsub) x w ∧ M.σ.SameCycle w.1 z := by
  classical
  induction h with
  | refl => exact ⟨x, Relation.ReflTransGen.refl, Equiv.Perm.SameCycle.rfl⟩
  | @tail b c hxb hbc ih =>
      obtain ⟨w, hwkept, hwb⟩ := ih
      -- one more raw step `b → c`; combine with `w ~σ b`.
      rcases hbc with hσ | hαe
      · -- `c` in same `M.σ`-cycle as `b`, hence as `w`.
        exact ⟨w, hwkept, hwb.trans hσ⟩
      · -- `c = rawAlpha b`.
        by_cases hbDel : b ∈ Del
        · -- `rawAlpha b = b`, so `c = b`; nothing changes.
          rw [rawAlpha_eq_self_of_mem M Del hclosed hbDel] at hαe
          exact ⟨w, hwkept, hαe ▸ hwb⟩
        · -- `b` kept, `c = M.α b` kept (α-closure); `w ~σ b` gives a kept σ-step `w → ⟨b⟩`,
          -- then the kept α-edge `⟨b⟩ → ⟨c⟩`.
          have hck : c ∉ Del := by
            rw [rawAlpha_eq_alpha_of_notMem M Del hclosed hbDel] at hαe
            rw [hαe]; intro hc; exact hbDel ((hsub b).2 hc)
          have hbw : M.σ.SameCycle w.1 b := hwb
          -- kept σ-step `w → ⟨b, hbDel⟩`:
          have hstep1 : keptStepRel M Del hsub w ⟨b, hbDel⟩ :=
            Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del w ⟨b, hbDel⟩).2 hbw)
          -- kept α-edge `⟨b⟩ → ⟨c⟩`:
          have hstep2 : keptStepRel M Del hsub ⟨b, hbDel⟩ ⟨c, hck⟩ := by
            refine Or.inr (Subtype.ext ?_)
            show c = M.α b
            rw [rawAlpha_eq_alpha_of_notMem M Del hclosed hbDel] at hαe
            exact hαe
          exact ⟨⟨c, hck⟩, (hwkept.tail hstep1).tail hstep2, Equiv.Perm.SameCycle.rfl⟩

/-- **Descent.**  Two kept darts that are raw-`EqvGen` are kept-`EqvGen`.  (From the descent
witness: the witness `w` for `y` is `M.σ`-`SameCycle` to `y`, both kept, hence kept-connected
by a single kept `σ`-step.) -/
lemma raw_eqvGen_descends {x y : {d : D // d ∉ Del}}
    (h : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1) :
    Relation.EqvGen (keptStepRel M Del hsub) x y := by
  classical
  -- pass to `ReflTransGen` (symmetric relation), apply the witness, close with a kept σ-step.
  have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
      dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
    fun a b => rawStepRel_symm M Del hclosed
  rw [eqvGen_iff_reflTransGen hsymm] at h
  obtain ⟨w, hwkept, hwy⟩ := raw_reach_kept_witness M Del hclosed hsub h
  -- `w ~σ y` (both kept) ⇒ kept σ-step `w → y`.
  have hstep : keptStepRel M Del hsub w y :=
    Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del w y).2 hwy)
  have hksymm : ∀ a b, keptStepRel M Del hsub a b → keptStepRel M Del hsub b a :=
    fun a b h => dartStepRel_symm (keptAlpha_invol M Del hsub) h
  rw [eqvGen_iff_reflTransGen hksymm]
  exact hwkept.tail hstep



/-- `keptCompToRaw` is injective: by the descent lemma, kept darts raw-`EqvGen` are
kept-`EqvGen`. -/
lemma keptCompToRaw_injective : Function.Injective (keptCompToRaw M Del hclosed hsub) := by
  classical
  intro a b hab
  refine Quotient.inductionOn₂ a b (fun x y hxy => ?_) hab
  apply Quotient.sound
  show Relation.EqvGen (keptStepRel M Del hsub) x y
  exact raw_eqvGen_descends M Del hclosed hsub (Quotient.exact hxy)







/-- The image of `keptCompToRaw` is exactly the non-deleted raw components. -/
lemma keptCompToRaw_range_iff
    (q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :
    (∃ a, keptCompToRaw M Del hclosed hsub a = q) ↔ ¬ DeletedComp M Del hclosed q := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    refine Quotient.inductionOn a (fun x => ?_)
    simp only [DeletedComp, not_forall]
    exact ⟨x.1, rfl, x.2⟩
  · intro hq
    simp only [DeletedComp, not_forall] at hq
    obtain ⟨x, hxq, hxD⟩ := hq
    exact ⟨Quotient.mk _ ⟨x, hxD⟩, hxq⟩



/-- **Component split.**  `numComponents M.σ rawAlpha = numComp (keptStepRel) + numDeletedComp`. -/
theorem numComponents_raw_split :
    numComponents M.σ (rawAlpha M Del hclosed)
      = _root_.numComp (keptStepRel M Del hsub) + numDeletedComp M Del hclosed := by
  classical
  rw [numComponents_def]
  have hbij : Function.Bijective
      (fun a => (⟨keptCompToRaw M Del hclosed hsub a, by
        rw [← keptCompToRaw_range_iff M Del hclosed hsub]; exact ⟨a, rfl⟩⟩ :
        {q // ¬ DeletedComp M Del hclosed q})) := by
    constructor
    · intro a b hab
      exact keptCompToRaw_injective M Del hclosed hsub (Subtype.ext_iff.mp hab)
    · rintro ⟨q, hq⟩
      obtain ⟨a, ha⟩ := (keptCompToRaw_range_iff M Del hclosed hsub q).2 hq
      exact ⟨a, Subtype.ext ha⟩
  have hcard_kept : _root_.numComp (keptStepRel M Del hsub)
      = Fintype.card {q // ¬ DeletedComp M Del hclosed q} := by
    unfold _root_.numComp
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_bijective hbij
  have hcompl : Fintype.card {q // ¬ DeletedComp M Del hclosed q}
      = Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))))
        - Fintype.card {q // DeletedComp M Del hclosed q} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {q // DeletedComp M Del hclosed q}
      ≤ Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :=
    Fintype.card_subtype_le _
  have hraw : _root_.numComp (dartStepRel M.σ (rawAlpha M Del hclosed))
      = Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) := by
    unfold _root_.numComp; rw [Nat.card_eq_fintype_card]
  rw [hraw, hcard_kept, numDeletedComp, hcompl]
  omega



/-- **A deleted-component dart has its whole `M.σ`-orbit deleted.**  If every dart in `x`'s
`dartStepRel`-component lies in `Del`, then in particular `M.σ x` lies in `Del` (it is a
`dartStepRel`-step away), and inductively the whole `M.σ`-orbit of `x` is deleted. -/
lemma sigma_sameCycle_imp_eqvGen_dartStepRel {a b : D} (h : M.σ.SameCycle a b) :
    Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) a b :=
  Relation.EqvGen.rel _ _ (Or.inl h)

/-- On `Del`, a `dartStepRel`-step keeps you in the same `M.σ`-orbit (the `rawAlpha`-edge fixes
deleted darts).  Hence within a deleted component the relation collapses to `M.σ.SameCycle`. -/
lemma dartStepRel_of_mem_del {a b : D} (ha : a ∈ Del)
    (h : dartStepRel M.σ (rawAlpha M Del hclosed) a b) : M.σ.SameCycle a b := by
  rcases h with hσ | hαe
  · exact hσ
  · rw [rawAlpha_eq_self_of_mem M Del hclosed ha] at hαe
    exact hαe ▸ Equiv.Perm.SameCycle.rfl

/-- **DeletedComp ⟺ DeletedOrbit (`M.σ`).**  The `dartStepRel`-class of a dart is entirely
deleted iff its `M.σ`-orbit is entirely deleted.  (`⟸`: a deleted `M.σ`-orbit admits no
`rawAlpha`-edge leaving `Del`, so the component stays in `Del`; `⟹`: `M.σ.SameCycle` is a
`dartStepRel`-step, so a deleted component contains the whole `M.σ`-orbit.) -/
lemma deletedComp_iff_deletedOrbit (x : D) :
    DeletedComp M Del hclosed (Quotient.mk _ x)
      ↔ DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x) := by
  classical
  constructor
  · -- DeletedComp ⇒ DeletedOrbit: any `M.σ`-cycle dart is `dartStepRel`-related, hence deleted.
    intro hC y hy
    apply hC y
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) y x
    have hsc : M.σ.SameCycle y x := Quotient.exact hy
    exact sigma_sameCycle_imp_eqvGen_dartStepRel M Del hclosed hsc
  · -- DeletedOrbit ⇒ DeletedComp: every `dartStepRel`-related dart stays in the deleted σ-orbit.
    intro hO y hy
    have hxy : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x y :=
      (Quotient.exact hy).symm
    have hxDel : x ∈ Del := hO x rfl
    -- pass to ReflTransGen and carry the invariant `M.σ.SameCycle x z ∧ z ∈ Del` forward.
    have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
        dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
      fun a b => rawStepRel_symm M Del hclosed
    rw [eqvGen_iff_reflTransGen hsymm] at hxy
    have hinv : ∀ z, Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z →
        M.σ.SameCycle x z ∧ z ∈ Del := by
      intro z hz
      induction hz with
      | refl => exact ⟨Equiv.Perm.SameCycle.rfl, hxDel⟩
      | @tail b c hxb hbc ih =>
          obtain ⟨hxb_sc, hbDel⟩ := ih
          have hbc_sc : M.σ.SameCycle b c := dartStepRel_of_mem_del M Del hclosed hbDel hbc
          have hxc_sc : M.σ.SameCycle x c := hxb_sc.trans hbc_sc
          refine ⟨hxc_sc, ?_⟩
          -- `c` is in `x`'s σ-orbit, which is deleted.
          exact hO c (Quotient.sound hxc_sc.symm)
    exact (hinv y hxy).2

/-- Within a deleted component, `dartStepRel`-`EqvGen` collapses to `M.σ.SameCycle`. -/
lemma comp_eqvGen_imp_sigma_of_deleted {x y : D} (hxDel : x ∈ Del)
    (hdel : ∀ z, Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z → z ∈ Del)
    (h : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x y) :
    M.σ.SameCycle x y := by
  classical
  have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
      dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
    fun a b => rawStepRel_symm M Del hclosed
  rw [eqvGen_iff_reflTransGen hsymm] at h
  have hinv : ∀ z, Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z →
      M.σ.SameCycle x z := by
    intro z hz
    induction hz with
    | refl => exact Equiv.Perm.SameCycle.rfl
    | @tail b c hxb hbc ih =>
        have hbDel : b ∈ Del :=
          hdel b ((eqvGen_iff_reflTransGen hsymm x b).2 hxb)
        exact ih.trans (dartStepRel_of_mem_del M Del hclosed hbDel hbc)
  exact hinv y h

/-- A deleted `dartStepRel`-class's representative `out` is deleted, and its whole component is
deleted (every dart `EqvGen`-related to it). -/
lemma deletedComp_out_props
    {q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))}
    (hq : DeletedComp M Del hclosed q) :
    q.out ∈ Del ∧ ∀ z, Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) q.out z →
      z ∈ Del := by
  classical
  have hout : q.out ∈ Del := hq q.out (Quotient.out_eq q)
  refine ⟨hout, fun z hz => ?_⟩
  apply hq z
  rw [← Quotient.out_eq q]
  exact Quotient.sound (Relation.EqvGen.symm _ _ hz)

/-- **`numDeletedComp = numDeletedOrbits M.σ Del`.**  Both count the same family of deleted
`M.σ`-orbits; the equiv sends a deleted component to the `M.σ`-orbit of its representative and
back, well-defined by the within-deleted collapse `comp_eqvGen_imp_sigma_of_deleted`. -/
theorem numDeletedComp_eq_numDeletedOrbits :
    numDeletedComp M Del hclosed = numDeletedOrbits M.σ Del := by
  classical
  unfold numDeletedComp numDeletedOrbits
  refine Fintype.card_congr ?_
  refine
    { toFun := fun q => ⟨Quotient.mk (cycleSetoid M.σ) q.1.out,
        (deletedComp_iff_deletedOrbit M Del hclosed q.1.out).1 (by
          intro z hz
          obtain ⟨hout, hcomp⟩ := deletedComp_out_props M Del hclosed q.2
          exact q.2 z (by rw [hz]; exact Quotient.out_eq q.1))⟩,
      invFun := fun o => ⟨Quotient.mk _ o.1.out,
        (deletedComp_iff_deletedOrbit M Del hclosed o.1.out).2 (by
          intro z hz
          exact o.2 z (by rw [hz]; exact Quotient.out_eq o.1))⟩,
      left_inv := ?_, right_inv := ?_ }
  · -- `[ [qc].out ]_σ` then `[ · ]_comp` returns `qc`.
    rintro ⟨qc, hqc⟩
    apply Subtype.ext
    dsimp only
    obtain ⟨hout, hcomp⟩ := deletedComp_out_props M Del hclosed hqc
    -- the σ-orbit of `qc.out`'s out is σ-SameCycle to `qc.out`, hence same comp-class.
    nth_rewrite 2 [← Quotient.out_eq qc]
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) _ qc.out
    have hsc : M.σ.SameCycle (Quotient.mk (cycleSetoid M.σ) qc.out).out qc.out := by
      have := Quotient.out_eq (Quotient.mk (cycleSetoid M.σ) qc.out)
      exact Quotient.exact this
    exact sigma_sameCycle_imp_eqvGen_dartStepRel M Del hclosed hsc
  · -- `[ [o].out ]_comp` then `[ · ]_σ` returns `o`.
    rintro ⟨o, ho⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq o]
    apply Quotient.sound
    show M.σ.SameCycle _ o.out
    -- the comp-class of `o.out` is deleted; its out is σ-SameCycle to `o.out` by the collapse.
    have hodel : o.out ∈ Del := ho o.out (Quotient.out_eq o)
    -- `o`'s σ-orbit is deleted ⇒ `o.out`'s comp-class is deleted (`deletedComp_iff_deletedOrbit`).
    have hDOrbit : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) o.out) := by
      intro z hz
      exact ho z (by rw [hz]; exact Quotient.out_eq o)
    have hDComp : DeletedComp M Del hclosed
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out) :=
      (deletedComp_iff_deletedOrbit M Del hclosed o.out).2 hDOrbit
    obtain ⟨_, hcompdel⟩ := deletedComp_out_props M Del hclosed hDComp
    have hsc : M.σ.SameCycle
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out).out
        o.out := by
      apply comp_eqvGen_imp_sigma_of_deleted M Del hclosed
        (hcompdel _ (Relation.EqvGen.refl _)) hcompdel
      have := Quotient.out_eq
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out)
      exact Quotient.exact this
    exact hsc







/-- **`DeletedOrbit`s coincide** for `M.σ` and `M.σ * rawAlpha`. -/
lemma deletedOrbit_sigmaRaw_iff (x : D) :
    DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) x)
      ↔ DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x) := by
  classical
  -- Trajectory: if `x`'s `σRaw`-orbit is deleted then `σ^k x = σRaw^k x ∈ Del` for all `k`,
  -- and symmetrically; this collapses each orbit-deletion predicate to the other.
  have key : ∀ (p q : Equiv.Perm D),
      (∀ d : D, d ∈ Del → p d = q d) →
      ∀ (hpx : DeletedOrbit p Del (Quotient.mk (cycleSetoid p) x)),
      ∀ k : ℕ, (p ^ k) x = (q ^ k) x ∧ (q ^ k) x ∈ Del := by
    intro p q hpq hpx k
    have hxDel : x ∈ Del := hpx x rfl
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hqk_del : (q ^ k) x ∈ Del := ihDel
        have hpk_del : (p ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : (p ^ (k+1)) x = (q ^ (k+1)) x := by
          rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ihEq,
            hpq _ hqk_del]
        refine ⟨heq, ?_⟩
        -- `q^(k+1) x = p^(k+1) x` is in `x`'s `p`-orbit, hence deleted by `hpx`.
        apply hpx
        apply Quotient.sound
        show p.SameCycle ((q ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  constructor
  · intro hP y hy
    have hsc : M.σ.SameCycle y x := Quotient.exact hy
    have hagree : ∀ d : D, d ∈ Del → (M.σ * rawAlpha M Del hclosed) d = M.σ d :=
      fun d hd => sameCycle_sigma_rawFace_of_mem M Del hclosed hd
    -- `y` is in `x`'s σ-orbit; show deleted via the trajectory of `M.σ` matching `σRaw`.
    obtain ⟨n, hn⟩ := hsc.symm.exists_nat_pow_eq  -- `σ^n x = y`
    have := key (M.σ * rawAlpha M Del hclosed) M.σ hagree hP n
    rw [hn] at this
    exact this.2
  · intro hO y hy
    have hsc : (M.σ * rawAlpha M Del hclosed).SameCycle y x := Quotient.exact hy
    have hagree : ∀ d : D, d ∈ Del → M.σ d = (M.σ * rawAlpha M Del hclosed) d :=
      fun d hd => (sameCycle_sigma_rawFace_of_mem M Del hclosed hd).symm
    obtain ⟨n, hn⟩ := hsc.symm.exists_nat_pow_eq  -- `σRaw^n x = y`
    have := key M.σ (M.σ * rawAlpha M Del hclosed) hagree hO n
    rw [hn] at this
    exact this.2

/-- A `σ`-`SameCycle` within a deleted `σRaw`-orbit is a `σRaw`-`SameCycle` (and conversely),
since the two rotations agree on `Del` and the orbit stays in `Del`. -/
lemma sigmaRaw_sameCycle_iff_sigma_of_deletedOrbit {x : D}
    (hP : DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
      (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) x)) {y : D}
    (h : M.σ.SameCycle x y) : (M.σ * rawAlpha M Del hclosed).SameCycle x y := by
  classical
  have hxDel : x ∈ Del := hP x rfl
  -- trajectory: `σ^k x = σRaw^k x ∈ Del`.
  have key : ∀ k : ℕ, ((M.σ * rawAlpha M Del hclosed) ^ k) x = (M.σ ^ k) x
      ∧ (M.σ ^ k) x ∈ Del := by
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hraw_del : ((M.σ * rawAlpha M Del hclosed) ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x = (M.σ ^ (k+1)) x := by
          have e1 : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x
              = M.σ (((M.σ * rawAlpha M Del hclosed) ^ k) x) := by
            rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
              rawAlpha_eq_self_of_mem M Del hclosed hraw_del]
          have e2 : (M.σ ^ (k+1)) x = M.σ ((M.σ ^ k) x) := by rw [pow_succ']; rfl
          rw [e1, e2, ihEq]
        refine ⟨heq, ?_⟩
        apply hP
        apply Quotient.sound
        show (M.σ * rawAlpha M Del hclosed).SameCycle ((M.σ ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, (key n).1, hn]⟩

/-- The converse: a `σRaw`-`SameCycle` within a deleted `σ`-orbit is a `σ`-`SameCycle`. -/
lemma sigma_sameCycle_iff_sigmaRaw_of_deletedOrbit {x : D}
    (hO : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x)) {y : D}
    (h : (M.σ * rawAlpha M Del hclosed).SameCycle x y) : M.σ.SameCycle x y := by
  classical
  have hxDel : x ∈ Del := hO x rfl
  have key : ∀ k : ℕ, (M.σ ^ k) x = ((M.σ * rawAlpha M Del hclosed) ^ k) x
      ∧ ((M.σ * rawAlpha M Del hclosed) ^ k) x ∈ Del := by
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hσ_del : (M.σ ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : (M.σ ^ (k+1)) x = ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x := by
          have e1 : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x
              = M.σ (((M.σ * rawAlpha M Del hclosed) ^ k) x) := by
            rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
              rawAlpha_eq_self_of_mem M Del hclosed ihDel]
          have e2 : (M.σ ^ (k+1)) x = M.σ ((M.σ ^ k) x) := by rw [pow_succ']; rfl
          rw [e1, e2, ihEq]
        refine ⟨heq, ?_⟩
        apply hO
        apply Quotient.sound
        show M.σ.SameCycle (((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, (key n).1, hn]⟩

/-- **`numDeletedOrbits (M.σ * rawAlpha) Del = numDeletedOrbits M.σ Del`.** -/
theorem numDeletedOrbits_sigmaRaw_eq :
    numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del = numDeletedOrbits M.σ Del := by
  classical
  unfold numDeletedOrbits
  refine Fintype.card_congr ?_
  refine
    { toFun := fun q => ⟨Quotient.mk (cycleSetoid M.σ) q.1.out,
        (deletedOrbit_sigmaRaw_iff M Del hclosed q.1.out).1 (by
          intro z hz; exact q.2 z (by rw [hz]; exact Quotient.out_eq q.1))⟩,
      invFun := fun o => ⟨Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.1.out,
        (deletedOrbit_sigmaRaw_iff M Del hclosed o.1.out).2 (by
          intro z hz; exact o.2 z (by rw [hz]; exact Quotient.out_eq o.1))⟩,
      left_inv := ?_, right_inv := ?_ }
  · rintro ⟨q, hq⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq q]
    apply Quotient.sound
    show (M.σ * rawAlpha M Del hclosed).SameCycle
      (Quotient.mk (cycleSetoid M.σ) q.out).out q.out
    -- `(mk_σ q.out).out` is `σ`-SameCycle to `q.out`; convert to `σRaw` via deletedness.
    have hsc : M.σ.SameCycle (Quotient.mk (cycleSetoid M.σ) q.out).out q.out :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (cycleSetoid M.σ) q.out))
    -- `q.out`'s `σRaw`-orbit is deleted (q is a deleted `σRaw`-class).
    have hqDel : DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) q.out) := by
      intro z hz; exact hq z (by rw [hz]; exact Quotient.out_eq q)
    exact (sigmaRaw_sameCycle_iff_sigma_of_deletedOrbit M Del hclosed hqDel hsc.symm).symm
  · rintro ⟨o, ho⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq o]
    apply Quotient.sound
    show M.σ.SameCycle (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out).out o.out
    have hsc : (M.σ * rawAlpha M Del hclosed).SameCycle
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out).out o.out :=
      Quotient.exact (Quotient.out_eq
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out))
    -- `o.out`'s `σ`-orbit is deleted (o is a deleted `σ`-class); convert via the converse lemma.
    have hoDel : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) o.out) := by
      intro z hz; exact ho z (by rw [hz]; exact Quotient.out_eq o)
    exact (sigma_sameCycle_iff_sigmaRaw_of_deletedOrbit M Del hclosed hoDel hsc.symm).symm



/-- `rawAlpha` is an edge-deletion sub-involution of `M.α`. -/
lemma rawAlpha_subInvolution : SubInvolution M.α (rawAlpha M Del hclosed) := by
  refine ⟨rawAlpha_invol M Del hclosed, fun x hx => ?_⟩
  -- where `rawAlpha` moves `x`, it equals `M.α x` (so `x ∉ Del`).
  by_cases hxD : x ∈ Del
  · exact absurd (rawAlpha_eq_self_of_mem M Del hclosed hxD) hx
  · exact rawAlpha_eq_alpha_of_notMem M Del hclosed hxD

/-- **The raw slack of a genus-0 `M` after deleting `Del` is zero** (`d₀` a witness dart). -/
theorem genusSlack_rawAlpha_eq_zero (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack M.σ (rawAlpha M Del hclosed) = 0 := by
  have hle : genusSlack M.σ (rawAlpha M Del hclosed) ≤ genusSlack M.σ M.α :=
    genusSlack_le_of_subInvolution M.σ M.α M.α_invol _ (rawAlpha_subInvolution M Del hclosed)
  have hM0 : genusSlack M.σ M.α = 0 := genusSlack_sphere_eq_zero M hsphere d₀
  have hge : 0 ≤ genusSlack M.σ (rawAlpha M Del hclosed) :=
    genusSlack_nonneg M.σ _ (rawAlpha_invol M Del hclosed)
  rw [hM0] at hle
  exact le_antisymm hle hge

/-- The kept edge involution has the same number of edges (transpositions) as `rawAlpha`:
both have support exactly the kept darts. -/
lemma Ehalf_keptAlpha_eq_rawAlpha :
    Ehalf (keptAlpha M Del hsub) = Ehalf (rawAlpha M Del hclosed) := by
  classical
  -- `2 * Ehalf = card support`.  `keptAlpha` is fixed-point-free on the kept subtype, so its
  -- support is all kept darts; `rawAlpha`'s support is exactly the kept darts of `D`.
  have hk : (keptAlpha M Del hsub) ∈ Set.univ := ⟨⟩
  -- `keptAlpha` fixed-point-free:
  have hkff : ∀ d, keptAlpha M Del hsub d ≠ d := by
    intro d hd
    apply M.α_no_fixed d.1
    have := congrArg Subtype.val hd
    rwa [keptAlpha_apply_coe] at this
  have hksupp : Equiv.Perm.support (keptAlpha M Del hsub) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]; intro d; rw [Equiv.Perm.mem_support]; exact hkff d
  -- `rawAlpha` support = kept darts (its complement is `Del`).
  have hrsupp : Equiv.Perm.support (rawAlpha M Del hclosed) = Finset.univ.filter (· ∉ Del) := by
    ext d
    simp only [Equiv.Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rawAlpha_apply]
    by_cases hd : d ∈ Del
    · simp [hd]
    · simp only [hd, if_false, not_false_iff, iff_true]
      exact fun hc => M.α_no_fixed d hc
  unfold Ehalf
  rw [hksupp, hrsupp, Finset.card_univ]
  -- both cardinalities are `|kept darts|`.
  have : (Finset.univ.filter (· ∉ Del) : Finset D).card
      = Fintype.card {d : D // d ∉ Del} := by
    rw [Fintype.card_subtype]
  rw [this]

/-- **The kept combinatorial map's genus slack is zero** on a genus-0 `M`.  This is the
structural genus-0 certificate: the kept side (an edge-deletion sub-map of the sphere `M`) has
genus slack `0`, hence — when connected — Euler characteristic `2` (no handle). -/
theorem keptMap_genusSlack_eq_zero (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) = 0 := by
  classical
  have hraw0 : genusSlack M.σ (rawAlpha M Del hclosed) = 0 :=
    genusSlack_rawAlpha_eq_zero M Del hclosed hsphere d₀
  -- expand both slacks via the count bridges.
  unfold genusSlack at hraw0 ⊢
  -- raw: `2c_raw - numCycles σ + Ehalf rawAlpha - numCycles (σ rawAlpha)`.
  -- kept: `2c_kept - numCycles(deleteSet σ) + Ehalf keptAlpha - numCycles(keptFacePerm)`.
  -- bridges:
  have hcsplit : numComponents M.σ (rawAlpha M Del hclosed)
      = _root_.numComp (keptStepRel M Del hsub) + numDeletedComp M Del hclosed :=
    numComponents_raw_split M Del hclosed hsub
  have hkeptStep_eq : _root_.numComp (keptStepRel M Del hsub)
      = numComponents (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) := by
    rw [numComponents_def]; rfl
  have hDC : numDeletedComp M Del hclosed = numDeletedOrbits M.σ Del :=
    numDeletedComp_eq_numDeletedOrbits M Del hclosed
  have hVsplit : _root_.numCycles M.σ
      = _root_.numCycles (Equiv.Perm.deleteSet M.σ Del) + numDeletedOrbits M.σ Del :=
    numCycles_eq_kept_add_deleted M.σ Del
  have hFsplit : _root_.numCycles (M.σ * rawAlpha M Del hclosed)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del)
        + numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del :=
    numCycles_eq_kept_add_deleted (M.σ * rawAlpha M Del hclosed) Del
  have hFbridge : _root_.numCycles (keptFacePerm M Del hclosed hsub)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del) :=
    numCycles_keptFacePerm_eq M Del hclosed hsub
  have hDF : numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del = numDeletedOrbits M.σ Del :=
    numDeletedOrbits_sigmaRaw_eq M Del hclosed
  have hEh : Ehalf (keptAlpha M Del hsub) = Ehalf (rawAlpha M Del hclosed) :=
    Ehalf_keptAlpha_eq_rawAlpha M Del hclosed hsub
  -- the kept face permutation is the σα of the kept CombMap.
  have hkeptFace : (Equiv.Perm.deleteSet M.σ Del) * (keptAlpha M Del hsub)
      = keptFacePerm M Del hclosed hsub := rfl
  -- assemble: rewrite `hraw0` (raw slack = 0) into kept quantities.
  rw [hkeptStep_eq] at hcsplit
  rw [hcsplit, hVsplit, ← hEh, hFsplit, hDF, hDC] at hraw0
  -- hraw0 now: `2(c_kept + DV) - (V_kept + DV) + Ehalf keptAlpha
  --   - (numCycles(deleteSet(σ*rawAlpha)) + DV) = 0`.
  -- goal: `2 c_kept - V_kept + Ehalf keptAlpha - numCycles(keptFacePerm) = 0`.
  rw [hkeptFace, hFbridge]
  push_cast at hraw0 ⊢
  linarith

/-- **The kept combinatorial map of a chord-split side of a genus-0 `M` is a disk
(no handle).**  Given a `CombMap K` whose rotation is `deleteSet M.σ Del` and whose edge
involution is `keptAlpha`, if it is connected and has a dart, then its Euler characteristic is
exactly `2`.  This is the reverse inequality `2 ≤ eulerChar` (in fact equality), supplied by the
structural genus monotonicity — the genus-0 certificate that the chord side has no handle. -/
theorem keptMap_eulerChar_eq_two (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap)
    (K : CombMap {d : D // d ∉ Del})
    (hKσ : K.σ = Equiv.Perm.deleteSet M.σ Del) (hKα : K.α = keptAlpha M Del hsub)
    (d : {d : D // d ∉ Del}) (hconn : K.Connected) :
    K.eulerChar = 2 := by
  classical
  have hslack0 : genusSlack (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) = 0 :=
    keptMap_genusSlack_eq_zero M Del hsub hclosed hsphere d.1
  have hc : numComponents K.σ K.α = 1 :=
    numComponents_eq_one_of_connected K hconn d
  have hVc : (K.V : ℤ) = (_root_.numCycles K.σ : ℤ) := by rw [V_eq_numCycles]
  have hEc : (K.E : ℤ) = (Ehalf K.α : ℤ) := by rw [Ehalf_eq_E]
  have hFc : (K.F : ℤ) = (_root_.numCycles (K.σ * K.α) : ℤ) := by rw [F_eq_numCycles]; rfl
  have hslack : genusSlack K.σ K.α = 0 := by rw [hKσ, hKα]; exact hslack0
  unfold genusSlack at hslack
  rw [hc] at hslack
  unfold CombMap.eulerChar
  rw [hVc, hEc, hFc]
  push_cast at hslack ⊢
  linarith

end RawRestrict



section ChordThreading

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation

open ProofsInTheBook.ChordSideRecon















end ChordThreading

end ProofsInTheBook.SubmapPlanar

















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

/-- `flipAux first prev xs` is the sum of the unequal-indicators over the consecutive pairs of
`prev :: xs` read cyclically with wrap target `first`: namely `zipWith` of `prev :: xs` with
`xs ++ [first]`. -/
theorem flipAux_eq_zipWith (first : α) :
    ∀ (prev : α) (xs : List α),
      flipAux first prev xs
        = (List.zipWith (fun a b => if a ≠ b then 1 else 0) (prev :: xs) (xs ++ [first])).sum
  | _, [] => by simp [flipAux]
  | prev, x :: xs => by
      simp only [flipAux, List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [flipAux_eq_zipWith first x xs]

/-- **Layer 1 (list bridge).**  The cyclic flip count of a list is the sum of unequal-indicators
over cyclically-consecutive pairs, where the cyclic successor list is `l.rotate 1`. -/
theorem cyclicFlipCount_eq_zipWith_rotate (l : List α) :
    cyclicFlipCount l
      = (List.zipWith (fun a b => if a ≠ b then 1 else 0) l (l.rotate 1)).sum := by
  cases l with
  | nil => simp [cyclicFlipCount]
  | cons a l =>
      rw [cyclicFlipCount, flipAux_eq_zipWith]
      congr 1
      simp [List.rotate_cons_succ, List.rotate_zero]

/-- The sum of a `zipWith` over two equal-length lists is the indexed sum over `Fin`. -/
theorem zipWith_sum_eq_finsum {β : Type*} (g : β → β → ℕ) (l m : List β)
    (h : l.length = m.length) :
    (List.zipWith g l m).sum = ∑ i : Fin l.length, g (l.get i) (m.get (Fin.cast h i)) := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi2
    simp [List.getElem_zipWith, List.getElem_ofFn]

end ListBridge



section OrbitBridge

variable {α : Type*} [DecidableEq α] [Fintype α] {β : Type*} [DecidableEq β]

/-- The cyclic flip count of `(p.toList x).map f` as an indexed sum over the orbit positions. -/
theorem cyclicFlipCount_map_toList_eq_finsum (p : Perm α) (x : α) (f : α → β) :
    cyclicFlipCount ((p.toList x).map f)
      = ∑ i : Fin (p.toList x).length,
          (if f ((p ^ (i : ℕ)) x) ≠ f (p ((p ^ (i : ℕ)) x)) then 1 else 0) := by
  rw [cyclicFlipCount_eq_zipWith_rotate,
      zipWith_sum_eq_finsum _ _ _ (by rw [List.length_rotate])]
  have hlen : ((p.toList x).map f).length = (p.toList x).length := by simp
  rw [← Fin.sum_congr' _ hlen.symm]
  apply Finset.sum_congr rfl
  intro i _
  have e1 : ((p.toList x).map f).get (Fin.cast hlen.symm i) = f ((p ^ (i : ℕ)) x) := by
    rw [List.get_eq_getElem, List.getElem_map, Equiv.Perm.getElem_toList]; rfl
  have e2 : (((p.toList x).map f).rotate 1).get
        (Fin.cast (by rw [List.length_rotate]) (Fin.cast hlen.symm i))
      = f (p ((p ^ (i : ℕ)) x)) := by
    rw [List.get_eq_getElem, List.getElem_rotate, List.getElem_map, Equiv.Perm.getElem_toList]
    simp only [List.length_map, Equiv.Perm.length_toList]
    rw [Equiv.Perm.pow_mod_card_support_cycleOf_self_apply, pow_succ', mul_apply]
    rfl
  rw [e1, e2]

/-- Indexed sum over orbit positions equals the count over the orbit Finset (`toList.toFinset`),
because `p.toList x` is `Nodup` and `i ↦ (p.toList x).get i` enumerates it. -/
theorem finsum_orbit_eq_toFinset_card (p : Perm α) (x : α) (P : α → Prop) [DecidablePred P] :
    (∑ i : Fin (p.toList x).length, (if P ((p ^ (i : ℕ)) x) then 1 else 0))
      = ((p.toList x).toFinset.filter P).card := by
  have hget : ∀ i : Fin (p.toList x).length, (p.toList x).get i = (p ^ (i : ℕ)) x := by
    intro i; rw [List.get_eq_getElem, Equiv.Perm.getElem_toList]
  have hstep1 :
      (∑ i : Fin (p.toList x).length, (if P ((p ^ (i : ℕ)) x) then 1 else 0))
        = ((p.toList x).map (fun y => if P y then 1 else 0)).sum := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hi2
      rw [List.getElem_ofFn, List.getElem_map, Equiv.Perm.getElem_toList]
  rw [hstep1]
  have hnodup := Equiv.Perm.nodup_toList p x
  have h1 : ((p.toList x).map (fun y => if P y then 1 else 0)).sum
      = ((p.toList x).filter (fun y => decide (P y))).length := by
    induction (p.toList x) with
    | nil => simp
    | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, List.filter_cons]
        by_cases hp : P a <;> simp [hp] <;> omega
  rw [h1, ← List.toFinset_card_of_nodup (hnodup.filter _)]
  congr 1
  ext y
  simp [List.mem_toFinset, Finset.mem_filter]

/-- The orbit Finset (`toList.toFinset`) is the `SameCycle` fiber intersected with the support. -/
theorem toList_toFinset_eq (p : Perm α) (x : α) :
    (p.toList x).toFinset
      = Finset.univ.filter (fun y => p.SameCycle x y ∧ x ∈ p.support) := by
  ext y
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Equiv.Perm.mem_toList_iff

/-- **Layer 2 (orbit bridge).**  For a permutation `p` and a (decidable) sign function `f`, the
cyclic flip count of `(p.toList x).map f` is the number of darts `y` in the support-orbit of `x`
with `f y ≠ f (p y)`. -/
theorem cyclicFlipCount_map_toList_eq_orbitFlip (p : Perm α) (x : α) (f : α → β) :
    cyclicFlipCount ((p.toList x).map f)
      = (Finset.univ.filter
          (fun y => (p.SameCycle x y ∧ x ∈ p.support) ∧ f y ≠ f (p y))).card := by
  rw [cyclicFlipCount_map_toList_eq_finsum,
      finsum_orbit_eq_toFinset_card p x (fun y => f y ≠ f (p y)), toList_toFinset_eq]
  congr 1
  rw [Finset.filter_filter]

end OrbitBridge



section StrictBridge

variable {D : Type*} [Fintype D] [DecidableEq D]



@[simp] theorem toStrict_strictToEdge (a : StrictEdgeSign) :
    (strictToEdge a).toStrict = some a := by cases a <;> rfl

/-- `filterMap toStrict` undoes `map strictToEdge`: a strict list embedded into `EdgeSign` and then
filtered back is itself (there are no zeros to drop). -/
theorem filterMap_toStrict_map_strictToEdge (l : List StrictEdgeSign) :
    (l.map strictToEdge).filterMap EdgeSign.toStrict = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, List.filterMap_cons, toStrict_strictToEdge, ih]

/-- The orbit-bridge set (the `SameCycle ∧ support`-restricted change set) equals the strict core's
`vertexFlip` fiber.  This holds in both the support case (genuine cycle) and the fixed-point case
(degree-`1` vertex), where both counts vanish. -/
theorem orbitFlip_set_eq_vertexFlip (M : CombMap D) (s : D → StrictEdgeSign) (d₀ : D) :
    (Finset.univ.filter
       (fun y => (M.σ.SameCycle d₀ y ∧ d₀ ∈ M.σ.support) ∧ s y ≠ s (M.σ y))).card
      = vertexFlip M s (Quotient.mk (cycleSetoid M.σ) d₀) := by
  rw [vertexFlip, vertexChangeSet, Finset.filter_filter]
  by_cases hd : d₀ ∈ M.σ.support
  · apply Finset.card_bij (fun y _ => y)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨hy.2, by rw [Quotient.eq]; exact hy.1.1.symm⟩
    · intro a _ b _ h; exact h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨y, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Quotient.eq] at hy
      exact ⟨⟨hy.2.symm, hd⟩, hy.1⟩
  · have hfix : M.σ d₀ = d₀ := by
      rw [Equiv.Perm.mem_support, not_not] at hd; exact hd
    rw [Finset.filter_eq_empty_iff.mpr (fun y _ h => hd h.1.2), Finset.card_empty]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    obtain ⟨hflip, hmk⟩ := hy
    rw [Quotient.eq] at hmk
    have hyd : y = d₀ := by
      obtain ⟨k, hk⟩ := hmk
      have hk' : (M.σ ^ (-k)) d₀ = y := by rw [← hk]; simp
      rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix] at hk'
      exact hk'.symm
    rw [hyd, hfix] at hflip
    exact hflip rfl

/-- **Strict bridge.**  For a strict signing `s`, the book's skip-zero count of the embedded edge
signing `strictToEdge ∘ s`, read in `σ`-order around the vertex of `d₀`, equals the strict core's
`vertexFlip`. -/
theorem vertexFlipCountSkipZeros_strict_eq_vertexFlip
    (M : CombMap D) (s : D → StrictEdgeSign) (d₀ : D) :
    vertexFlipCountSkipZeros M (fun d => strictToEdge (s d)) d₀
      = vertexFlip M s (Quotient.mk (cycleSetoid M.σ) d₀) := by
  rw [vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros]
  -- (σ.toList d₀).map (strictToEdge ∘ s) |>.filterMap toStrict = (σ.toList d₀).map s
  have hfm : (((M.σ.toList d₀).map (fun d => strictToEdge (s d))).filterMap EdgeSign.toStrict)
      = (M.σ.toList d₀).map s := by
    have h2 : ((M.σ.toList d₀).map (fun d => strictToEdge (s d)))
        = ((M.σ.toList d₀).map s).map strictToEdge := by rw [List.map_map]; rfl
    rw [h2, filterMap_toStrict_map_strictToEdge]
  rw [hfm, cyclicFlipCount_map_toList_eq_orbitFlip, orbitFlip_set_eq_vertexFlip]

end StrictBridge



section ActiveComponent

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- The face flip count is at most the face degree (it counts a subset of the face's darts). -/
theorem faceFlip_le_faceDeg (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.φ)) : faceFlip M s Q ≤ faceDeg M Q := by
  rw [faceFlip, faceDeg, faceChangeSet]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.2

/-- **The planar per-face bound.**  On a face of degree `m ≥ 3`, the (even) face flip count is at
most `2m − 4`.  For `m = 3` it is `≤ 2 = 2·3 − 4` (even and `≤ 3`); for `m ≥ 4`,
`faceFlip ≤ m ≤ 2m − 4`. -/
theorem faceFlip_le_two_mul_faceDeg_sub_four (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.φ)) (h3 : 3 ≤ faceDeg M Q) :
    faceFlip M s Q ≤ 2 * faceDeg M Q - 4 := by
  have hle := faceFlip_le_faceDeg M s Q
  rcases faceFlip_even M s Q with ⟨k, hk⟩
  omega

/-- **The non-triangular active-component low-vertex theorem.**

Let `A` be a connected combinatorial map of sphere Euler characteristic (`V − E + F = 2`) whose
faces all have degree `≥ 3` (with `∑ faceDeg = 2E`).  Then every edge-invariant strict signing has
a vertex with at most two corner changes.

This is the surgery-free core of the with-zeros Cauchy lemma: applied to the active component of a
marked sphere it yields the desired low active vertex.  It strictly generalizes
`strict_signed_triangulated_sphere_not_all_ge_four`. -/
theorem active_component_low_vertex (A : CombMap D)
    (hEuler : (A.V : ℤ) - A.E + A.F = 2)
    (hFaceDegSum : (∑ R : Quotient (cycleSetoid A.φ), faceDeg A R) = 2 * A.E)
    (hFaceDeg_ge_three : ∀ R : Quotient (cycleSetoid A.φ), 3 ≤ faceDeg A R)
    (s : D → StrictEdgeSign) (hs : EdgeInvariant A s) :
    ∃ Q : Quotient (cycleSetoid A.σ), vertexFlip A s Q ≤ 2 := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hall4 : ∀ Q, 4 ≤ vertexFlip A s Q := by
    intro Q
    have h3 : 3 ≤ vertexFlip A s Q := hcon Q
    rcases vertexFlip_even A s Q with ⟨k, hk⟩
    omega
  have hV : 4 * A.V ≤ ∑ Q : Quotient (cycleSetoid A.σ), vertexFlip A s Q := by
    have hle : (∑ _Q : Quotient (cycleSetoid A.σ), (4 : ℕ)) ≤
        ∑ Q : Quotient (cycleSetoid A.σ), vertexFlip A s Q :=
      Finset.sum_le_sum (fun Q _ => hall4 Q)
    simpa [Finset.sum_const, Finset.card_univ, V, Nat.mul_comm] using hle
  have heq := sum_vertexFlip_eq_sum_faceFlip A s hs
  have hFbound : (∑ R : Quotient (cycleSetoid A.φ), faceFlip A s R)
      ≤ ∑ R : Quotient (cycleSetoid A.φ), (2 * faceDeg A R - 4) :=
    Finset.sum_le_sum
      (fun R _ => faceFlip_le_two_mul_faceDeg_sub_four A s R (hFaceDeg_ge_three R))
  have hsum_int : ((∑ R : Quotient (cycleSetoid A.φ), (2 * faceDeg A R - 4) : ℕ) : ℤ)
      = 2 * (∑ R : Quotient (cycleSetoid A.φ), (faceDeg A R : ℤ)) - 4 * A.F := by
    rw [Nat.cast_sum]
    have hcast : ∀ R : Quotient (cycleSetoid A.φ),
        ((2 * faceDeg A R - 4 : ℕ) : ℤ) = 2 * (faceDeg A R : ℤ) - 4 := by
      intro R; have := hFaceDeg_ge_three R; rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [Finset.sum_congr rfl (fun R _ => hcast R), Finset.sum_sub_distrib, Finset.sum_const,
        ← Finset.mul_sum]
    simp [Finset.card_univ, F]
    ring
  have hFDS_int : (∑ R : Quotient (cycleSetoid A.φ), (faceDeg A R : ℤ)) = 2 * A.E := by
    rw [← Nat.cast_sum]; exact_mod_cast hFaceDegSum
  have key : (4 * A.V : ℤ) ≤ 4 * A.E - 4 * A.F := by
    calc (4 * A.V : ℤ)
        ≤ (∑ Q : Quotient (cycleSetoid A.σ), vertexFlip A s Q : ℕ) := by exact_mod_cast hV
      _ = (∑ R : Quotient (cycleSetoid A.φ), faceFlip A s R : ℕ) := by exact_mod_cast heq
      _ ≤ (∑ R : Quotient (cycleSetoid A.φ), (2 * faceDeg A R - 4) : ℕ) := by exact_mod_cast hFbound
      _ = 2 * (∑ R : Quotient (cycleSetoid A.φ), (faceDeg A R : ℤ)) - 4 * A.F := hsum_int
      _ = 2 * (2 * A.E) - 4 * A.F := by rw [hFDS_int]
      _ = 4 * A.E - 4 * A.F := by ring
  linarith [hEuler, key]





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



/-- For any combinatorial map, the sum of face degrees is `2E` (orbit partition). -/
theorem sum_faceDeg_eq_two_mul_E (A : CombMap D) :
    (∑ R : Quotient (cycleSetoid A.φ), faceDeg A R) = 2 * A.E := by
  have h := CombMap.sum_class_card A.φ
  rw [CombMap.two_mul_E_eq_card]
  simpa [faceDeg] using h













open ProofsInTheBook.SubmapPlanar



@[simp] theorem keptMap_sigma (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    (keptMap M Del hsub).σ = Equiv.Perm.deleteSet M.σ Del := rfl

@[simp] theorem keptMap_alpha (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    (keptMap M Del hsub).α = keptAlpha M Del hsub := rfl

/-- **Euler char of the kept map is `2` when it is connected** (genus-0 certificate from
`SubmapPlanar.keptMap_eulerChar_eq_two`): the active sub-map of a sphere has no handle. -/
theorem keptMap_eulerChar_eq_two_of_connected (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del) (hsphere : M.IsSphereMap)
    (d : {d : D // d ∉ Del}) (hconn : (keptMap M Del hsub).Connected) :
    (keptMap M Del hsub).eulerChar = 2 :=
  ProofsInTheBook.SubmapPlanar.keptMap_eulerChar_eq_two M Del hsub hclosed hsphere
    (keptMap M Del hsub) rfl rfl d hconn

/-- Euler identity form `(V:ℤ) - E + F = 2` for the connected kept map. -/
theorem keptMap_euler_VEF (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del) (hsphere : M.IsSphereMap)
    (d : {d : D // d ∉ Del}) (hconn : (keptMap M Del hsub).Connected) :
    ((keptMap M Del hsub).V : ℤ) - (keptMap M Del hsub).E + (keptMap M Del hsub).F = 2 := by
  have h := keptMap_eulerChar_eq_two_of_connected M Del hsub hclosed hsphere d hconn
  rwa [CombMap.eulerChar] at h



  -- unreachable on active darts





/-- The kept strict signing is edge-invariant when `es` is. -/
theorem keptSign_edgeInvariant (M : CombMap D) (es : D → EdgeSign) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (hes : ∀ d, es (M.α d) = es d) :
    EdgeInvariant (keptMap M Del hsub) (keptSign M es Del) := by
  intro d
  simp only [keptSign, keptMap_alpha, keptAlpha_apply_coe, hes d.1]



/-- **Conditional active-component low vertex.**  For an `α`-closed deleted set `Del` such that the
kept (active) map is connected and has all faces of degree `≥ 3`, the kept strict signing has a kept
vertex with at most two corner changes.  (Free assembly of the proven core over the kept map.) -/
theorem keptMap_low_vertex
    (M : CombMap D) (es : D → EdgeSign) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap) (hes : ∀ d, es (M.α d) = es d)
    (d₀ : {d : D // d ∉ Del})
    (hconn : (keptMap M Del hsub).Connected)
    (hFaceDeg : ∀ R, 3 ≤ faceDeg (keptMap M Del hsub) R) :
    ∃ Q : Quotient (cycleSetoid (keptMap M Del hsub).σ),
      vertexFlip (keptMap M Del hsub) (keptSign M es Del) Q ≤ 2 := by
  set A := keptMap M Del hsub with hA
  refine active_component_low_vertex A ?_ ?_ hFaceDeg (keptSign M es Del)
    (keptSign_edgeInvariant M es Del hsub hes)
  · exact keptMap_euler_VEF M Del hsub hclosed hsphere d₀ hconn
  · exact sum_faceDeg_eq_two_mul_E A



/-- **Modular with-zeros marked-sphere low active vertex.**  Given the active component as a
connected, face-degree-`≥ 3` kept map together with the flip-count transport, the book's with-zeros
conclusion follows: some active `M`-vertex has skip-zero flip count `≤ 2`. -/
theorem marked_sphere_low_active_vertex_modular
    (M : CombMap D) (es : D → EdgeSign) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap) (hes : ∀ d, es (M.α d) = es d)
    (d₀ : {d : D // d ∉ Del})
    (hDel : ∀ d : {d : D // d ∉ Del}, es d.1 ≠ EdgeSign.zero)
    (hconn : (keptMap M Del hsub).Connected)
    (hFaceDeg : ∀ R, 3 ≤ faceDeg (keptMap M Del hsub) R)
    (htrans : ∀ d : {d : D // d ∉ Del},
      vertexFlip (keptMap M Del hsub) (keptSign M es Del)
        (Quotient.mk (cycleSetoid (keptMap M Del hsub).σ) d) = vertexFlipCountSkipZeros M es d.1) :
    ∃ d : D, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  obtain ⟨Q, hQ⟩ := keptMap_low_vertex M es Del hsub hclosed hsphere hes d₀ hconn hFaceDeg
  obtain ⟨d, rfl⟩ := Q.exists_rep
  refine ⟨d.1, ?_, ?_⟩
  · -- the kept dart d.1 is active (nonzero sign) at its own vertex
    exact ⟨d.1, Equiv.Perm.SameCycle.refl _ _, hDel d⟩
  · rw [← htrans d]; exact hQ









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



/-- The underlying dart of the `n`-th `deleteSet`-iterate of `x` is the `gOffset n`-th `p`-power
of `x.1`. -/
theorem deleteSet_pow_coe (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) (n : ℕ) :
    (((deleteSet p S) ^ n) x : D) = (p ^ gOffset p S x n) x.1 := by
  induction n with
  | zero => simp [gOffset]
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, gOffset]
      -- ((deleteSet p S) ((deleteSet p S)^n x)).1 = (p ^ firstOutside ...) ((deleteSet p S)^n x).1
      rw [Equiv.Perm.deleteSet_apply_coe, ih, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm]

/-- `gOffset` is strictly monotone in `n`: each `firstOutside` step is positive. -/
theorem gOffset_strictMono (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) :
    StrictMono (gOffset p S x) := by
  have hstep : ∀ n, gOffset p S x n < gOffset p S x (n + 1) := by
    intro n
    rw [gOffset]
    have := Equiv.Perm.DeleteSet.firstOutside_pos p S (((deleteSet p S) ^ n) x)
    omega
  exact strictMono_nat_of_lt_succ hstep

/-- Every value `gOffset n` lands on a kept dart (`∉ S`): it is the underlying value of the
`n`-th `deleteSet`-iterate, which lives in the subtype. -/
theorem gOffset_kept (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) (n : ℕ) :
    (p ^ gOffset p S x n) x.1 ∉ S := by
  rw [← deleteSet_pow_coe]
  exact (((deleteSet p S) ^ n) x).2

/-- The orbit length `L = (p.toList x).length` is a period of `x` under `p`. -/
theorem pow_length_toList_apply (p : Equiv.Perm D) (x : D) :
    (p ^ (p.toList x).length) x = x := by
  rw [Equiv.Perm.length_toList]
  have := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply p ((p.cycleOf x).support.card) x
  rw [Nat.mod_self, pow_zero, Equiv.Perm.coe_one, id_eq] at this
  exact this.symm

/-- **`firstOutside` wrap bound.**  If `y.1 = (p ^ g) x.1` with `g < L = (p.toList x.1).length`,
then the next surviving forward iterate of `y` is reached within `L - g` steps, because index `L`
returns to `x.1`, which survives (`x.1 ∉ S`).  Hence `firstOutside p S y ≤ L - g`. -/
theorem firstOutside_wrap_le (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (g : ℕ) (hg : g < (p.toList x.1).length) (y : {d : D // d ∉ S}) (hy : y.1 = (p ^ g) x.1) :
    Equiv.Perm.DeleteSet.firstOutside p S y ≤ (p.toList x.1).length - g := by
  set L := (p.toList x.1).length with hL
  have hpos : 0 < L - g := Nat.sub_pos_of_lt hg
  have hval : (p ^ (L - g)) y.1 = x.1 := by
    rw [hy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (le_of_lt hg),
      pow_length_toList_apply]
  refine Nat.find_le ?_
  exact ⟨hpos, by rw [hval]; exact x.2⟩

/-- **Nodup injectivity of iterates on the orbit list.**  If `a, b < L' = length of the
`deleteSet`-orbit list of `x` and the `a`-th and `b`-th iterates coincide, then `a = b`. -/
theorem deleteSet_pow_inj (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    {a b : ℕ} (ha : a < ((deleteSet p S).toList x).length)
    (hb : b < ((deleteSet p S).toList x).length)
    (hab : ((deleteSet p S) ^ a) x = ((deleteSet p S) ^ b) x) : a = b := by
  have hnodup := Equiv.Perm.nodup_toList (deleteSet p S) x
  rw [List.nodup_iff_injective_getElem] at hnodup
  have hga : ((deleteSet p S).toList x)[a] = ((deleteSet p S) ^ a) x :=
    Equiv.Perm.getElem_toList _ _ _ _
  have hgb : ((deleteSet p S).toList x)[b] = ((deleteSet p S) ^ b) x :=
    Equiv.Perm.getElem_toList _ _ _ _
  have : (⟨a, ha⟩ : Fin _) = ⟨b, hb⟩ := by
    apply hnodup
    simp only [hga, hgb, hab]
  exact Fin.mk.injEq .. ▸ this

/-- **Boundedness of `gOffset`.**  For `n` below the `deleteSet`-orbit length `L'`, the cumulative
offset `gOffset n` stays strictly below the full orbit length `L = (p.toList x.1).length`.

Proof: were some `gOffset n ≥ L` with `n < L'`, take the minimal such `n`; then `n > 0`
(`gOffset 0 = 0`), `gOffset (n-1) < L`, and the wrap bound forces `gOffset n ≤ L`, hence
`gOffset n = L`, so `(deleteSet)^n x` returns to `x` — contradicting `Nodup` (`n ≠ 0`, both
`< L'`). -/
theorem gOffset_lt_length (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) :
    ∀ n, n < ((deleteSet p S).toList x).length → gOffset p S x n < (p.toList x.1).length := by
  set L := (p.toList x.1).length with hLdef
  set L' := ((deleteSet p S).toList x).length with hL'def
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hnL', hgn⟩ := hcon
  -- minimal counterexample
  obtain ⟨m, hmL', hgm, hmin⟩ :
      ∃ m, m < L' ∧ L ≤ gOffset p S x m ∧ ∀ k < m, ¬ (k < L' ∧ L ≤ gOffset p S x k) := by
    have hex : ∃ m, m < L' ∧ L ≤ gOffset p S x m := ⟨n, hnL', hgn⟩
    classical
    let m := Nat.find hex
    have hspec := Nat.find_spec hex
    exact ⟨m, hspec.1, hspec.2, fun k hk => Nat.find_min hex hk⟩
  -- m > 0 since gOffset 0 = 0 < L
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, gOffset] at hgm; omega
    · exact hpos
  -- gOffset (m-1) < L
  have hm1L' : m - 1 < L' := by omega
  have hgm1 : gOffset p S x (m - 1) < L := by
    by_contra h
    push Not at h
    exact hmin (m - 1) (by omega) ⟨hm1L', h⟩
  -- the underlying dart at iterate (m-1)
  have hval : (((deleteSet p S) ^ (m - 1)) x : D) = (p ^ gOffset p S x (m - 1)) x.1 :=
    deleteSet_pow_coe p S x (m - 1)
  -- wrap bound: firstOutside ≤ L - gOffset (m-1)
  have hwrap : Equiv.Perm.DeleteSet.firstOutside p S (((deleteSet p S) ^ (m - 1)) x)
      ≤ L - gOffset p S x (m - 1) :=
    firstOutside_wrap_le p S x (gOffset p S x (m - 1)) hgm1 _ hval
  -- gOffset m = gOffset (m-1) + firstOutside, so gOffset m ≤ L
  have hmsucc : gOffset p S x m
      = gOffset p S x (m - 1)
        + Equiv.Perm.DeleteSet.firstOutside p S (((deleteSet p S) ^ (m - 1)) x) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [gOffset]
  have hgmLe : gOffset p S x m ≤ L := by omega
  have hgmEq : gOffset p S x m = L := le_antisymm hgmLe hgm
  -- so (deleteSet)^m x = x
  have hreturn : ((deleteSet p S) ^ m) x = x := by
    apply Subtype.ext
    rw [deleteSet_pow_coe, hgmEq, pow_length_toList_apply]
  -- contradiction with Nodup: m and 0 both < L', m > 0
  have hzero : ((deleteSet p S) ^ (0 : ℕ)) x = x := by simp
  have := deleteSet_pow_inj p S x hmL' (by omega : (0:ℕ) < L') (by rw [hreturn, hzero])
  omega

/-- The powers `p^i x` for `i < L = (p.toList x).length` are pairwise distinct. -/
theorem pow_inj_lt_length (p : Equiv.Perm D) (x : D) {a b : ℕ}
    (ha : a < (p.toList x).length) (hb : b < (p.toList x).length)
    (hab : (p ^ a) x = (p ^ b) x) : a = b := by
  have hnodup := Equiv.Perm.nodup_toList p x
  rw [List.nodup_iff_injective_getElem] at hnodup
  have hga : (p.toList x)[a] = (p ^ a) x := Equiv.Perm.getElem_toList _ _ _ _
  have hgb : (p.toList x)[b] = (p ^ b) x := Equiv.Perm.getElem_toList _ _ _ _
  have : (⟨a, ha⟩ : Fin _) = ⟨b, hb⟩ := by
    apply hnodup; simp only [hga, hgb, hab]
  exact Fin.mk.injEq .. ▸ this

/-- The `deleteSet`-orbit length `L'` is a period: `(deleteSet)^(n % L') x = (deleteSet)^n x`. -/
theorem deleteSet_pow_mod_length (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) (n : ℕ) :
    ((deleteSet p S) ^ (n % ((deleteSet p S).toList x).length)) x = ((deleteSet p S) ^ n) x := by
  rw [Equiv.Perm.length_toList]
  exact Equiv.Perm.pow_mod_card_support_cycleOf_self_apply (deleteSet p S) n x

/-- **Completeness of `gOffset`.**  Every kept index `i < L` of the `p`-orbit of `x.1` is hit by
some `gOffset n` with `n < L'`.  Proof: the kept dart `p^i x.1` is `deleteSet`-`SameCycle` to `x`
(via `sameCycle_deleteSet_iff`), hence equals `(deleteSet)^n x` for some `n < L'` (reduce the
exponent mod the period `L'`); injectivity of `p^· x.1` on `[0,L)` then pins `gOffset n = i`. -/
theorem gOffset_surj (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((deleteSet p S).toList x).length)
    {i : ℕ} (hi : i < (p.toList x.1).length)
    (hkept : (p ^ i) x.1 ∉ S) :
    ∃ n, n < ((deleteSet p S).toList x).length ∧ gOffset p S x n = i := by
  set L' := ((deleteSet p S).toList x).length with hL'def
  -- the kept dart as a subtype element
  set y : {d : D // d ∉ S} := ⟨(p ^ i) x.1, hkept⟩ with hy
  -- p.SameCycle x.1 y.1, hence deleteSet-SameCycle x y
  have hsc : p.SameCycle x.1 y.1 := ⟨i, by rw [zpow_natCast]⟩
  have hsc' : (deleteSet p S).SameCycle x y :=
    (Equiv.Perm.sameCycle_deleteSet_iff p S x y).2 hsc
  obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := deleteSet p S) hsc'
  -- reduce k mod L'
  refine ⟨k % L', Nat.mod_lt _ hL'pos, ?_⟩
  have hpow : ((deleteSet p S) ^ (k % L')) x = y := by
    rw [deleteSet_pow_mod_length, hk]
  -- p^(gOffset (k%L')) x.1 = p^i x.1
  have hval : (p ^ gOffset p S x (k % L')) x.1 = (p ^ i) x.1 := by
    rw [← deleteSet_pow_coe, hpow]
  -- gOffset (k%L') < L by boundedness, i < L, injectivity ⟹ equal
  have hgbnd : gOffset p S x (k % L') < (p.toList x.1).length :=
    gOffset_lt_length p S x hL (k % L') (Nat.mod_lt _ hL'pos)
  exact pow_inj_lt_length p x.1 hgbnd hi hval



/-- `p.toList x` is the `range`-map of the orbit powers. -/
theorem toList_eq_range_map (p : Equiv.Perm D) (x : D) :
    p.toList x = (List.range (p.toList x).length).map (fun i => (p ^ i) x) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi2
    rw [List.getElem_map, List.getElem_range, Equiv.Perm.getElem_toList]



/-- **Index-list identity (G).**  When the `deleteSet`-orbit of `x` is nontrivial (`L' > 0`), the
cumulative-offset sequence enumerates exactly the kept indices of the `p`-orbit, in increasing
order:
  `(range L').map gOffset = (range L).filter (fun i => (p ^ i) x.1 ∉ S)`.
Proved by `Perm.eq_of_sortedLE`: both lists are `Nodup`, `SortedLE`, and have the same membership
(boundedness + kept ⟹ ⊆; completeness ⟹ ⊇). -/
theorem gOffset_range_map_eq_filter (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((deleteSet p S).toList x).length) :
    (List.range ((deleteSet p S).toList x).length).map (gOffset p S x)
      = (List.range (p.toList x.1).length).filter (fun i => decide ((p ^ i) x.1 ∉ S)) := by
  set L := (p.toList x.1).length with hLdef
  set L' := ((deleteSet p S).toList x).length with hL'def
  -- membership characterization of each side
  have hmemL : ∀ i, i ∈ (List.range L').map (gOffset p S x)
      ↔ (i < L ∧ (p ^ i) x.1 ∉ S) := by
    intro i
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨gOffset_lt_length p S x hL n hn, gOffset_kept p S x n⟩
    · rintro ⟨hiL, hkept⟩
      obtain ⟨n, hn, hgn⟩ := gOffset_surj p S x hL hL'pos hiL hkept
      exact ⟨n, hn, hgn⟩
  have hmemR : ∀ i, i ∈ (List.range L).filter (fun i => decide ((p ^ i) x.1 ∉ S))
      ↔ (i < L ∧ (p ^ i) x.1 ∉ S) := by
    intro i
    rw [List.mem_filter, List.mem_range, decide_eq_true_iff]
  -- both Nodup
  have hndL : ((List.range L').map (gOffset p S x)).Nodup :=
    (List.nodup_range).map (gOffset_strictMono p S x).injective
  have hndR : ((List.range L).filter (fun i => decide ((p ^ i) x.1 ∉ S))).Nodup :=
    (List.nodup_range).filter _
  -- Perm via mutual subperm
  have hperm : ((List.range L').map (gOffset p S x)).Perm
      ((List.range L).filter (fun i => decide ((p ^ i) x.1 ∉ S))) := by
    apply List.Subperm.antisymm
    · apply hndL.subperm
      intro i hi; rw [hmemR]; exact (hmemL i).1 hi
    · apply hndR.subperm
      intro i hi; rw [hmemL]; exact (hmemR i).1 hi
  -- both SortedLE
  have hsortL : ((List.range L').map (gOffset p S x)).SortedLE := by
    rw [List.sortedLE_iff_pairwise, List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun hab => le_of_lt ((gOffset_strictMono p S x) hab))
  have hsortR : ((List.range L).filter (fun i => decide ((p ^ i) x.1 ∉ S))).SortedLE := by
    rw [List.sortedLE_iff_pairwise]
    exact (List.pairwise_lt_range.imp (fun h => le_of_lt h)).filter _
  exact hperm.eq_of_sortedLE hsortL hsortR

/-- **Filtered-`toList` identity (L), nontrivial case.**  When the `deleteSet`-orbit of `x` is
nontrivial, the underlying darts of the `deleteSet`-orbit list of `x` are exactly the surviving
(`∉ S`) darts of the `p`-orbit list of `x.1`, in cyclic order. -/
theorem deleteSet_toList_map_val (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((deleteSet p S).toList x).length) :
    ((deleteSet p S).toList x).map Subtype.val = (p.toList x.1).filter (fun d => decide (d ∉ S)) := by
  -- LHS = (range L').map (p^(gOffset ·) x.1)
  have hLHS : ((deleteSet p S).toList x).map Subtype.val
      = (List.range ((deleteSet p S).toList x).length).map (fun n => (p ^ gOffset p S x n) x.1) := by
    conv_lhs => rw [show (deleteSet p S).toList x
      = (List.range ((deleteSet p S).toList x).length).map
          (fun n => ((deleteSet p S) ^ n) x) from toList_eq_range_map (deleteSet p S) x]
    rw [List.map_map]
    apply List.map_congr_left
    intro n _
    exact deleteSet_pow_coe p S x n
  -- RHS = ((range L).filter (∉S after p^·)).map (p^· x.1), via injective map-filter commute
  have hRHS : (p.toList x.1).filter (fun d => decide (d ∉ S))
      = ((List.range (p.toList x.1).length).filter (fun i => decide ((p ^ i) x.1 ∉ S))).map
          (fun i => (p ^ i) x.1) := by
    conv_lhs => rw [toList_eq_range_map p x.1]
    rw [List.filter_map]
    rfl
  rw [hLHS, hRHS]
  -- both are maps over index lists that agree by (G)
  rw [← gOffset_range_map_eq_filter p S x hL hL'pos, List.map_map]
  rfl



/-- On a nonzero edge sign, `EdgeSign.toStrict` is `some` of `edgeToStrict`. -/
theorem toStrict_eq_some_edgeToStrict {a : EdgeSign} (h : a ≠ EdgeSign.zero) :
    a.toStrict = some (edgeToStrict a) := by
  cases a with
  | plus => rfl
  | minus => rfl
  | zero => exact absurd rfl h

omit [Fintype D] [DecidableEq D] in
/-- `filterMap (toStrict ∘ es)` over a list equals `map (edgeToStrict ∘ es)` over the sublist of
darts with nonzero sign.  (A `filterMap` whose option is governed by the nonzero predicate is a
`filter` followed by a `map`.) -/
theorem filterMap_toStrict_eq_filter_map (es : D → EdgeSign) (l : List D) :
    l.filterMap (fun d => (es d).toStrict)
      = (l.filter (fun d => decide (es d ≠ EdgeSign.zero))).map (fun d => edgeToStrict (es d)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.filterMap_cons, List.filter_cons]
      by_cases ha : es a = EdgeSign.zero
      · rw [ha]
        rw [show (EdgeSign.zero.toStrict) = none from rfl]
        rw [if_neg (by simp), ih]
      · rw [toStrict_eq_some_edgeToStrict ha, if_pos (by simpa using ha), List.map_cons, ih]



/-- `cyclicFlipCount` of a list of length `≤ 1` is `0`. -/
theorem cyclicFlipCount_eq_zero_of_length_le_one {α : Type*} [DecidableEq α] (l : List α)
    (h : l.length ≤ 1) : cyclicFlipCount l = 0 := by
  match l, h with
  | [], _ => rfl
  | [a], _ => simp only [cyclicFlipCount, flipAux, ne_eq, not_true_eq_false, if_false]































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



/-- `faceDeg = faceLen` (same orbit-card definition). -/
theorem faceDeg_eq_faceLen (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) :
    faceDeg M Q = M.faceLen Q := rfl







/-- Two kept darts have the same kept tail-vertex iff their underlying darts have the same
`M`-tail-vertex. -/
theorem keptMap_tail_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).tail x = (keptMap M Del hsub).tail y ↔ M.tail x.1 = M.tail y.1 := by
  unfold CombMap.tail
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle x y ↔ M.σ.SameCycle x.1 y.1
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del x y

/-- The kept head-vertex of `x` is the `M`-head-vertex of `x.1`, transported. -/
theorem keptMap_head_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).head x = (keptMap M Del hsub).head y ↔ M.head x.1 = M.head y.1 := by
  unfold CombMap.head
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle ((keptMap M Del hsub).α x) ((keptMap M Del hsub).α y)
      ↔ M.σ.SameCycle (M.α x.1) (M.α y.1)
  have hx : ((keptMap M Del hsub).α x : D) = M.α x.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub x
  have hy : ((keptMap M Del hsub).α y : D) = M.α y.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub y
  rw [← hx, ← hy]
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del _ _

/-- Cross form: kept-tail of `x` equals kept-head of `y` iff `M`-tail of `x.1` equals `M`-head of
`y.1`. -/
theorem keptMap_tail_eq_head_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).tail x = (keptMap M Del hsub).head y ↔ M.tail x.1 = M.head y.1 := by
  unfold CombMap.tail CombMap.head
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle x ((keptMap M Del hsub).α y)
      ↔ M.σ.SameCycle x.1 (M.α y.1)
  have hy : ((keptMap M Del hsub).α y : D) = M.α y.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub y
  rw [← hy]
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del _ _

/-- The kept `dartEdge` of `x` is `s(keptTail x, keptHead x)`; we compare via the `M`-endpoints. -/
theorem keptMap_dartEdge_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).dartEdge x = (keptMap M Del hsub).dartEdge y
      ↔ M.dartEdge x.1 = M.dartEdge y.1 := by
  unfold CombMap.dartEdge
  rw [Sym2.eq_iff, Sym2.eq_iff,
    keptMap_tail_eq_iff M Del hsub x y, keptMap_head_eq_iff M Del hsub x y,
    keptMap_tail_eq_head_iff M Del hsub x y,
    show ((keptMap M Del hsub).head x = (keptMap M Del hsub).tail y)
        ↔ (M.head x.1 = M.tail y.1) from by
      rw [eq_comm, keptMap_tail_eq_head_iff M Del hsub y x, eq_comm]]

/-- **The kept (active sub-)map inherits `IsSimpleGraph`.** -/
theorem keptMap_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    (keptMap M Del hsub).IsSimpleGraph where
  no_loop x := by
    rw [Ne, keptMap_tail_eq_head_iff M Del hsub x x]
    exact hM.no_loop x.1
  no_parallel {x y} h := by
    -- kept dartEdge equal ⟹ M dartEdge equal ⟹ M.α.SameCycle x.1 y.1 ⟹ keptAlpha.SameCycle x y
    rw [keptMap_dartEdge_eq_iff M Del hsub x y] at h
    have hMsc : M.α.SameCycle x.1 y.1 := hM.no_parallel h
    -- y.1 ∈ {x.1, M.α x.1}; both kept; gives keptAlpha.SameCycle x y
    rcases (M.alpha_sameCycle_iff x.1 y.1).mp hMsc with hxy | hxy
    · -- y = x
      have hyx : y = x := Subtype.ext hxy
      exact hyx ▸ Equiv.Perm.SameCycle.rfl
    · -- y = M.α x.1 = keptAlpha x (coercion)
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have hcoe : ((keptMap M Del hsub).α x : D) = M.α x.1 := by
        rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub x
      rw [zpow_one, hcoe]
      exact hxy.symm





/-- `activeStep` is symmetric. -/
theorem activeStep_symm (M : CombMap D) (es : D → EdgeSign)
    {d e : D} (h : activeStep M es d e) : activeStep M es e d := by
  obtain ⟨hstep, hd, he⟩ := h
  refine ⟨?_, he, hd⟩
  rcases hstep with hσ | hα
  · exact Or.inl hσ.symm
  · refine Or.inr ?_
    subst hα
    rw [M.alpha_alpha]





/-- A dart **not** in `compDel` is `EqvGen`-reached from `d₀`. -/
theorem reached_of_notMem_compDel (M : CombMap D) (es : D → EdgeSign) (d₀ d : D)
    (hd : d ∉ compDel M es d₀) : Relation.EqvGen (activeStep M es) d₀ d := by
  by_contra h
  exact hd ((mem_compDel M es d₀ d).2 h)









open ProofsInTheBook.Ch13FlipTransport in
/-- **Orbit-local kept-strict-list identity** (nontrivial case).  Same as
`Ch13FlipTransport.kept_strict_list_eq` but with the global `hSzero` replaced by the orbit-local
characterization `hSorbit` on the `p`-orbit of `x.1`. -/
theorem kept_strict_list_eq_orbit (p : Equiv.Perm D) (es : D → EdgeSign) (S : Finset D)
    (x : {d : D // d ∉ S})
    (hSorbit : ∀ c, p.SameCycle x.1 c → (c ∈ S ↔ es c = EdgeSign.zero))
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((Equiv.Perm.deleteSet p S).toList x).length) :
    ((Equiv.Perm.deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1))
      = ((p.toList x.1).map es).filterMap EdgeSign.toStrict := by
  rw [List.filterMap_map, Function.comp_def, filterMap_toStrict_eq_filter_map]
  have hLHS : ((Equiv.Perm.deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1))
      = (((Equiv.Perm.deleteSet p S).toList x).map Subtype.val).map (fun d => edgeToStrict (es d)) := by
    rw [List.map_map]; rfl
  rw [hLHS, deleteSet_toList_map_val p S x hL hL'pos]
  congr 1
  apply List.filter_congr
  intro d hd
  have hsc : p.SameCycle x.1 d := (Equiv.Perm.mem_toList_iff.mp hd).1
  simp only [decide_eq_decide]
  rw [ne_eq, ← hSorbit d hsc]

open ProofsInTheBook.Ch13FlipTransport in
/-- **Orbit-local degenerate case.**  Same as
`Ch13FlipTransport.cyclicFlipCount_filterMap_eq_zero_of_empty` but with orbit-local `hSorbit`. -/
theorem cyclicFlipCount_filterMap_eq_zero_of_empty_orbit (p : Equiv.Perm D) (es : D → EdgeSign)
    (S : Finset D) (x : {d : D // d ∉ S})
    (hSorbit : ∀ c, p.SameCycle x.1 c → (c ∈ S ↔ es c = EdgeSign.zero))
    (hempty : (Equiv.Perm.deleteSet p S).toList x = []) :
    cyclicFlipCount (((p.toList x.1).map es).filterMap EdgeSign.toStrict) = 0 := by
  apply cyclicFlipCount_eq_zero_of_length_le_one
  rw [List.filterMap_map, Function.comp_def, filterMap_toStrict_eq_filter_map, List.length_map]
  have hxfix : (Equiv.Perm.deleteSet p S) x = x := by
    have hnotsupp : x ∉ (Equiv.Perm.deleteSet p S).support := Equiv.Perm.toList_eq_nil_iff.mp hempty
    exact Equiv.Perm.notMem_support.mp hnotsupp
  have hall : ∀ y ∈ (p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)), y = x.1 := by
    intro y hy
    rw [List.mem_filter, decide_eq_true_iff] at hy
    obtain ⟨hymem, hynz⟩ := hy
    have hscy : p.SameCycle x.1 y := (Equiv.Perm.mem_toList_iff.mp hymem).1
    have hyS : y ∉ S := by rw [hSorbit y hscy]; exact hynz
    have hsc' : (Equiv.Perm.deleteSet p S).SameCycle x ⟨y, hyS⟩ :=
      (Equiv.Perm.sameCycle_deleteSet_iff p S x ⟨y, hyS⟩).2 hscy
    obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := Equiv.Perm.deleteSet p S) hsc'
    have hxx : ((Equiv.Perm.deleteSet p S) ^ k) x = x :=
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxfix k
    have hyx : (⟨y, hyS⟩ : {d : D // d ∉ S}) = x := by rw [← hk, hxx]
    exact congrArg Subtype.val hyx
  have hnodup : ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).Nodup :=
    (Equiv.Perm.nodup_toList p x.1).filter _
  by_contra hlen
  push Not at hlen
  obtain ⟨a, b, hab, ha, hb⟩ :
      ∃ a b, a ≠ b ∧ a < ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).length
        ∧ b < ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).length :=
    ⟨0, 1, by omega, by omega, by omega⟩
  rw [List.nodup_iff_injective_getElem] at hnodup
  apply hab
  have he : ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)))[a]
      = ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)))[b] := by
    rw [hall _ (List.getElem_mem ha), hall _ (List.getElem_mem hb)]
  have hfin : (⟨a, ha⟩ : Fin _) = ⟨b, hb⟩ := hnodup he
  exact Fin.mk.injEq .. ▸ hfin

open ProofsInTheBook.Ch13FlipTransport in
/-- **Orbit-local cyclic flip-count transport.**  For an orbit-local zero set, the cyclic flip
count of the kept (`deleteSet`) orbit strict signs equals the zero-skipped count of the full
`p`-orbit. -/
theorem cyclicFlipCount_transport_orbit (p : Equiv.Perm D) (es : D → EdgeSign) (S : Finset D)
    (x : {d : D // d ∉ S})
    (hSorbit : ∀ c, p.SameCycle x.1 c → (c ∈ S ↔ es c = EdgeSign.zero)) :
    cyclicFlipCount (((Equiv.Perm.deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1)))
      = cyclicFlipCount (((p.toList x.1).map es).filterMap EdgeSign.toStrict) := by
  by_cases hL'pos : 0 < ((Equiv.Perm.deleteSet p S).toList x).length
  · have hL : 0 < (p.toList x.1).length := by
      by_contra h
      push Not at h
      have hxfix : p x.1 = x.1 := by
        have hns : x.1 ∉ p.support :=
          Equiv.Perm.toList_eq_nil_iff.mp (List.length_eq_zero_iff.mp (by omega))
        exact Equiv.Perm.notMem_support.mp hns
      have hdfix : (Equiv.Perm.deleteSet p S) x = x := by
        apply Subtype.ext
        rw [Equiv.Perm.deleteSet_apply_coe]
        exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxfix _
      have hns2 : x ∉ (Equiv.Perm.deleteSet p S).support := Equiv.Perm.notMem_support.mpr hdfix
      rw [← Equiv.Perm.toList_eq_nil_iff] at hns2
      rw [hns2] at hL'pos; simp at hL'pos
    rw [kept_strict_list_eq_orbit p es S x hSorbit hL hL'pos]
  · push Not at hL'pos
    have hempty : (Equiv.Perm.deleteSet p S).toList x = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hempty, List.map_nil, cyclicFlipCount,
      cyclicFlipCount_filterMap_eq_zero_of_empty_orbit p es S x hSorbit hempty]



variable (M : CombMap D) (es : D → EdgeSign)



/-- `compDel` is `α`-closed (`hclosed` input). -/
theorem compDel_hclosed (hes : ∀ d, es (M.α d) = es d) {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero) :
    ∀ d, d ∈ compDel M es d₀ → M.α d ∈ compDel M es d₀ :=
  fun d hd => (compDel_hsub M es hes hd₀ d).1 hd

/-- Kept darts of `compDel` are active (`hKeptNonzero`). -/
theorem compDel_hKeptNonzero {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero) :
    ∀ d, d ∉ compDel M es d₀ → es d ≠ EdgeSign.zero :=
  fun d hd => reached_active M es hd₀ (reached_of_notMem_compDel M es d₀ d hd)

/-- The orbit-local zero characterization holds on the `M.σ`-orbit of any kept dart:
a σ-neighbour `c` is deleted iff `es c = 0` (active σ-neighbours of a kept dart are in the same
active component, hence kept). -/
theorem compDel_orbit_zero {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    (x : {d : D // d ∉ compDel M es d₀}) :
    ∀ c, M.σ.SameCycle x.1 c → (c ∈ compDel M es d₀ ↔ es c = EdgeSign.zero) := by
  intro c hsc
  rw [mem_compDel]
  constructor
  · -- c deleted ⟹ es c = 0: if es c ≠ 0, c is reached via a vertex-step from kept x
    intro hcdel
    by_contra hcnz
    apply hcdel
    have hxnz : es x.1 ≠ EdgeSign.zero := compDel_hKeptNonzero M es hd₀ x.1 x.2
    have hxr : Relation.EqvGen (activeStep M es) d₀ x.1 :=
      reached_of_notMem_compDel M es d₀ x.1 x.2
    refine Relation.EqvGen.trans _ _ _ hxr (Relation.EqvGen.rel _ _ ?_)
    exact ⟨Or.inl hsc, hxnz, hcnz⟩
  · -- es c = 0 ⟹ c deleted: an inactive dart is never reached
    intro hcz hcr
    exact (reached_active M es hd₀ hcr) hcz

/-- **Orbit-local flip transport for `compDel`.**  The kept submap's `vertexFlip` at a kept dart's
vertex equals the book's skip-zeros count, even though `compDel` deletes darts of other
components. -/
theorem flip_transport_compDel (hes : ∀ d, es (M.α d) = es d) {d₀ : D}
    (hd₀ : es d₀ ≠ EdgeSign.zero)
    (d : {d : D // d ∉ compDel M es d₀}) :
    vertexFlip (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀))
        (keptSign M es (compDel M es d₀))
        (Quotient.mk (cycleSetoid (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)).σ) d)
      = vertexFlipCountSkipZeros M es d.1 := by
  rw [← ProofsInTheBook.Ch13MarkedReduction.vertexFlipCountSkipZeros_strict_eq_vertexFlip
        (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)) (keptSign M es (compDel M es d₀)) d]
  rw [vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros,
      vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros]
  have hLHSlist :
      (((keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)).σ.toList d).map
            (fun y => strictToEdge (keptSign M es (compDel M es d₀) y))).filterMap
          EdgeSign.toStrict
      = ((Equiv.Perm.deleteSet M.σ (compDel M es d₀)).toList d).map (fun y => edgeToStrict (es y.1)) := by
    rw [keptMap_sigma]
    rw [show (fun y : {d : D // d ∉ compDel M es d₀} =>
            strictToEdge (keptSign M es (compDel M es d₀) y))
          = strictToEdge ∘ (keptSign M es (compDel M es d₀)) from rfl, ← List.map_map,
        ProofsInTheBook.Ch13MarkedReduction.filterMap_toStrict_map_strictToEdge]
    rfl
  rw [hLHSlist]
  exact cyclicFlipCount_transport_orbit M.σ es (compDel M es d₀) d
    (compDel_orbit_zero M es hd₀ d)



/-- Membership-free reachability is symmetric, so `EqvGen activeStep` is `ReflTransGen activeStep`. -/
theorem reflTransGen_activeStep_of_eqvGen {d₀ z : D}
    (h : Relation.EqvGen (activeStep M es) d₀ z) :
    Relation.ReflTransGen (activeStep M es) d₀ z :=
  (eqvGen_iff_reflTransGen (fun _ _ => activeStep_symm M es) d₀ z).1 h

/-- **Every kept dart reaches `d₀` by a kept walk.**  `ReflTransGen activeStep d₀ z` with `z` kept
gives `ReflTransGen keptStepRel ⟨d₀⟩ ⟨z⟩`; intermediates are reachable from `d₀`, hence kept. -/
theorem keptReflTrans_of_reflTransGen_activeStep (hes : ∀ d, es (M.α d) = es d)
    {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    {z : D} (h : Relation.ReflTransGen (activeStep M es) d₀ z) (hz : z ∉ compDel M es d₀) :
    Relation.ReflTransGen
        (ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀)
          (compDel_hsub M es hes hd₀))
        ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩ ⟨z, hz⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hb hbc ih =>
      -- `b` reachable from `d₀` (the prefix), so `b ∉ compDel`
      have hbeqv : Relation.EqvGen (activeStep M es) d₀ b :=
        (eqvGen_iff_reflTransGen (fun _ _ => activeStep_symm M es) d₀ b).2 hb
      have hbkept : b ∉ compDel M es d₀ := by rw [mem_compDel]; exact not_not.2 hbeqv
      -- assemble the kept dart-step `⟨b⟩ → ⟨c⟩`
      have hstep : ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀)
          (compDel_hsub M es hes hd₀) ⟨b, hbkept⟩ ⟨c, hz⟩ := by
        obtain ⟨hstepbc, _, _⟩ := hbc
        rcases hstepbc with hσ | hα
        · exact Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ (compDel M es d₀)
            ⟨b, hbkept⟩ ⟨c, hz⟩).2 hσ)
        · refine Or.inr (Subtype.ext ?_)
          show (c : D) = M.α b
          exact hα
      exact Relation.ReflTransGen.tail (ih hbkept) hstep

/-- **The active component is connected.**  Every pair of kept darts is connected by a kept walk:
route each through the seed `d₀` via `keptReflTrans_of_reflTransGen_activeStep`. -/
theorem compDel_keptMap_connected (hes : ∀ d, es (M.α d) = es d)
    {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero) :
    (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)).Connected := by
  intro a b
  -- the kept dart-step of `keptMap` is `keptStepRel` (definitional)
  show Relation.ReflTransGen
      (ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀) (compDel_hsub M es hes hd₀)) a b
  have hd₀kept : d₀ ∉ compDel M es d₀ := by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)
  -- `a` and `b` both reach `d₀`
  have ha : Relation.ReflTransGen (activeStep M es) d₀ a.1 :=
    reflTransGen_activeStep_of_eqvGen M es (reached_of_notMem_compDel M es d₀ a.1 a.2)
  have hb : Relation.ReflTransGen (activeStep M es) d₀ b.1 :=
    reflTransGen_activeStep_of_eqvGen M es (reached_of_notMem_compDel M es d₀ b.1 b.2)
  have hksymm : ∀ u v, ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀)
      (compDel_hsub M es hes hd₀) u v → ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀)
      (compDel_hsub M es hes hd₀) v u :=
    fun u v h => dartStepRel_symm
      (ProofsInTheBook.SubmapPlanar.keptAlpha_invol M (compDel M es d₀)
        (compDel_hsub M es hes hd₀)) h
  -- a → ⟨d₀⟩ (reverse of ⟨d₀⟩ → a) then ⟨d₀⟩ → b
  have hda : Relation.ReflTransGen
      (ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀) (compDel_hsub M es hes hd₀))
      ⟨d₀, hd₀kept⟩ a :=
    keptReflTrans_of_reflTransGen_activeStep M es hes hd₀ ha a.2
  have hdb : Relation.ReflTransGen
      (ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀) (compDel_hsub M es hes hd₀))
      ⟨d₀, hd₀kept⟩ b :=
    keptReflTrans_of_reflTransGen_activeStep M es hes hd₀ hb b.2
  exact (reflTransGen_symm hksymm hda).trans hdb



/-- A digon (`faceLen = 2`) representative `d` of a simple map has both `A.σ d = d` and
`A.σ (A.α d) = A.α d` (both darts of its single edge are `σ`-fixed leaves). -/
theorem digon_sigma_fixed {A : CombMap D} (hA : A.IsSimpleGraph) {d : D}
    (hφ : A.φ d ≠ d) (hcard2 : (A.φ.cycleOf d).support.card = 2) :
    A.σ d = d ∧ A.σ (A.α d) = A.α d := by
  -- φ² d = d (digon)
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply A.φ 2 d
  rw [hcard2] at hpow
  have hsq : A.φ (A.φ d) = d := by
    have h2 : (A.φ ^ 2) d = d := by simpa using hpow.symm
    simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using h2
  -- the two boundary darts share an edge ⟹ φ d = α d
  have he1 : A.dartEdge d = s(A.tail d, A.tail (A.φ d)) := A.dartEdge_eq_mk_tail_tail_phi d
  have he2 : A.dartEdge (A.φ d) = s(A.tail (A.φ d), A.tail d) := by
    rw [A.dartEdge_eq_mk_tail_tail_phi (A.φ d), hsq]
  have hedge : A.dartEdge d = A.dartEdge (A.φ d) := by rw [he1, he2, Sym2.eq_swap]
  have hsc : A.α.SameCycle d (A.φ d) := hA.no_parallel hedge
  have hφα : A.φ d = A.α d := by
    rcases (A.alpha_sameCycle_iff d (A.φ d)).mp hsc with hcase | hcase
    · exact absurd hcase hφ
    · exact hcase
  -- φ = σ * α: φ d = σ (α d) = α d ⟹ σ fixes α d
  have hσαd : A.σ (A.α d) = A.α d := by
    have : A.σ (A.α d) = A.φ d := rfl
    rw [this, hφα]
  -- φ (φ d) = d with φ d = α d: φ (α d) = σ (α (α d)) = σ d = d ⟹ σ fixes d
  have hσd : A.σ d = d := by
    have hφαd : A.φ (A.α d) = d := by rw [← hφα]; exact hsq
    have hcalc : A.σ d = A.φ (A.α d) := by
      show A.σ d = A.σ (A.α (A.α d))
      rw [A.alpha_alpha]
    rw [hcalc, hφαd]
  exact ⟨hσd, hσαd⟩

/-- **A connected simple map with `≥ 2` edges has all faces of degree `≥ 3`** (no digon). -/
theorem three_le_faceDeg_of_connected_simple_twoEdge {A : CombMap D} (hA : A.IsSimpleGraph)
    (hconn : A.Connected) (hE : 2 ≤ A.E) (R : Quotient (cycleSetoid A.φ)) :
    3 ≤ faceDeg A R := by
  obtain ⟨d, rfl⟩ := R.exists_rep
  have hφ : A.φ d ≠ d := phi_ne_self_of_isSimpleGraph A hA d
  rw [faceDeg_eq_faceLen]
  show 3 ≤ A.faceLen (A.dartFace d)
  rw [faceLen_dartFace_eq_card_support_cycleOf A hφ]
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ (A.φ.cycleOf d).support.card :=
    (Equiv.Perm.isCycle_cycleOf A.φ hφ).two_le_card_support
  have hcard2 : (A.φ.cycleOf d).support.card = 2 := by omega
  obtain ⟨hσd, hσαd⟩ := digon_sigma_fixed hA hφ hcard2
  -- the edge {d, α d} is the entire (connected) map: every dart is d or α d
  have hαd_ne : A.α d ≠ d := A.α_no_fixed d
  -- dartStep from d stays in {d, α d}
  have hstep_d : ∀ y, A.dartStep d y → y = d ∨ y = A.α d := by
    intro y hy
    rcases hy with hσ | hαe
    · -- same σ-cycle as d; σ fixes d ⟹ y = d
      left
      obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := A.σ) hσ
      have : (A.σ ^ k) d = d := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hσd k
      rw [← hk, this]
    · exact Or.inr hαe
  have hstep_αd : ∀ y, A.dartStep (A.α d) y → y = d ∨ y = A.α d := by
    intro y hy
    rcases hy with hσ | hαe
    · right
      obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := A.σ) hσ
      have : (A.σ ^ k) (A.α d) = A.α d := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hσαd k
      rw [← hk, this]
    · left; rw [hαe, A.alpha_alpha]
  -- every dart reachable from d lies in {d, α d}
  have hall : ∀ y, Relation.ReflTransGen A.dartStep d y → y = d ∨ y = A.α d := by
    intro y h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
        rcases ih with rfl | rfl
        · exact hstep_d c hbc
        · exact hstep_αd c hbc
  have hsub : ∀ y : D, y ∈ ({d, A.α d} : Finset D) := by
    intro y
    have := hall y (hconn d y)
    rcases this with rfl | rfl <;> simp
  -- so |D| ≤ 2, hence 2*E = |D| ≤ 2, E ≤ 1, contradicting hE
  have hcardD : Fintype.card D ≤ 2 := by
    have hle : Fintype.card D ≤ ({d, A.α d} : Finset D).card := by
      rw [← Finset.card_univ]
      apply Finset.card_le_card
      intro y _; exact hsub y
    calc Fintype.card D ≤ ({d, A.α d} : Finset D).card := hle
      _ ≤ 2 := by
          calc ({d, A.α d} : Finset D).card ≤ ({A.α d} : Finset D).card + 1 :=
                Finset.card_insert_le _ _
            _ ≤ 2 := by simp
  have h2E : 2 * A.E = Fintype.card D := A.two_mul_E_eq_card
  omega



/-- The modular assembly specialized to `compDel`, transport discharged by `flip_transport_compDel`.
Requires only the two topological residuals on the active component. -/
theorem compDel_low_active_vertex (hsphere : M.IsSphereMap) (hes : ∀ d, es (M.α d) = es d)
    {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    (hFaceDeg : ∀ R, 3 ≤ faceDeg (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)) R) :
    ∃ d : D, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  refine marked_sphere_low_active_vertex_modular M es (compDel M es d₀)
    (compDel_hsub M es hes hd₀) (compDel_hclosed M es hes hd₀) hsphere hes
    ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩
    (fun d => compDel_hKeptNonzero M es hd₀ d.1 d.2)
    (compDel_keptMap_connected M es hes hd₀) hFaceDeg
    (fun d => flip_transport_compDel M es hes hd₀ d)

/-- **Single-edge component branch.**  When the active component has exactly one edge, `d₀`'s kept
vertex is a singleton (`deleteSet M.σ Del` fixes `d₀`), so its skip-zeros flip count is `0`. -/
theorem single_edge_low_active_vertex {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    (hfix : (Equiv.Perm.deleteSet M.σ (compDel M es d₀))
      ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩
        = ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩) :
    ∃ d : D, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  set d₀' : {d : D // d ∉ compDel M es d₀} :=
    ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩ with hd₀'def
  refine ⟨d₀, ⟨d₀, Equiv.Perm.SameCycle.refl _ _, hd₀⟩, ?_⟩
  -- the deleteSet orbit of d₀ is empty (fixed point), so the skip-zeros count is 0
  have hempty : (Equiv.Perm.deleteSet M.σ (compDel M es d₀)).toList d₀' = [] := by
    rw [Equiv.Perm.toList_eq_nil_iff]
    exact Equiv.Perm.notMem_support.mpr hfix
  have hzero : vertexFlipCountSkipZeros M es d₀ = 0 := by
    rw [vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros]
    show cyclicFlipCount (((M.σ.toList d₀).map es).filterMap EdgeSign.toStrict) = 0
    have hval : (d₀ : D) = (d₀' : D) := rfl
    rw [hval]
    exact cyclicFlipCount_filterMap_eq_zero_of_empty_orbit M.σ es (compDel M es d₀) d₀'
      (compDel_orbit_zero M es hd₀ d₀') hempty
  rw [hzero]; omega

/-- **Sole-survivor fixed point.**  If `x` is the only kept dart in its `p`-cycle, `deleteSet p S`
fixes `x`. -/
theorem deleteSet_fix_of_sole_survivor (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hsole : ∀ y : {d : D // d ∉ S}, p.SameCycle x.1 y.1 → y = x) :
    Equiv.Perm.deleteSet p S x = x := by
  apply Subtype.ext
  rw [Equiv.Perm.deleteSet_apply_coe]
  set n := Equiv.Perm.DeleteSet.firstOutside p S x with hn
  have hnotmem : (p ^ n) x.1 ∉ S := Equiv.Perm.DeleteSet.firstOutside_notMem p S x
  have hsc : p.SameCycle x.1 ((p ^ n) x.1) := ⟨n, rfl⟩
  have := hsole ⟨(p ^ n) x.1, hnotmem⟩ hsc
  exact congrArg Subtype.val this



/-- **Cauchy marked-sphere low active vertex, simple form.**  For a simple triangulated sphere
carrying an edge-invariant `±/0` signing with some nonzero edge, some active vertex has skip-zero
flip count `≤ 2`.  `Del := compDel M es d₀` extracts the seed's active component (connected,
`hconn`); branch on its edge count for `hFaceDeg` (no-digon, ≥2 edges) vs the single-edge
endpoint. -/
theorem cauchy_marked_sphere_low_active_vertex_simple
    (M : CombMap D) (hsphere : M.IsSphereMap) (hTri : M.FaceRegular 3) (hsimple : M.IsSimpleGraph)
    (es : D → EdgeSign) (hes : ∀ d, es (M.α d) = es d) (hnz : ∃ d, es d ≠ EdgeSign.zero) :
    ∃ d, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  obtain ⟨d₀, hd₀⟩ := hnz
  set Del := compDel M es d₀ with hDeldef
  set hsub := compDel_hsub M es hes hd₀ with hsubdef
  set A := keptMap M Del hsub with hAdef
  have hd₀kept : d₀ ∉ Del := by rw [hDeldef, mem_compDel]; exact not_not.2 (reached_refl M es d₀)
  set d₀' : {d : D // d ∉ Del} := ⟨d₀, hd₀kept⟩ with hd₀'def
  have hAsimple : A.IsSimpleGraph := keptMap_isSimpleGraph M hsimple Del hsub
  have hAconn : A.Connected := compDel_keptMap_connected M es hes hd₀
  -- branch on the kept edge count
  rcases Nat.lt_or_ge A.E 2 with hE | hE
  · -- E ≤ 1.  E ≥ 1 (the seed edge {d₀, α d₀} survives), so E = 1: single active edge
    have hElt2 : A.E < 2 := hE
    -- exactly 2 kept darts (card = 2 E < 4, and ≥ 2 since d₀', keptAlpha d₀' distinct)
    have h2E : 2 * A.E = Fintype.card {d : D // d ∉ Del} := A.two_mul_E_eq_card
    have hcardlt : Fintype.card {d : D // d ∉ Del} < 4 := by omega
    -- the two distinct kept darts d₀', keptAlpha d₀'
    have hαne : (keptAlpha M Del hsub) d₀' ≠ d₀' := by
      intro h
      apply M.α_no_fixed d₀
      have := congrArg Subtype.val h
      rwa [keptAlpha_apply_coe] at this
    have hcardge2 : 2 ≤ Fintype.card {d : D // d ∉ Del} := by
      have : ({d₀', (keptAlpha M Del hsub) d₀'} : Finset {d : D // d ∉ Del}).card ≤
          Fintype.card {d : D // d ∉ Del} := Finset.card_le_univ _
      rw [Finset.card_insert_of_notMem (by simp [hαne.symm]), Finset.card_singleton] at this
      omega
    -- so card = 2 (E = 1): the only kept darts are d₀' and keptAlpha d₀'
    have hcard2 : Fintype.card {d : D // d ∉ Del} = 2 := by omega
    -- d₀' is the sole kept dart in its M.σ-cycle (its α-partner is at a different vertex: no loop)
    have hsole : ∀ y : {d : D // d ∉ Del}, M.σ.SameCycle d₀'.1 y.1 → y = d₀' := by
      intro y hy
      -- y is one of the two kept darts
      have hmem : y ∈ ({d₀', (keptAlpha M Del hsub) d₀'} : Finset {d : D // d ∉ Del}) := by
        by_contra hnotmem
        have : 3 ≤ Fintype.card {d : D // d ∉ Del} := by
          have hsubset : ({d₀', (keptAlpha M Del hsub) d₀', y} :
              Finset {d : D // d ∉ Del}).card ≤ Fintype.card {d : D // d ∉ Del} :=
            Finset.card_le_univ _
          rw [show ({d₀', (keptAlpha M Del hsub) d₀', y} : Finset {d : D // d ∉ Del}).card = 3 from by
            rw [Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                refine ⟨hαne.symm, ?_⟩
                intro h; exact hnotmem (by rw [← h]; simp)),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_singleton]
                intro h; exact hnotmem (by rw [h]; simp)),
              Finset.card_singleton]] at hsubset
          exact hsubset
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · rfl
      · -- y = keptAlpha d₀' = α d₀; σ-same-cycle d₀ would be a loop
        exfalso
        have hsc : M.σ.SameCycle d₀ (M.α d₀) := by
          have hval : ((keptAlpha M Del hsub) d₀' : D) = M.α d₀ := keptAlpha_apply_coe M Del hsub d₀'
          rw [hval] at hy; exact hy
        have htail : M.tail d₀ = M.tail (M.α d₀) := Quotient.sound hsc
        rw [M.tail_alpha] at htail
        exact hsimple.no_loop d₀ htail
    -- deleteSet fixes d₀' ⟹ single-edge branch
    have hfix : (Equiv.Perm.deleteSet M.σ Del) d₀' = d₀' :=
      deleteSet_fix_of_sole_survivor M.σ Del d₀' hsole
    exact single_edge_low_active_vertex M es hd₀ hfix
  · -- ≥ 2 edges: no-digon hFaceDeg, then the modular assembly
    have hFaceDeg : ∀ R, 3 ≤ faceDeg A R :=
      three_le_faceDeg_of_connected_simple_twoEdge hAsimple hAconn hE
    exact compDel_low_active_vertex M es hsphere hes hd₀ hFaceDeg







end ProofsInTheBook.Ch13ComponentClose

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13ComponentClose
import ProofsInTheBook.Chapter13
-/
/- Source module: ProofsInTheBook.Ch13CauchyAssembly -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13CauchyAssembly

open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Chapter13

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- **The faithful Cauchy contradiction.**  Given the geometric input and the (separately proven)
combinatorial lemma — every nonzero ±/0 signing of a triangulated sphere has an ACTIVE vertex with ≤2
skip-zeros sign changes — every edge sign is zero (no dihedral angle differs ⟹ the polyhedra are
congruent).  The genuine `≥4` (from real links) collides with the combinatorial `≤2`. -/
theorem cauchy_no_nonzero_edgeSign {M : CombMap D}
    (C : CauchyMarkedTriangulatedSphere M)
    (hcomb : M.IsSphereMap → M.FaceRegular 3 →
      (∃ d, C.edgeSign d ≠ EdgeSign.zero) →
      ∃ d, ActiveVertex M C.edgeSign d ∧ vertexFlipCountSkipZeros M C.edgeSign d ≤ 2) :
    ∀ d, C.edgeSign d = EdgeSign.zero := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨d₀, hd₀⟩ := hnot
  obtain ⟨d, hdActive, hdLow⟩ := hcomb C.isSphere C.triangleFaces ⟨d₀, hd₀⟩
  have hdFour : 4 ≤ vertexFlipCountSkipZeros M C.edgeSign d := by
    rw [← C.vertexArm_signChanges_eq d hdActive]
    exact CauchyArmVertex.four_le_signChanges (C.vertexArm d hdActive)
  omega

/-- **The faithful Cauchy contradiction, unconditional.**  Same as `cauchy_no_nonzero_edgeSign` but
with the combinatorial lemma now DISCHARGED by `Ch13ComponentClose.cauchy_marked_sphere_low_active_vertex_simple`
(both residuals `hconn`/`hFaceDeg` closed clean-3) — the simplicity it needs is supplied by the
genuine `C.isSimple` field (Steinitz).  So: on a simple triangulated sphere with a genuine
per-active-vertex spherical-link signing, every edge sign is zero.  The geometric `≥4` (real links)
collides with the combinatorial `≤2`; no abstract `hcomb` hypothesis remains. -/
theorem cauchy_no_nonzero_edgeSign_final {M : CombMap D}
    (C : CauchyMarkedTriangulatedSphere M) :
    ∀ d, C.edgeSign d = EdgeSign.zero :=
  cauchy_no_nonzero_edgeSign C
    (fun hsphere hTri hnz =>
      Ch13ComponentClose.cauchy_marked_sphere_low_active_vertex_simple
        M hsphere hTri C.isSimple C.edgeSign C.edgeSign_inv hnz)

end ProofsInTheBook.Ch13CauchyAssembly

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT112
-/
/- Source module: ProofsInTheBook.Ch13LemmaII -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13LemmaII

open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT112











end ProofsInTheBook.Ch13LemmaII





end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalDiagCut
-/
/- Source module: ProofsInTheBook.Ch13SubArc -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalHingeCut ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain

namespace ProofsInTheBook.Ch13SubArc



















































end ProofsInTheBook.Ch13SubArc

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13LemmaII
import ProofsInTheBook.Ch13SubArc
-/
/- Source module: ProofsInTheBook.Ch13ArmVertex -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ArmVertex

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13LemmaII
open ProofsInTheBook.Ch13SubArc

















open scoped Classical









































end ProofsInTheBook.Ch13ArmVertex







end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13ArmVertex
-/
/- Source module: ProofsInTheBook.Ch13ArmVertexFull -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ArmVertexFull

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13LemmaII
open ProofsInTheBook.Ch13ArmVertex

open scoped Classical































end ProofsInTheBook.Ch13ArmVertexFull








end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalKernel
-/
/- Source module: ProofsInTheBook.Ch13VertexStar -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar





namespace VertexStar

























































end VertexStar

























end ProofsInTheBook.Ch13VertexStar




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13VertexStar
-/
/- Source module: ProofsInTheBook.Ch13Dihedral -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar

namespace VertexStar

variable (S : VertexStar)



/-- Scaling the projection axis by a nonzero scalar does not change `projOut`. -/
theorem projOut_smul_left {c : ℝ} (hc : c ≠ 0) (d x : E3) :
    projOut (c • d) x = projOut d x := by
  simp only [projOut, real_inner_smul_right, real_inner_smul_left, smul_smul]
  congr 2
  field_simp











/-- `tangentTo (edgeDir b) (edgeDir a)`, as a `projOut` of the *raw* directions, scaled by the
positive inverse norm `‖rawDir a‖⁻¹`. -/
theorem tangentTo_edgeDir_eq (a b : Fin (S.n + 1)) :
    tangentTo (S.edgeDir b) (S.edgeDir a)
      = ‖S.rawDir a‖⁻¹ • projOut (S.rawDir b) (S.rawDir a) := by
  rw [tangentTo, edgeDir_coe, edgeDir_coe,
    projOut_smul_left (ne_of_gt (S.inv_norm_pos b)) (S.rawDir b) _,
    projOut_smul (S.rawDir b) (‖S.rawDir a‖⁻¹) (S.rawDir a)]

/-- **Bridge B.**  The spherical joint angle of the vertex link equals the extrinsic ℝ³ dihedral
angle of the star along the corresponding middle edge.  A *theorem*: the dihedral is defined
independently of the link in `dihedral`, so this is not vacuous. -/
theorem jointAngle_vertexLink_eq_dihedral (i : Fin (S.n - 1)) :
    jointAngle S.vertexLink i = S.dihedral i := by
  -- Unfold `jointAngle ∘ vertexLink` to `sphAngle` of the three `edgeDir`s, then to `angle` of the
  -- two tangents.  The three indices coincide with `jIdx0/1/2`.
  rw [jointAngle]
  simp only [vertexLink_apply]
  rw [sphAngle]
  -- rewrite both tangents as scaled raw `projOut`s
  show InnerProductGeometry.angle
      (tangentTo (S.edgeDir (S.jIdx1 i)) (S.edgeDir (S.jIdx0 i)))
      (tangentTo (S.edgeDir (S.jIdx1 i)) (S.edgeDir (S.jIdx2 i))) = _
  rw [tangentTo_edgeDir_eq, tangentTo_edgeDir_eq]
  -- kill the two positive inverse-norm scalings
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (S.inv_norm_pos (S.jIdx0 i)),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (S.inv_norm_pos (S.jIdx2 i))]
  rfl

end VertexStar





end ProofsInTheBook.Ch13VertexStar



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13CauchyAssembly
import ProofsInTheBook.Ch13ArmVertexFull
import ProofsInTheBook.Ch13VertexStar
import ProofsInTheBook.Ch13Dihedral
import ProofsInTheBook.PlanarMapSimple
-/
/- Source module: ProofsInTheBook.Ch13Realization -/
section
set_option autoImplicit true




noncomputable section

open scoped Classical
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13 EdgeSign
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13Realization

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace List



end List































































theorem perm_of_dihedralRotated {α : Type*} {l m : List α}
    (h : List.DihedralRotated l m) : l.Perm m := by
  rcases h with hrot | hrev
  · exact hrot.perm
  · exact (List.reverse_perm l).symm.trans hrev.perm













/-- `jointAngle` is invariant under the trivial `Fin.cast` reindexing. -/
theorem jointAngle_reindex {n m : ℕ} (h : n = m) (A : Fin (m + 1) → S2)
    (i : Fin (n - 1)) :
    jointAngle (fun j : Fin (n + 1) => A (Fin.cast (by rw [h]) j)) i
      = jointAngle A (Fin.cast (by rw [h]) i) := by
  subst h
  simp



namespace ConvexPolytopeRealization

variable {M : CombMap D} (R : ConvexPolytopeRealization M)






























/-- **The Cauchy conclusion: every edge sign is zero (given a `ConvexPolytopeRealization`).**
No extra side-hypothesis beyond the realization datum `R`.  No dihedral angle differs
between the two congruent-faced realizations.  This is `cauchy_no_nonzero_edgeSign_final` applied to
`realization_marked`: the combinatorial low-active-vertex lemma is fully discharged (using the genuine
`isSimple` field, Steinitz), so no abstract `hcomb` hypothesis remains.  The geometric `≥4` (real
spherical links) collides with the combinatorial `≤2`. -/
theorem realization_all_edgeSign_zero :
    ∀ d, R.edgeSign d = EdgeSign.zero :=
  Ch13CauchyAssembly.cauchy_no_nonzero_edgeSign_final R.realization_marked



/-- All edge signs zero forces every link-angle difference to vanish: at each vertex the closed-link
real-sign list is the all-`zero` list (by `linkOrder` + `∀ d, edgeSign d = zero`), so each
`realSignToEdgeSign (linkDiff i) = zero`, hence each `linkDiff i = 0`. -/
theorem linkDiff_zero_of_edgeSign_zero (hzero : ∀ d, R.edgeSign d = EdgeSign.zero)
    (Q : M.Vertex) (i : Fin ((R.starP Q).n + 1)) :
    linkDiff (R.starP Q).vertexLink (R.linkQ Q) i = 0 := by
  let geom :=
    (List.ofFn (linkDiff (R.starP Q).vertexLink (R.linkQ Q))).map realSignToEdgeSign
  let comb := (M.σ.toList (R.dartRep Q)).map R.edgeSign
  have hperm : geom.Perm comb := (perm_of_dihedralRotated (R.linkOrder Q)).symm
  have hmem_geom : realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) ∈ geom := by
    apply List.mem_map.mpr
    exact ⟨linkDiff (R.starP Q).vertexLink (R.linkQ Q) i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
  have hmem_comb : realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) ∈ comb :=
    hperm.mem_iff.mp hmem_geom
  have hz : realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) = EdgeSign.zero := by
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hmem_comb
    rw [← ha, hzero a]
  exact (realSignToEdgeSign_eq_zero_iff _).mp hz

/-- Equal corresponding link joint angles at each vertex. -/
theorem jointAngle_eq_of_edgeSign_zero (hzero : ∀ d, R.edgeSign d = EdgeSign.zero)
    (Q : M.Vertex) (i : Fin ((R.starP Q).n - 1)) :
    jointAngle (R.starP Q).vertexLink i = jointAngle (R.linkQ Q) i := by
  have hk := R.linkDiff_zero_of_edgeSign_zero hzero Q ⟨i.val + 1, by have := i.isLt; omega⟩
  rw [linkDiff_interior] at hk
  unfold jointDiff at hk
  linarith

/-- **`realization_rigid` — the headline (given a `ConvexPolytopeRealization`).**  Conditional on the
realization datum `R` (the ℝ³ input, out of scope); no extra side-hypothesis.  Every corresponding dihedral angle of the
two congruent-faced convex-polytope realizations agrees — Cauchy's sign-machinery content, with the
combinatorial low-active-vertex lemma already discharged via the genuine `isSimple` field.  The
`Fin.cast` reindexes the `Q`-realization joint onto the `P` index range (the two realizations have the
same incident-edge count, `R.hnn`). -/
theorem realization_rigid
    (Q : M.Vertex) (i : Fin ((R.starP Q).n - 1)) :
    (R.starP Q).dihedral i
      = (R.starQ Q).dihedral (Fin.cast (by rw [R.hnn Q]) i) := by
  have hzero := R.realization_all_edgeSign_zero
  -- link joint angles agree
  have hj := R.jointAngle_eq_of_edgeSign_zero hzero Q i
  -- Bridge B on the P-star: jointAngle (starP Q).vertexLink i = (starP Q).dihedral i
  rw [VertexStar.jointAngle_vertexLink_eq_dihedral] at hj
  -- on the Q side: jointAngle (linkQ Q) i = jointAngle (starQ Q).vertexLink (cast i) = (starQ Q).dihedral (cast i)
  rw [show R.linkQ Q = (fun j : Fin ((R.starP Q).n + 1) =>
        (R.starQ Q).vertexLink (Fin.cast (by rw [R.hnn Q]) j)) from rfl] at hj
  rw [jointAngle_reindex (R.hnn Q).symm (R.starQ Q).vertexLink i] at hj
  rw [VertexStar.jointAngle_vertexLink_eq_dihedral] at hj
  exact hj

end ConvexPolytopeRealization

end ProofsInTheBook.Ch13Realization



namespace ProofsInTheBook.Ch13Realization









end ProofsInTheBook.Ch13Realization








end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13ComponentClose
import ProofsInTheBook.SphericalRotation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fin.Tuple.Reflection
-/
/- Source module: ProofsInTheBook.ZinanCh13Euclidean -/
section
set_option autoImplicit true




noncomputable section

open scoped Classical
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.Ch13Euclidean



































































































-- The regular tetrahedron satisfies the reverse-`σ` rotation-faithfulness convention.


-- The regular tetrahedron satisfies the face-local outward-orientation convention.


















































end ProofsInTheBook.Ch13Euclidean

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh13Euclidean
import ProofsInTheBook.Ch13VertexStar
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.SphericalRotation
import Mathlib.Data.Fin.Rev
-/
/- Source module: ProofsInTheBook.ZinanCh13EuclLink -/
section
set_option autoImplicit true




noncomputable section

set_option maxHeartbeats 3000000

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.Ch13EuclLink
































































































































namespace VertexLinkGeometry




















end VertexLinkGeometry



















































































end ProofsInTheBook.Ch13EuclLink

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.SphericalCongruence
import ProofsInTheBook.Ch13ArmVertexFull
-/
/- Source module: ProofsInTheBook.ZinanCh13SphAngle -/
section
set_option autoImplicit true




noncomputable section

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13ArmVertexFull (linkAngle)
open ProofsInTheBook.SphericalKernel
  (S2 ShortArc tangentTo tangentTo_eq tangentTo_eq_zero_iff jointAngle sphAngle)
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.Ch13SphAngle










































































































end ProofsInTheBook.Ch13SphAngle

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13VertexStar
-/
/- Source module: ProofsInTheBook.Ch13LinkSides -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13VertexStar

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel



end ProofsInTheBook.Ch13VertexStar

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13ArmVertex
-/
/- Source module: ProofsInTheBook.Ch13SubArcWrap -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.Ch13SubArc
open ProofsInTheBook.Ch13ArmVertex

namespace ProofsInTheBook.Ch13SubArcWrap















































end ProofsInTheBook.Ch13SubArcWrap







end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh13SphAngle
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13LinkSides
import ProofsInTheBook.Ch13SubArcWrap
import Mathlib.Geometry.Euclidean.Triangle
-/
/- Source module: ProofsInTheBook.ZinanCh13Cauchy3D -/
section
set_option autoImplicit true




noncomputable section

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.Ch13Realization
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13SubArc
open ProofsInTheBook.Ch13SubArcWrap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar

namespace VertexStar





end VertexStar

end ProofsInTheBook.Ch13VertexStar

namespace ProofsInTheBook.Ch13Cauchy3D

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}





namespace ConvexEuclideanPolyhedron











end ConvexEuclideanPolyhedron



































































































































































namespace ListCyclicOrder



















end ListCyclicOrder

















































































































namespace RotTwoBlockCert




























end RotTwoBlockCert























































































theorem chapter13_euclidean
    (P Q : ConvexEuclideanPolyhedron M)
    (hcong : CongruentFaces P.toTri Q.toTri)
    (v : M.Vertex)
    (i : Fin ((rotatedStarP P.toTri (fun w => P.linkGeomAt w)
      (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).n - 1)) :
    (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral i =
      (rotatedStarQ P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral
        (Fin.cast (by
          change (P.linkGeomAt v).n - 1 = (Q.linkGeomAt v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P.toTri Q.toTri
              (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w) v).symm) i) := by
  simpa [convexPolytopeRealization_of_convexEuclidean] using
    (convexPolytopeRealization_of_convexEuclidean P Q hcong).realization_rigid v i
















































end ProofsInTheBook.Ch13Cauchy3D

end
end


set_option autoImplicit true
open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.Ch13Realization
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13SubArc
open ProofsInTheBook.Ch13SubArcWrap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.Ch13Cauchy3D
variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

theorem solution
    (P Q : ConvexEuclideanPolyhedron M)
    (hcong : CongruentFaces P.toTri Q.toTri)
    (v : M.Vertex)
    (i : Fin ((rotatedStarP P.toTri (fun w => P.linkGeomAt w)
      (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).n - 1)) :
    (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral i =
      (rotatedStarQ P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral
        (Fin.cast (by
          change (P.linkGeomAt v).n - 1 = (Q.linkGeomAt v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P.toTri Q.toTri
              (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w) v).symm) i) :=
  chapter13_euclidean P Q hcong v i
