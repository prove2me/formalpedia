-- Prove2me | Definitions.Def_P2MAssembly_Chapter13V2_Part3
-- name    : P2MAssembly_Chapter13V2_Part3
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T20:37:26.795247+00:00
-- url     : https://prove2.me/theorems/5a12202c-8b36-42a0-a367-47c137f718ca
-- title:
--   Monitored spherical openings and boundary configurations
-- statement:
--   This part defines admissible monitored opening families and their supremum parameters, together with target-reaching, support-stopping and base-stopping conditions. It includes reversed and reflected spherical arms, interval-wrap data, tail-fold boundary conditions and strict diagonal-support predicates. The retained proofs organize progress and boundary cases in the arm comparison argument. Conditions described by these intermediate predicates remain conditions; their names do not assert that all such configurations are realizable.
-- source:
--   Exact reviewed local source: proof_in_the_book commit 873d52e0c88cd351f594221e70c3c5b3559777a9, ProofsInTheBook/ZinanCh13Cauchy3D.lean:4470 (headline), :96 (ConvexEuclideanPolyhedron), :143 (edge-length congruence), :1157 (adaptive offset), :3467 (rotated stars); ProofsInTheBook/ZinanCh13Euclidean.lean:46 (realization) and :115 (face orientation). These staged files match git show at that local commit. PUBLIC SOURCE GAP: the raw GitHub URL for this commit returned HTTP 404; the older public commit 88d88d141768cded75e782c525ef1bf04b8fe220 differs in these two files and is not an exact source citation for this artifact. Unchanged supporting definitions are publicly byte-verified at https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L24 and https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapSimple.lean#L97. Repository topic: Cauchy rigidity; no edition-specific chapter mapping asserted.

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
import Definitions.Def_P2MAssembly_Chapter13V2_Part1
import Definitions.Def_P2MAssembly_Chapter13V2_Part2

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



/-- **The hemisphere-free monitored family `WBS`** (design §7).  Three member classes, all opening by
`-θ` (the widening direction):
* `inl (inl c)` — the non-incident support constraint `θ ↦ supportConstraint A K c (-θ)`;
* `inl (inr ())` — the joint slack `θ ↦ jointAngle B k − openedInteriorJointAngle A k (-θ)`;
* `inr ()` — the base cap support `baseCapSupportW A k` (already `-θ`).

Indexed by `(NonIncident n ⊕ Unit) ⊕ Unit`.  **No hemisphere member.** -/
def monitoredFamilyWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    (NonIncident n ⊕ Unit) ⊕ Unit → ℝ → ℝ
  | Sum.inl (Sum.inl c) => fun θ => supportConstraint A (openingAxis k) c (-θ)
  | Sum.inl (Sum.inr ()) => fun θ => jointAngle B k - openedInteriorJointAngle A k (-θ)
  | Sum.inr () => baseCapSupportW A k

/-- Each `WBS`-family member is continuous in `θ`.  Supports and slack are the `W`-family members
precomposed with the continuous negation (`continuous_supportConstraint`, `continuous_openedInteriorJointAngle`),
the base member is `continuous_baseCapSupportW`. -/
theorem continuous_monitoredFamilyWBS {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    ∀ o, Continuous (monitoredFamilyWBS A B k o) := by
  rintro ((c | ⟨⟩) | ⟨⟩)
  · exact (continuous_supportConstraint A (openingAxis k) c).comp continuous_neg
  · exact continuous_const.sub ((continuous_openedInteriorJointAngle hka hkt).comp continuous_neg)
  · exact continuous_baseCapSupportW A k

/-- The `WBS` admissible supremum `δ*_WBS := sSup {θ ∈ [0,π] : ∀ o, 0 ≤ monitoredFamilyWBS … o θ}`. -/
def monitoredSupWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : ℝ :=
  sSup (admissibleSet (monitoredFamilyWBS A B k) Real.pi)



/-- **Init admissibility at `θ = 0`.**  Supports `≥ 0` (`edge_support`), the joint slack `≥ 0` (from the
deficit `jointAngle A k < jointAngle B k`), and the base support `≥ 0` (the banked convex base orientation
`orientedDatum_interior`).  At `θ = 0` the support/slack members are the unopened arm's data (`-0 = 0`,
`openedInteriorJointAngle A k 0 = jointAngle A k`), the base member is the unopened base support. -/
theorem monitoredFamilyWBS_zero_nonneg {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hkdef : jointAngle A k < jointAngle B k) :
    ∀ o, 0 ≤ monitoredFamilyWBS A B k o 0 := by
  rintro ((c | ⟨⟩) | ⟨⟩)
  · -- support member: `supportConstraint A K c (-0) = supportConstraint A K c 0 ≥ 0`.
    show 0 ≤ supportConstraint A (openingAxis k) c (-(0 : ℝ))
    rw [neg_zero, supportConstraint_apply, openTail_zero_angle]
    exact hA.closed_convex.edge_support c.1.1 c.1.2
  · -- slack member: `jointAngle B k − openedInteriorJointAngle A k (-0) = jointAngle B k − jointAngle A k ≥ 0`.
    show 0 ≤ jointAngle B k - openedInteriorJointAngle A k (-(0 : ℝ))
    rw [neg_zero, openedInteriorJointAngle_zero]
    linarith
  · -- base member at `0`: `sOrient (A 0)(A K)(rotS2 (A K) 0 (A last)) = sOrient (A 0)(A K)(A last) ≥ 0`.
    show 0 ≤ baseCapSupportW A k 0
    obtain ⟨hK0, hKn⟩ := openingAxis_interior k
    have hrot0 : rotS2 (A (openingAxis k)) (-(0 : ℝ)) (A (Fin.last n)) = A (Fin.last n) := by
      apply S2.ext; rw [rotS2_coe, neg_zero, rot_zero]
    show 0 ≤ sOrient (A 0) (A (openingAxis k)) (rotS2 (A (openingAxis k)) (-(0 : ℝ)) (A (Fin.last n)))
    rw [hrot0]
    exact orientedDatum_interior hA hK0 hKn

/-- **The `WBS` admissible supremum is `WBS`-admissible** (closed nonempty bounded family). -/
theorem monitoredSupWBS_mem {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k ∈ admissibleSet (monitoredFamilyWBS A B k) Real.pi :=
  sSup_mem_admissibleSet (continuous_monitoredFamilyWBS hka hkt) Real.pi_nonneg
    (monitoredFamilyWBS_zero_nonneg hA hkdef)

/-- `δ*_WBS ∈ [0, π]`. -/
theorem monitoredSupWBS_mem_Icc {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k ∈ Set.Icc (0 : ℝ) Real.pi :=
  (monitoredSupWBS_mem hA hka hkt hkdef).1



/-- **Closure (supports `≥ 0` at `δ*_WBS`)**, support form on the opened triple of `A'_WBS`. -/
theorem supportWBS_sOrient_nonneg {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) := by
  intro i j hji hji1
  have hmem := monitoredSupWBS_mem hA hka hkt hkdef
  have := hmem.2 (Sum.inl (Sum.inl (⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n)))
  simp only [monitoredFamilyWBS, supportConstraint_apply] at this
  exact this

/-- **Closure (joint slack `≥ 0` at `δ*_WBS`)**: the opened interior joint is `≤ jointAngle B k`. -/
theorem openedInteriorJoint_le_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) ≤ jointAngle B k := by
  have hmem := monitoredSupWBS_mem hA hka hkt hkdef
  have := hmem.2 (Sum.inl (Sum.inr ()))
  simp only [monitoredFamilyWBS] at this
  linarith





/-- **Every `WBS`-admissible `θ` lies in `[0, jointAngle B k − jointAngle A k]`.**  Port of
`ZinanFFCT37.admissibleW_le_deficit`, re-instantiated on the `WBS` joint-witness support member and the
`WBS` slack member (both present in the hemisphere-free family). -/
theorem admissibleWBS_le_deficit {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    {θ : ℝ} (hθadm : θ ∈ admissibleSet (monitoredFamilyWBS A B k) Real.pi) :
    θ ≤ jointAngle B k - jointAngle A k := by
  obtain ⟨⟨hθ0, hθπ⟩, hmem⟩ := hθadm
  -- joint-witness support ≥ 0 (it is a `WBS` support member).
  have hsupp : 0 ≤ supportConstraint A (openingAxis k) (jointWitness k) (-θ) := by
    have := hmem (Sum.inl (Sum.inl (jointWitness k)))
    simpa only [monitoredFamilyWBS] using this
  rw [supportConstraint_jointWitness_neg, support_openNeg_eq_sin hA hka hkt] at hsupp
  -- norms positive ⟹ `sin (γ + θ) ≥ 0`.
  have hunz : tangentTo (A (openingAxis k)) (jointPrev A k) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hka
  have hwnz : tangentTo (A (openingAxis k)) (jointNext A k) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hkt
  have hup : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (jointNext A k)‖ := norm_pos_iff.2 hwnz
  have hsin : 0 ≤ Real.sin (jointAngle A k + θ) := by
    by_contra hneg
    push_neg at hneg
    have : ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
        * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖ * Real.sin (jointAngle A k + θ) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hup hwp) hneg
    linarith
  -- `γ + θ ∈ [0, 2π)` and `sin ≥ 0` ⟹ `γ + θ ≤ π` (the additive branch).
  have hγ0 : 0 ≤ jointAngle A k := by
    rw [show jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) by
      simp only [jointAngle, jointPrev, jointNext, openingAxis]]
    exact sphAngle_nonneg _ _ _
  have hγlt : jointAngle A k < Real.pi := strict_jointAngle_lt_pi hA k
  have hbranch : jointAngle A k + θ ≤ Real.pi := by
    by_contra hgt
    push_neg at hgt
    set t : ℝ := jointAngle A k + θ - Real.pi with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    have htlt : t < Real.pi := by rw [ht]; linarith [hγlt, hθπ]
    have hsin_t : Real.sin (jointAngle A k + θ) = - Real.sin t := by
      rw [show jointAngle A k + θ = Real.pi + t by rw [ht]; ring, Real.sin_add, Real.sin_pi,
        Real.cos_pi]
      ring
    have hpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htlt
    rw [hsin_t] at hsin; linarith
  -- on the branch, the opened joint equals `γ + θ`; slack ≥ 0 pins `γ + θ ≤ jointAngle B k`.
  have hopened : openedInteriorJointAngle A k (-θ) = jointAngle A k + θ :=
    openedNegJointAngle_eq_add hA hka hkt hθ0 hbranch
  have hslack : 0 ≤ jointAngle B k - openedInteriorJointAngle A k (-θ) := by
    have := hmem (Sum.inl (Sum.inr ()))
    simpa only [monitoredFamilyWBS] using this
  rw [hopened] at hslack
  linarith

/-- **`δ*_WBS ≤ jointAngle B k − jointAngle A k`.** -/
theorem monitoredSupWBS_le_deficit {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k ≤ jointAngle B k - jointAngle A k :=
  admissibleWBS_le_deficit hA hka hkt (monitoredSupWBS_mem hA hka hkt hkdef)

/-- **`δ*_WBS < π`.**  The deficit `jointAngle B k − jointAngle A k < π` (strict `B`, `γ ≥ 0`). -/
theorem monitoredSupWBS_lt_pi {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k < Real.pi := by
  have hub := monitoredSupWBS_le_deficit hA hka hkt hkdef
  have hγ0 : 0 ≤ jointAngle A k := by
    rw [show jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) by
      simp only [jointAngle, jointPrev, jointNext, openingAxis]]
    exact sphAngle_nonneg _ _ _
  have hBlt : jointAngle B k < Real.pi := strict_jointAngle_lt_pi hB k
  linarith

/-- **The base cap at the `WBS` supremum** (`GlueWBaseCap` for `δ*_WBS`): `δ*_WBS + γbase ≤ π`.  The `WBS`
supremum is `WBS`-admissible, so the base member is `≥ 0`, hence (norms positive, `γbase < π`, `δ*_WBS ≤ π`)
`admissibleWB_baseCap`'s sine-branch argument closes the cap.  Mirror of FFCT41's `GlueWBaseCap_at_supWB`. -/
theorem GlueWBaseCap_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k
      + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi := by
  obtain ⟨hbase0, hbaseLast⟩ :=
    shortArc_interior_base hA (openingAxis_interior k).1 (openingAxis_interior k).2
  obtain ⟨hIcc, hmemfun⟩ := monitoredSupWBS_mem hA hka hkt hkdef
  -- the sine-branch argument: base member `≥ 0` ⟹ `sin (γbase + δ*) ≥ 0` ⟹ cap.
  set γ : ℝ := sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) with hγ
  set θ : ℝ := monitoredSupWBS A B k with hθ
  obtain ⟨hθ0, hθπ⟩ := hIcc
  have hbase : 0 ≤ baseCapSupportW A k θ := by simpa only [monitoredFamilyWBS] using hmemfun (Sum.inr ())
  rw [baseSupport_openNeg_eq_sin hA k hbase0 hbaseLast, ← hγ] at hbase
  have hunz : tangentTo (A (openingAxis k)) (A 0) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hbase0
  have hwnz : tangentTo (A (openingAxis k)) (A (Fin.last n)) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hbaseLast
  have hup : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (A 0)‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖ := norm_pos_iff.2 hwnz
  have hsin : 0 ≤ Real.sin (γ + θ) := by
    by_contra hneg
    push_neg at hneg
    have : ‖tangentTo (A (openingAxis k)) (A 0)‖
        * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖ * Real.sin (γ + θ) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hup hwp) hneg
    linarith
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact sphAngle_nonneg _ _ _
  have hγlt : γ < Real.pi := base_sphAngle_lt_pi hA k
  by_contra hgt
  push_neg at hgt
  set t : ℝ := γ + θ - Real.pi with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have htlt : t < Real.pi := by rw [ht]; linarith [hγlt, hθπ]
  have hsin_t : Real.sin (γ + θ) = - Real.sin t := by
    rw [show γ + θ = Real.pi + t by rw [ht]; ring, Real.sin_add, Real.sin_pi, Real.cos_pi]
    ring
  have hpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htlt
  rw [hsin_t] at hsin; linarith



/-- The REACH predicate at the `WBS` supremum: the opened-by-`-δ*_WBS` interior joint reaches `B`'s value. -/
def ReachWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : Prop :=
  openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) = jointAngle B k

/-- The SUPPORT-STUCK predicate at the `WBS` supremum: a non-incident support of the opened-by-`-δ*_WBS`
arm vanishes.  (No hemisphere disjunct — the hemisphere members were dropped.) -/
def SupportStuckWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : Prop :=
  ∃ c : NonIncident n,
    supportConstraint A (openingAxis k) c (-(monitoredSupWBS A B k)) = 0

/-- The BASE-STUCK predicate at the `WBS` supremum: the base monitor vanishes — `sin (γbase + δ*_WBS) = 0`. -/
def BaseStuckWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : Prop :=
  baseCapSupportW A k (monitoredSupWBS A B k) = 0

/-- **The `WBS` boundary trichotomy** (here a tetrachotomy *without* a hemi branch).  At `δ*_WBS`: either
`δ*_WBS = π`, or `ReachWBS`, or `SupportStuckWBS`, or `BaseStuckWBS`.  The generic `reach_or_stuck` engine;
the CAP branch is killed downstream by `monitoredSupWBS_lt_pi`.  **No hemisphere-stuck branch exists.** -/
theorem opening_boundary_trichotomyWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k = Real.pi ∨
      ReachWBS A B k ∨ SupportStuckWBS A B k ∨ BaseStuckWBS A B k := by
  rcases reach_or_stuck (continuous_monitoredFamilyWBS hka hkt) Real.pi_nonneg
      (monitoredFamilyWBS_zero_nonneg hA hkdef) with hcap | ⟨o, ho⟩
  · exact Or.inl hcap
  · rcases o with (c | ⟨⟩) | ⟨⟩
    · -- a support constraint vanishes: SUPPORT-STUCK.
      refine Or.inr (Or.inr (Or.inl ⟨c, ?_⟩))
      simpa only [monitoredFamilyWBS, monitoredSupWBS] using ho
    · -- the joint slack vanishes: REACH.
      refine Or.inr (Or.inl ?_)
      have hslack : monitoredFamilyWBS A B k (Sum.inl (Sum.inr ())) (monitoredSupWBS A B k) = 0 := ho
      simp only [monitoredFamilyWBS] at hslack
      unfold ReachWBS
      linarith
    · -- the base monitor vanishes: BASE-STUCK.
      refine Or.inr (Or.inr (Or.inr ?_))
      have : monitoredFamilyWBS A B k (Sum.inr ()) (monitoredSupWBS A B k) = 0 := ho
      simpa only [monitoredFamilyWBS, monitoredSupWBS] using this

/-- **The `WBS` honest clause (ii): `¬ SupportStuckWBS → ReachWBS ∨ BaseStuckWBS`.**  The CAP branch is
impossible (`monitoredSupWBS_lt_pi`), SUPPORT-STUCK is excluded, leaving REACH or BASE-STUCK.  (There is no
hemi branch to dispose of — the design's payoff for dropping the hemisphere monitors.) -/
theorem glueWBS_clause_ii {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hnotStuck : ¬ SupportStuckWBS A B k) :
    ReachWBS A B k ∨ BaseStuckWBS A B k := by
  rcases opening_boundary_trichotomyWBS hA hka hkt hkdef with hcap | hreach | hstuck | hbase
  · exact absurd hcap (ne_of_lt (monitoredSupWBS_lt_pi hA hB hka hkt hkdef))
  · exact Or.inl hreach
  · exact absurd hstuck hnotStuck
  · exact Or.inr hbase

/-- **Clause (i) at `δ*_WBS`** — UNCONDITIONAL (the cap is discharged by `GlueWBaseCap_at_supWBS`).  Opening
by `-δ*_WBS` does not decrease the endpoint, since `δ*_WBS + γbase ≤ π` holds by admissibility.  Mirror of
FFCT41's `glueWB_clause_i`. -/
theorem glueWBS_clause_i {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) := by
  have hδ0 : 0 ≤ monitoredSupWBS A B k := (monitoredSupWBS_mem_Icc hA hka hkt hkdef).1
  exact endpt_openTail_interior_mono_neg hA k hδ0 (GlueWBaseCap_at_supWBS hA hka hkt hkdef)



/-- **Base-stuck forces a vanishing non-incident support of `A'_WBS`** — re-instantiation of FFCT42's
`baseStuck_forces_vanishingSupport` at the `WBS` sup.  The base diagonal zero **is** the wraparound
non-incident support zero at `(last, K)` (the `det3` cyclic identity, family-independent). -/
theorem baseStuckWBS_forces_vanishingSupport {n : ℕ} {A B : Fin (n + 1) → S2} (k : Fin (n - 1))
    (hbase : BaseStuckWBS A B k) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) = 0 := by
  -- `BaseStuckWBS` unfolds to `baseCapSupportW A k δ*_WBS = 0`; FFCT42's `baseStuck_eq_openedDiagonal`
  -- (free in `δ`) turns this into the opened diagonal `(0,K,last)` zero, and the cyclic identity
  -- `baseDiagonal_zero_is_wrapEdgeSupport_zero` (free in `δ`) yields the wrap-edge `(last,K)` payload.
  have hdiag : sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (openingAxis k))
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n)) = 0 := by
    rw [← baseStuck_eq_openedDiagonal]; exact hbase
  exact baseDiagonal_zero_is_wrapEdgeSupport_zero A k (monitoredSupWBS A B k) hdiag

/-- **The base-stuck progress residual at `δ*_WBS`** (design §11).  Stated in the same shape as FFCT41's
`BaseStuckProgressW`, but at the `WBS` sup and **without** the false-shaped hemi monitoring.  Unlike FFCT41,
this is a *theorem*, not a named residual: the FFCT42 cyclic shortcut discharges it by taking the
vanishing-support disjunct (the base diagonal zero **is** the wrap-edge non-incident support zero). -/
def BaseStuckProgressWBS : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
      BaseStuckWBS A B k →
        ReachWBS A B k ∨
        ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
            (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
            (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) = 0

/-- **`BaseStuckProgressWBS` holds** — Brick 7, the FFCT42 port DISCHARGED.  A base-stuck `WBS` supremum
always makes recursion-ready progress by taking the **vanishing-support** disjunct via the cyclic identity
(`baseStuckWBS_forces_vanishingSupport`).  `ReachWBS` is never needed.  Unconditional — no
`OpenedClosingEdge*`, no `SupportStuckMargins`, no straightening completion, no sub-arm IH.  This is the
honest analogue of FFCT42's `BaseStuckProgressW_holds`, but for the hemisphere-free family. -/
theorem BaseStuckProgressWBS_holds : BaseStuckProgressWBS := by
  intro n A B _hA _hB k _hkdef hbase
  exact Or.inr (baseStuckWBS_forces_vanishingSupport k hbase)











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



/-- **The endpoint of a strict convex arm is positive.**  `endpt A = sDist (A 0)(A last)`; the wraparound
edge `(last, last + 1)` of the closed polygon is short (`StrictConvexSphArm`'s `edge_short`), and
`last + 1 = 0` (`ZinanFFCT42.lastAddOne_eq_zero`), so `A last ≠ A 0`, whence `0 < sDist (A 0)(A last)`. -/
theorem strict_arm_endpt_pos {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) :
    0 < endpt A := by
  -- the wraparound edge `(last, last + 1 = 0)` is short ⟹ `A last ≠ A 0`.
  have hwrap : A (Fin.last n) ≠ A (Fin.last n + 1) := base_consecutive_ne hA (Fin.last n)
  rw [lastAddOne_eq_zero] at hwrap
  have hne : A 0 ≠ A (Fin.last n) := fun h => hwrap h.symm
  -- `endpt A = sDist (A 0)(A last) > 0`.
  exact sDist_pos_of_ne hne

















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



/-- **Margins-free open hemisphere from weak supports + open joints + short edges.**  For a closed chain
`P : Fin (n+1) → S2` (`2 ≤ n`) with cyclic short-arc edges (`hside`), weak (`≥ 0`) non-incident edge
supports (`hsupp`), and all interior joints in `(0, π)` (`hjopen`), there is a *unit* normal `h'`
strictly positive against every vertex: `∃ h', ‖h'‖ = 1 ∧ ∀ r, 0 < ⟪h', P r⟫`.  **No hemisphere-margin
hypothesis is consumed** — the genuine replacement for FFCT44's tilt route, which needed a weak-margin
base normal the WBS family does not supply. -/
theorem openHemisphere_of_weakSupports_jointOpen_full {n : ℕ} {P : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hside : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1)))
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j))
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    ∃ h' : E3, ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ) := by
  classical
  -- The full vertex image set.
  set s : Finset E3 := (Finset.univ : Finset (Fin (n + 1))).image (fun r => ((P r : S2) : E3))
    with hs
  have hmem_iff : ∀ v, v ∈ s ↔ ∃ m, ((P m : S2) : E3) = v := by
    intro v
    rw [hs, Finset.mem_image]
    constructor
    · rintro ⟨m, _hm, rfl⟩; exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩; exact ⟨m, Finset.mem_univ _, rfl⟩
  by_cases h0 : (0 : E3) ∈ convexHull ℝ (s : Set E3)
  · -- `0 ∈ hull`: derive a common edge-plane axis and contradict the FFCT44 collapse kernel.
    exfalso
    rw [Finset.mem_convexHull'] at h0
    obtain ⟨w, hw0, hw1, hwsum⟩ := h0
    -- For every edge `i` and every member `v`, `w v * det3 (P i)(P i+1) v ≥ 0` (weak supports).
    have hterm_nonneg : ∀ (i : Fin (n + 1)) (v : E3), v ∈ s →
        0 ≤ w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i v hv
      obtain ⟨m, rfl⟩ := (hmem_iff v).mp hv
      by_cases hmi : m = i
      · subst hmi; rw [show det3 (P m : E3) (P (m + 1) : E3) (P m : E3) = 0 from by
          simp only [det3]; ring, mul_zero]
      · by_cases hmi1 : m = i + 1
        · subst hmi1; rw [show det3 (P i : E3) (P (i + 1) : E3) (P (i + 1) : E3) = 0 from by
            simp only [det3]; ring, mul_zero]
        · exact mul_nonneg (hw0 _ hv)
            (le_trans (le_of_eq rfl) (hsupp i m (by simpa [eq_comm] using hmi)
              (by simpa [eq_comm] using hmi1)))
    -- The edge functional pushed through the convex combination is `0`.
    have hedge_zero : ∀ i : Fin (n + 1),
        (0 : ℝ) = ∑ v ∈ s, w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i
      have hkey := det3_edge_centerSum (P i : E3) (P (i + 1) : E3) s w
      rw [hwsum] at hkey
      rw [show det3 (P i : E3) (P (i + 1) : E3) (0 : E3) = 0 from by simp [det3]] at hkey
      exact hkey
    have hterm_zero : ∀ i : Fin (n + 1), ∀ v ∈ s,
        w v * det3 (P i : E3) (P (i + 1) : E3) v = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => hterm_nonneg i v hv)).mp
        (hedge_zero i).symm
    -- Pick a positive-weight member `v₀`.
    have hexists_pos : ∃ v ∈ s, 0 < w v := by
      by_contra hnone
      push_neg at hnone
      have : ∑ v ∈ s, w v = 0 :=
        Finset.sum_eq_zero (fun v hv => le_antisymm (hnone v hv) (hw0 v hv))
      rw [hw1] at this; exact one_ne_zero this
    obtain ⟨v0, hv0s, hv0pos⟩ := hexists_pos
    obtain ⟨r0, hv0eq⟩ := (hmem_iff v0).mp hv0s
    -- `z := P r0` is a common edge-plane axis.
    have hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (P r0 : E3) = 0 := by
      intro i
      have := hterm_zero i v0 hv0s
      rcases mul_eq_zero.mp this with hw | hd
      · exact absurd hw (ne_of_gt hv0pos)
      · rw [hv0eq]; exact hd
    exact commonLine_collapse_forces_flat_joint hn hside hallplanes hjopen
  · -- `0 ∉ hull`: separation gives the strict hemisphere normal directly; normalize to unit length.
    obtain ⟨t, ht⟩ := exists_inner_pos_of_zero_notMem_convexHull s.finite_toSet h0
    have htpos : ∀ r : Fin (n + 1), 0 < (⟪t, (P r : E3)⟫ : ℝ) := by
      intro r
      have hrmem : ((P r : S2) : E3) ∈ s := by rw [hmem_iff]; exact ⟨r, rfl⟩
      exact ht _ hrmem
    -- `t ≠ 0` (it has a strictly positive inner product against `P 0`); normalize.
    have htne : t ≠ 0 := by
      intro h
      have := htpos ⟨0, by omega⟩
      rw [h, inner_zero_left] at this
      exact lt_irrefl _ this
    have htnorm : 0 < ‖t‖ := norm_pos_iff.mpr htne
    refine ⟨(‖t‖⁻¹ : ℝ) • t, ?_, fun r => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]; field_simp
    · rw [inner_smul_left]
      simp only [RCLike.conj_to_real]
      exact mul_pos (by positivity) (htpos r)



/-- **Brick 4 — the open hemisphere at the WBS supremum.**  At `A'_WBS := openTail A K (-δ*_WBS)`, from
the WBS closure supports (`≥ 0`), the opened ShortArc edges (`hedge`), and joints-in-`(0, π)` (`hjopen`),
there is a *unit* normal `h'` strictly positive against every vertex.  **Margins-free** (no fixed-`h₀`
margins are monitored or consumed) — this is the §15.2 keystone replacing all fixed-hemi residuals. -/
theorem openHemisphere_at_WBS_sup {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hedge : ∀ i : Fin (n + 1),
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1)))
    (hjopen : ∀ r : Fin (n - 1),
      0 < jointAngle (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) r ∧
        jointAngle (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) r < Real.pi) :
    ∃ h' : E3, ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1),
      0 < (⟪h', ((openTail A (openingAxis k) (-(monitoredSupWBS A B k)) r : S2) : E3)⟫ : ℝ) := by
  have hn : 2 ≤ n := hA.two_le
  exact openHemisphere_of_weakSupports_jointOpen_full hn hedge
    (supportWBS_sOrient_nonneg hA hka hkt hkdef) hjopen



/-- A point pair with `0 < sDist < π` is a `ShortArc` (the converse of `ShortArc.sDist_pos`/`sDist_lt_pi`).
Distinctness from `sDist_eq_zero_iff`; non-antipodality because `(p : E3) = -(q : E3)` forces
`sInner p q = -1`, hence `sDist p q = arccos(-1) = π`, contradicting `sDist p q < π`. -/
theorem shortArc_of_sDist_pos_lt_pi {p q : S2}
    (hpos : 0 < sDist p q) (hlt : sDist p q < Real.pi) : ShortArc p q := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · rw [sDist_eq_zero_iff.2 he] at hpos; exact lt_irrefl 0 hpos
  · -- `(p : E3) = -(q : E3)` ⟹ `sInner p q = -1` ⟹ `sDist = π`.
    have hcos : sInner p q = -1 := by
      simp only [sInner, he, inner_neg_left, S2.inner_self]
    have : sDist p q = Real.pi := by rw [sDist, hcos, Real.arccos_neg_one]
    rw [this] at hlt; exact lt_irrefl Real.pi hlt

/-- **Opened non-wrap edges stay short** (margins-free).  For an edge `(i, i+1)` with `i ≠ Fin.last n`,
the opened edge `(openTail A K δ i, openTail A K δ (i + 1))` has the same spherical length as the base
edge `(A i, A (i + 1))` — both endpoints are on the same side of the axis `K` (or the seam, axis fixed +
isometry), so `sDist` is preserved — and the base edge is a `ShortArc` (`A` strict).  The wraparound edge
`i = Fin.last n` (where `i + 1 = 0` straddles the axis) is excluded. -/
theorem openTail_nonwrap_shortArc {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (K : Fin (n + 1)) (δ : ℝ) {i : Fin (n + 1)} (hi : i ≠ Fin.last n) :
    ShortArc (openTail A K δ i) (openTail A K δ (i + 1)) := by
  -- the base edge is short, with a known spherical length in `(0, π)`.
  have hbase : ShortArc (A i) (A (i + 1)) := arm_edge_short hA i
  -- `i ≠ last` ⟹ `i.val < n` ⟹ `(i + 1).val = i.val + 1` (no wraparound).
  have hilt : i.val < n := by
    have hival : i.val < n + 1 := i.isLt
    have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := Fin.val_last n
    rcases Nat.lt_or_ge i.val n with h | h
    · exact h
    · exact absurd (Fin.ext (by omega)) hi
  have hi1 : ((i + 1 : Fin (n + 1)) : ℕ) = i.val + 1 := by
    rw [Fin.val_add, Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
    exact Nat.mod_eq_of_lt (by omega)
  -- the opened edge has the same length as the base edge; ShortArc transfers.
  have hsd : sDist (openTail A K δ i) (openTail A K δ (i + 1)) = sDist (A i) (A (i + 1)) := by
    rcases lt_trichotomy i.val K.val with hlt | heq | hgt
    · -- both endpoints fixed (`i ≤ K` and `i + 1 ≤ K`).
      rw [openTail_fixed A K δ (by omega), openTail_fixed A K δ (show (i + 1).val ≤ K.val by omega)]
    · -- seam: `i = K` (axis fixed), `i + 1 > K` (tail rotated).
      have hiK : i = K := Fin.ext heq
      subst hiK
      have hgt1 : i.val < (i + 1).val := by omega
      exact sDist_openTail_axis_tail A i δ hgt1
    · -- both endpoints rotated (`i > K` and `i + 1 > K`).
      exact sDist_openTail_tail A K δ hgt (show K.val < (i + 1).val by omega)
  -- ShortArc from the preserved length in `(0, π)`.
  refine shortArc_of_sDist_pos_lt_pi ?_ ?_
  · rw [hsd]; exact hbase.sDist_pos
  · rw [hsd]; exact hbase.sDist_lt_pi

/-- **The opened-arm joints lie in `(0, π)` at the WBS supremum** (margins-free).  Off-axis joints are
unchanged (`jointAngle_openTail_eq_of_ne`), so positive (`A` strict) and `< π` (`A` strict); the joint
`k` opens to `jointAngle A k + δ*_WBS` (`openedNegJointAngle_eq_add`, branch from the deficit bound), so
`≥ jointAngle A k > 0` and `≤ jointAngle B k < π` (slack closure + `B` strict). -/
theorem openedJoints_in_Ioo_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    ∀ r : Fin (n - 1),
      0 < jointAngle (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) r ∧
        jointAngle (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) r < Real.pi := by
  set δ : ℝ := monitoredSupWBS A B k with hδ
  -- the deficit bound gives `δ ≤ jointAngle B k − jointAngle A k`, hence the additive branch.
  have hδ0 : 0 ≤ δ := (monitoredSupWBS_mem_Icc hA hka hkt hkdef).1
  have hub : δ ≤ jointAngle B k - jointAngle A k := monitoredSupWBS_le_deficit hA hka hkt hkdef
  have hBlt : jointAngle B k < Real.pi := strict_jointAngle_lt_pi hB k
  have hbranch : jointAngle A k + δ ≤ Real.pi := by linarith
  intro r
  by_cases hrk : r = k
  · -- the opened joint `k`.
    subst hrk
    rw [jointAngle_openTail_eq_openedInterior A r (-δ),
      openedNegJointAngle_eq_add hA hka hkt hδ0 hbranch]
    refine ⟨?_, by linarith⟩
    have hpos : 0 < jointAngle A r := strict_jointAngle_pos hA r
    linarith
  · -- off-axis joints are unchanged.
    rw [jointAngle_openTail_eq_of_ne A k (-δ) hrk]
    exact ⟨strict_jointAngle_pos hA r, strict_jointAngle_lt_pi hA r⟩

/-- **The opened-arm wraparound edge is distinct at the WBS supremum** (margins-free, FFCT43 route).
`endpt A'_WBS = sDist (A'_WBS 0)(A'_WBS last)`; `glueWBS_clause_i` gives `endpt A ≤ endpt A'_WBS` and
`strict_arm_endpt_pos` gives `0 < endpt A`, so `A'_WBS 0 ≠ A'_WBS last`.  (Non-antipodality of the wrap
edge is the one fact the weak-support branch cannot conclude margins-free; the strict branch closes it.) -/
theorem openedWrap_distinct_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0
      ≠ openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n) := by
  have hpos : 0 < endpt A := strict_arm_endpt_pos hA
  have hmono : endpt A ≤ endpt (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) :=
    glueWBS_clause_i hA hka hkt hkdef
  have hsd : (0 : ℝ) < sDist (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n)) :=
    lt_of_lt_of_le hpos hmono
  intro heq
  rw [sDist_eq_zero_iff.2 heq] at hsd
  exact lt_irrefl 0 hsd





/-- **Opened ShortArc edges (all `n + 1`) from the wrap residual.**  Interior/seam/tail edges are short
margins-free (`openTail_nonwrap_shortArc`); the wraparound edge `i = Fin.last n` (`i + 1 = 0`) is supplied
by the wrap ShortArc (symmetrized to the `(last, last + 1)` orientation). -/
theorem openedEdges_short_at_supWBS_of_wrap {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hwrap : ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)) :
    ∀ i : Fin (n + 1),
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1)) := by
  intro i
  by_cases hi : i = Fin.last n
  · subst hi; rw [lastAddOne_eq_zero]; exact hwrap
  · exact openTail_nonwrap_shortArc hA (openingAxis k) (-(monitoredSupWBS A B k)) hi

/-- **Brick 5 — support-stuck ⟹ weakly convex.**  At a `SupportStuckWBS` supremum (a non-incident support
vanishes, so only weak supports are available), the opened arm `A'_WBS` is `WeakConvexSphArm`.  The open
hemisphere (brick 4) is produced margins-free from weak supports + open joints + the opened ShortArc edges;
it gives the edge distinctness `hdist` and feeds `weakConvex_of_supportStuckW_of_hemiPos_anyH`.  The wrap
edge's non-antipodality is the residual `OpenedWrapShortArcAtSupWBS`. -/
theorem supportStuckWBS_weakConvex {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hwrap : ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)) :
    WeakConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) := by
  set δ : ℝ := monitoredSupWBS A B k with hδ
  have hedge := openedEdges_short_at_supWBS_of_wrap hA hwrap
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  have hsupp := supportWBS_sOrient_nonneg hA hka hkt hkdef
  -- the open hemisphere (brick 4), margins-free.
  obtain ⟨h', hnorm, hhem⟩ := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  -- edge distinctness from the ShortArc edges.
  have hdist : ∀ i : Fin (n + 1),
      openTail A (openingAxis k) (-δ) i ≠ openTail A (openingAxis k) (-δ) (i + 1) :=
    fun i => (hedge i).1
  exact weakConvex_of_supportStuckW_of_hemiPos_anyH hA hsupp hdist ⟨h', hnorm, hhem⟩

/-- **Brick 6 — reach / no-support-stuck ⟹ strictly convex.**  When no non-incident support of `A'_WBS`
vanishes (`¬ SupportStuckWBS`), the weak supports upgrade to **strict** (`lt_of_le_of_ne`).  The strict
supports give the opened ShortArc edges margins-free — including the wraparound edge, whose non-antipodality
follows from `antipodal_pair_excluded_of_strict` (so **no wrap residual is needed here**) — and the open
hemisphere (brick 4); `reach_strictConvex_interior` assembles `StrictConvexSphArm A'_WBS`. -/
theorem reachWBS_strictConvex {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hnotStuck : ¬ SupportStuckWBS A B k) :
    StrictConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) := by
  set δ : ℝ := monitoredSupWBS A B k with hδ
  have hn : 2 ≤ n := hA.two_le
  have hsupp := supportWBS_sOrient_nonneg hA hka hkt hkdef
  -- strict supports: weak `≥ 0` is `> 0` since none vanishes (else `SupportStuckWBS`).
  have hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < sOrient (openTail A (openingAxis k) (-δ) i) (openTail A (openingAxis k) (-δ) (i + 1))
        (openTail A (openingAxis k) (-δ) j) := by
    intro i j hji hji1
    refine lt_of_le_of_ne (hsupp i j hji hji1) (fun heq => hnotStuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, ?_⟩)
    rw [supportConstraint_apply]; exact heq.symm
  -- the opened ShortArc wrap edge from strict supports: distinct + non-antipodal.
  have hwrapdist := openedWrap_distinct_at_supWBS hA hka hkt hkdef
  have hwrap : ShortArc (openTail A (openingAxis k) (-δ) (Fin.last n))
      (openTail A (openingAxis k) (-δ) 0) := by
    refine ⟨fun he => hwrapdist he.symm, fun he => ?_⟩
    -- `A'_WBS last = -(A'_WBS 0)`: antipodal pair `(last, 0)` excluded by strict supports
    -- (`last ≠ 0`, `last ≠ 0 + 1 = 1` for `n ≥ 2`).
    have hl0 : (Fin.last n : Fin (n + 1)) ≠ (0 : Fin (n + 1)) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_last, Fin.val_zero] at this; omega
    have hl1 : (Fin.last n : Fin (n + 1)) ≠ (0 : Fin (n + 1)) + 1 := by
      intro h; have := congrArg Fin.val h
      rw [Fin.val_last, zero_add, Fin.val_one'] at this
      rw [Nat.mod_eq_of_lt (by omega : 1 < n + 1)] at this; omega
    exact antipodal_pair_excluded_of_strict hmix (r := Fin.last n) (s := 0) hl0 hl1 he
  have hedge := openedEdges_short_at_supWBS_of_wrap hA hwrap
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  obtain ⟨h', hnorm, hhem⟩ := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  exact reach_strictConvex_interior hA hnorm hmix hhem

/-- A `SupportStuckWBS` witness yields a vanishing non-incident support of `A'_WBS` in `sOrient` form. -/
theorem supportStuckWBS_vanishingSupport {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hstuck : SupportStuckWBS A B k) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) = 0 := by
  obtain ⟨c, hc⟩ := hstuck
  rw [supportConstraint_apply] at hc
  exact ⟨c.1.1, c.1.2, c.2.1, c.2.2, hc⟩



















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



/-- The base index of an interior joint, as a `Fin (n+1)`. -/
 def jIdx {n : ℕ} (r : Fin (n - 1)) : Fin (n + 1) :=
  ⟨r.val, by have := r.isLt; omega⟩

 theorem jIdx_val {n : ℕ} (r : Fin (n - 1)) : ((jIdx r : Fin (n + 1)) : ℕ) = r.val := rfl

 theorem jIdx_succ_val {n : ℕ} (r : Fin (n - 1)) :
    ((jIdx r + 1 : Fin (n + 1)) : ℕ) = r.val + 1 := by
  have hr := r.isLt
  rw [Fin.val_add, jIdx_val]
  have h1 : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [h1]
  exact Nat.mod_eq_of_lt (by omega)

 theorem jIdx_succ_succ_val {n : ℕ} (r : Fin (n - 1)) :
    (((jIdx r + 1) + 1 : Fin (n + 1)) : ℕ) = r.val + 2 := by
  have hr := r.isLt
  rw [Fin.val_add, jIdx_succ_val]
  have h1 : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [h1]; exact Nat.mod_eq_of_lt (by omega)

 theorem P_jIdx_succ {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P (jIdx r + 1) = P ⟨r.val + 1, by have := r.isLt; omega⟩ := by
  congr 1; apply Fin.ext; rw [jIdx_succ_val]

 theorem P_jIdx_succ_succ {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P ((jIdx r + 1) + 1) = P ⟨r.val + 2, by have := r.isLt; omega⟩ := by
  congr 1; apply Fin.ext; rw [jIdx_succ_succ_val]

 theorem P_jIdx {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P (jIdx r) = P ⟨r.val, by have := r.isLt; omega⟩ := rfl

 theorem jointAngle_eq_consecutive {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    jointAngle P r =
      sphAngle (P ⟨r.val, by have := r.isLt; omega⟩) (P ⟨r.val + 1, by have := r.isLt; omega⟩)
        (P ⟨r.val + 2, by have := r.isLt; omega⟩) := rfl

/-- An interior-joint base index `jIdx r` is a **real** edge: `jIdx r ≠ Fin.last n` (its value is
`r.val ≤ n - 2 < n`). -/
 theorem jIdx_ne_last {n : ℕ} (r : Fin (n - 1)) : (jIdx r : Fin (n + 1)) ≠ Fin.last n := by
  intro h
  have hr := r.isLt
  have := congrArg Fin.val h
  rw [jIdx_val, Fin.val_last] at this
  omega

/-- The successor index `jIdx r + 1` is also a **real** edge: its value is `r.val + 1 ≤ n - 1 < n`. -/
 theorem jIdx_succ_ne_last {n : ℕ} (r : Fin (n - 1)) :
    (jIdx r + 1 : Fin (n + 1)) ≠ Fin.last n := by
  intro h
  have hr := r.isLt
  have := congrArg Fin.val h
  rw [jIdx_succ_val, Fin.val_last] at this
  omega



/-- A flat interior joint is impossible (open-chain copy of FFCT44's `flat_interior_joint_absurd`). -/
 theorem flat_interior_joint_absurd {n : ℕ} {P : Fin (n + 1) → S2} (r : Fin (n - 1))
    (hsau : ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩) (P ⟨r.val, by have := r.isLt; omega⟩))
    (hsav : ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩)
      (P ⟨r.val + 2, by have := r.isLt; omega⟩))
    (hcol : det3 (P ⟨r.val, by have := r.isLt; omega⟩ : E3)
      (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
      (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) = 0)
    (hjopen : 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    False := by
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero
    (u := P ⟨r.val, by have := r.isLt; omega⟩) (v := P ⟨r.val + 1, by have := r.isLt; omega⟩)
    (w := P ⟨r.val + 2, by have := r.isLt; omega⟩) hsau hsav hcol
  rw [jointAngle_eq_consecutive] at hjopen
  rcases hbridge with h0 | hπ
  · rw [h0] at hjopen; exact lt_irrefl 0 hjopen.1
  · rw [hπ] at hjopen; exact lt_irrefl Real.pi hjopen.2

/-- The two real edges adjacent to the apex of interior joint `r` both have a vanishing area form
against the axis `z` (open-chain: `hallplanes` invoked only at the two real indices). -/
 theorem edge_planes_at_apex {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hallplanes : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (r : Fin (n - 1)) :
    det3 (P ⟨r.val, by have := r.isLt; omega⟩ : E3) (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
        (z : E3) = 0 ∧
      det3 (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
        (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) (z : E3) = 0 := by
  have h1 := hallplanes (jIdx r) (jIdx_ne_last r)
  have h2 := hallplanes (jIdx r + 1) (jIdx_succ_ne_last r)
  rw [P_jIdx P r, P_jIdx_succ P r] at h1
  rw [P_jIdx_succ P r, P_jIdx_succ_succ P r] at h2
  exact ⟨h1, h2⟩

/-- The non-pole apex collapse (open-chain copy of FFCT44's `consecutive_det3_zero_of_nonpole`). -/
 theorem consecutive_det3_zero_of_nonpole {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hallplanes : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (r : Fin (n - 1))
    (hne : (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ (z : E3))
    (hanti : (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ -(z : E3)) :
    det3 (P ⟨r.val, by have := r.isLt; omega⟩ : E3) (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
      (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) = 0 := by
  obtain ⟨he1, he2⟩ := edge_planes_at_apex hallplanes r
  set apex : E3 := (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) with hapex
  set x : E3 := (P ⟨r.val, by have := r.isLt; omega⟩ : E3) with hx
  set y : E3 := (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) with hy
  set zz : E3 := (z : E3) with hzz
  have hzu : ‖zz‖ = 1 := z.2
  have hau : ‖apex‖ = 1 := (P _).2
  have hzne : zz ≠ apex := fun h => hne h.symm
  have hzanti : zz ≠ -apex := by
    intro h
    exact hanti (by rw [h]; simp)
  have hdetx : det3 zz apex x = 0 := by
    have hcyc : det3 zz apex x = -det3 x apex zz := by simp only [det3]; ring
    rw [hcyc, he1, neg_zero]
  have hdety : det3 zz apex y = 0 := by
    have hcyc : det3 zz apex y = det3 apex y zz := by simp only [det3]; ring
    rw [hcyc, he2]
  obtain ⟨c1, d1, hx'⟩ := lin_indep_span_of_det3_zero hzu hau hzne hzanti hdetx
  obtain ⟨c2, d2, hy'⟩ := lin_indep_span_of_det3_zero hzu hau hzne hzanti hdety
  have hap' : apex = (0 : ℝ) • zz + (1 : ℝ) • apex := by simp
  exact coplanar_triple_det3_zero ⟨c1, d1, hx'.symm⟩ ⟨0, 1, hap'.symm⟩ ⟨c2, d2, hy'.symm⟩

/-- **§1 — the open-chain meridian-pencil collapse kernel (`3 ≤ n`).**  A chain `P : Fin (n+1) → S2`
(`3 ≤ n`), every **real** edge of which is a short arc (`hside`, `i ≠ Fin.last n`), every **real** edge
plane of which contains a common unit axis `z` (`hallplanes`, `i ≠ Fin.last n`), with all interior joints
in `(0, π)` (`hjopen`), is impossible.  The wrap edge `(P last, P 0)` is **not** used. -/
theorem openChain_collapse_forces_flat_joint_ge3 {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hn : 3 ≤ n)
    (hside : ∀ i : Fin (n + 1), i ≠ Fin.last n → ShortArc (P i) (P (i + 1)))
    (hallplanes : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    False := by
  classical
  -- The two short joint arcs at the apex of interior joint `r` (both edges real).
  have hshort_apex : ∀ r : Fin (n - 1),
      ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩) (P ⟨r.val, by have := r.isLt; omega⟩) ∧
        ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩)
          (P ⟨r.val + 2, by have := r.isLt; omega⟩) := by
    intro r
    have e1 := hside (jIdx r) (jIdx_ne_last r)
    have e2 := hside (jIdx r + 1) (jIdx_succ_ne_last r)
    rw [P_jIdx P r, P_jIdx_succ P r] at e1
    rw [P_jIdx_succ P r, P_jIdx_succ_succ P r] at e2
    exact ⟨e1.symm, e2⟩
  by_cases hsome : ∃ r : Fin (n - 1),
      (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ (z : E3) ∧
        (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ -(z : E3)
  · -- CASE (a): a non-pole apex.  The collapse gives a flat joint.
    obtain ⟨r, hne, hanti⟩ := hsome
    obtain ⟨hsau, hsav⟩ := hshort_apex r
    have hcol := consecutive_det3_zero_of_nonpole hallplanes r hne hanti
    exact flat_interior_joint_absurd r hsau hsav hcol (hjopen r)
  · -- CASE (b): every interior apex is a pole `P apex = ± z`.  With `n ≥ 3`, joints `0`, `1` give
    -- adjacent interior poles `P 1`, `P 2` sharing the real edge `(P 1, P 2)` — ShortArc kill.
    push_neg at hsome
    have hpole : ∀ r : Fin (n - 1),
        (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = (z : E3) ∨
          (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = -(z : E3) := by
      intro r
      by_cases h1 : (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = (z : E3)
      · exact Or.inl h1
      · exact Or.inr (hsome r h1)
    have hp0 := hpole ⟨0, by omega⟩
    have hp1 := hpole ⟨1, by omega⟩
    have hsh := (hshort_apex ⟨0, by omega⟩).2
    have hsh1 : (P ⟨0 + 1, by omega⟩ : E3) ≠ (P ⟨0 + 2, by omega⟩ : E3) := by
      intro he; exact hsh.1 (S2.ext he)
    have hsh2 : (P ⟨0 + 1, by omega⟩ : E3) ≠ -(P ⟨0 + 2, by omega⟩ : E3) := hsh.2
    rcases hp0 with hp0z | hp0z <;> rcases hp1 with hp1z | hp1z
    · exact hsh1 (by rw [hp0z, hp1z])
    · exact hsh2 (by rw [hp0z, hp1z, neg_neg])
    · exact hsh2 (by rw [hp0z, hp1z])
    · exact hsh1 (by rw [hp0z, hp1z])



/-- **§2 — margins-free, wrap-edge-free open hemisphere.**  For a chain `P : Fin (n+1) → S2` (`2 ≤ n`)
with **real-edge** short arcs (`hside`, `i ≠ Fin.last n`), **real-edge** weak supports (`hsupp`,
`i ≠ Fin.last n`), and all interior joints in `(0, π)` (`hjopen`), there is a *unit* normal `h'`
strictly positive against every vertex.  **No margins, no wrap edge.** -/
theorem openHemisphere_full_openChain {n : ℕ} {P : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hside : ∀ i : Fin (n + 1), i ≠ Fin.last n → ShortArc (P i) (P (i + 1)))
    (hsupp : ∀ i j : Fin (n + 1), i ≠ Fin.last n → j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j))
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    ∃ h' : E3, ‖h'‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ) := by
  classical
  set s : Finset E3 := (Finset.univ : Finset (Fin (n + 1))).image (fun r => ((P r : S2) : E3))
    with hs
  have hmem_iff : ∀ v, v ∈ s ↔ ∃ m, ((P m : S2) : E3) = v := by
    intro v
    rw [hs, Finset.mem_image]
    constructor
    · rintro ⟨m, _hm, rfl⟩; exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩; exact ⟨m, Finset.mem_univ _, rfl⟩
  by_cases h0 : (0 : E3) ∈ convexHull ℝ (s : Set E3)
  · exfalso
    rw [Finset.mem_convexHull'] at h0
    obtain ⟨w, hw0, hw1, hwsum⟩ := h0
    -- For every REAL edge `i` and every member `v`, `w v * det3 (P i)(P i+1) v ≥ 0`.
    have hterm_nonneg : ∀ (i : Fin (n + 1)), i ≠ Fin.last n → ∀ (v : E3), v ∈ s →
        0 ≤ w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i hi v hv
      obtain ⟨m, rfl⟩ := (hmem_iff v).mp hv
      by_cases hmi : m = i
      · subst hmi; rw [show det3 (P m : E3) (P (m + 1) : E3) (P m : E3) = 0 from by
          simp only [det3]; ring, mul_zero]
      · by_cases hmi1 : m = i + 1
        · subst hmi1; rw [show det3 (P i : E3) (P (i + 1) : E3) (P (i + 1) : E3) = 0 from by
            simp only [det3]; ring, mul_zero]
        · exact mul_nonneg (hw0 _ hv)
            (le_trans (le_of_eq rfl) (hsupp i m hi (by simpa [eq_comm] using hmi)
              (by simpa [eq_comm] using hmi1)))
    -- The REAL-edge functional pushed through the convex combination is `0`.
    have hedge_zero : ∀ i : Fin (n + 1), i ≠ Fin.last n →
        (0 : ℝ) = ∑ v ∈ s, w v * det3 (P i : E3) (P (i + 1) : E3) v := by
      intro i _hi
      have hkey := det3_edge_centerSum (P i : E3) (P (i + 1) : E3) s w
      rw [hwsum] at hkey
      rw [show det3 (P i : E3) (P (i + 1) : E3) (0 : E3) = 0 from by simp [det3]] at hkey
      exact hkey
    have hterm_zero : ∀ i : Fin (n + 1), i ≠ Fin.last n → ∀ v ∈ s,
        w v * det3 (P i : E3) (P (i + 1) : E3) v = 0 := by
      intro i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => hterm_nonneg i hi v hv)).mp
        (hedge_zero i hi).symm
    -- Pick a positive-weight member.
    have hexists_pos : ∃ v ∈ s, 0 < w v := by
      by_contra hnone
      push_neg at hnone
      have : ∑ v ∈ s, w v = 0 :=
        Finset.sum_eq_zero (fun v hv => le_antisymm (hnone v hv) (hw0 v hv))
      rw [hw1] at this; exact one_ne_zero this
    -- A positive-weight vertex `v₀ = P r₀` is a common REAL-edge axis.
    have hcommon_axis : ∀ (r0 : Fin (n + 1)), 0 < w ((P r0 : S2) : E3) →
        ∀ i : Fin (n + 1), i ≠ Fin.last n →
          det3 (P i : E3) (P (i + 1) : E3) (P r0 : E3) = 0 := by
      intro r0 hr0pos i hi
      have hv0s : ((P r0 : S2) : E3) ∈ s := by rw [hmem_iff]; exact ⟨r0, rfl⟩
      have := hterm_zero i hi ((P r0 : S2) : E3) hv0s
      rcases mul_eq_zero.mp this with hw | hd
      · exact absurd hw (ne_of_gt hr0pos)
      · exact hd
    rcases Nat.lt_or_ge 2 n with hn3 | hn2
    · -- `3 ≤ n`: a common-axis vertex contradicts the open-chain kernel.
      obtain ⟨v0, hv0s, hv0pos⟩ := hexists_pos
      obtain ⟨r0, hv0eq⟩ := (hmem_iff v0).mp hv0s
      have hr0pos : 0 < w ((P r0 : S2) : E3) := by rw [hv0eq]; exact hv0pos
      exact openChain_collapse_forces_flat_joint_ge3 (z := P r0) (by omega) hside
        (hcommon_axis r0 hr0pos) hjopen
    · -- `n = 2`: a positive-weight vertex `≠ P 1` (index `0` or `2`) gives the flat single joint.
      have hneq : n = 2 := by omega
      subst hneq
      -- There is a positive-weight vertex `v₀` with `v₀ ≠ (P 1 : E3)` (else `0 = (Σw)•(P 1)`).
      have hne1 : ∃ v ∈ s, 0 < w v ∧ v ≠ ((P (1 : Fin 3) : S2) : E3) := by
        by_contra hcon
        push_neg at hcon
        -- every member is either zero-weight or equals `P 1`.
        have hsum1 : ∑ v ∈ s, w v • v = ((∑ v ∈ s, w v) : ℝ) • ((P (1 : Fin 3) : S2) : E3) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl (fun v hv => ?_)
          rcases lt_or_eq_of_le (hw0 v hv) with hpos | hzero
          · rw [hcon v hv hpos]
          · rw [← hzero, zero_smul, zero_smul]
        rw [hwsum, hw1, one_smul] at hsum1
        -- `0 = P 1` contradicts `‖P 1‖ = 1`.
        have hnorm1 : ‖((P (1 : Fin 3) : S2) : E3)‖ = 1 := (P (1 : Fin 3)).2
        rw [← hsum1, norm_zero] at hnorm1
        exact one_ne_zero hnorm1.symm
      obtain ⟨v0, hv0s, hv0pos, hv0ne⟩ := hne1
      obtain ⟨r0, hv0eq⟩ := (hmem_iff v0).mp hv0s
      have hr0pos : 0 < w ((P r0 : S2) : E3) := by rw [hv0eq]; exact hv0pos
      -- `r0 ≠ 1` (else `P r0 = P 1 = v0`, contradicting `hv0ne`).
      have hr0ne1 : r0 ≠ (1 : Fin 3) := by
        intro h; apply hv0ne; rw [← hv0eq, h]
      -- the single interior joint `0`; vertices `P 0, P 1, P 2`.
      have hjoint0 := hjopen ⟨0, by omega⟩
      -- the two real edges `0` and `1`.
      have he0 : (Fin.last 2 : Fin 3) = (2 : Fin 3) := rfl
      have h0ne : (0 : Fin 3) ≠ Fin.last 2 := by rw [he0]; decide
      have h1ne : (1 : Fin 3) ≠ Fin.last 2 := by rw [he0]; decide
      -- `det3 (P 0)(P 1)(P 2) = 0` from the common-axis facts, depending on `r0 ∈ {0, 2}`.
      have hcol : det3 (P ⟨0, by omega⟩ : E3) (P ⟨0 + 1, by omega⟩ : E3)
          (P ⟨0 + 2, by omega⟩ : E3) = 0 := by
        -- normalise the nat-indexed vertices to `P 0, P 1, P 2`.
        have e0 : (P ⟨0, by omega⟩ : E3) = (P (0 : Fin 3) : E3) := rfl
        have e1 : (P ⟨0 + 1, by omega⟩ : E3) = (P (1 : Fin 3) : E3) := rfl
        have e2 : (P ⟨0 + 2, by omega⟩ : E3) = (P (2 : Fin 3) : E3) := rfl
        rw [e0, e1, e2]
        -- `r0` is `0` or `2`.
        have hr0cases : r0 = (0 : Fin 3) ∨ r0 = (2 : Fin 3) := by
          fin_cases r0
          · exact Or.inl rfl
          · exact absurd rfl hr0ne1
          · exact Or.inr rfl
        rcases hr0cases with hr0 | hr0
        · -- `r0 = 0`: edge `1 = (P 1, P 2)` axis gives `det3 (P 1)(P 2)(P 0) = 0`; cyclic.
          have hax := hcommon_axis r0 hr0pos (1 : Fin 3) h1ne
          rw [hr0] at hax
          -- `(1 : Fin 3) + 1 = 2`.
          have h11 : ((1 : Fin 3) + 1) = (2 : Fin 3) := by decide
          rw [h11] at hax
          -- `hax : det3 (P 1)(P 2)(P 0) = 0`; cyclic ⟹ `det3 (P 0)(P 1)(P 2) = 0`.
          have hcyc : det3 (P (0 : Fin 3) : E3) (P (1 : Fin 3) : E3) (P (2 : Fin 3) : E3)
              = det3 (P (1 : Fin 3) : E3) (P (2 : Fin 3) : E3) (P (0 : Fin 3) : E3) := by
            simp only [det3]; ring
          rw [hcyc]; exact hax
        · -- `r0 = 2`: edge `0 = (P 0, P 1)` axis gives `det3 (P 0)(P 1)(P 2) = 0` directly.
          have hax := hcommon_axis r0 hr0pos (0 : Fin 3) h0ne
          rw [hr0] at hax
          have h01 : ((0 : Fin 3) + 1) = (1 : Fin 3) := by decide
          rw [h01] at hax
          exact hax
      -- the short joint arcs at apex `P 1` (both real edges).
      have hside0 := hside (0 : Fin 3) h0ne
      have hside1 := hside (1 : Fin 3) h1ne
      have h01 : ((0 : Fin 3) + 1) = (1 : Fin 3) := by decide
      have h11 : ((1 : Fin 3) + 1) = (2 : Fin 3) := by decide
      rw [h01] at hside0
      rw [h11] at hside1
      -- assemble the apex short arcs in the orientation `flat_interior_joint_absurd` wants.
      have hsau : ShortArc (P ⟨0 + 1, by omega⟩ : S2) (P ⟨0, by omega⟩ : S2) := by
        have : ShortArc (P (1 : Fin 3)) (P (0 : Fin 3)) := hside0.symm
        exact this
      have hsav : ShortArc (P ⟨0 + 1, by omega⟩ : S2) (P ⟨0 + 2, by omega⟩ : S2) := by
        have : ShortArc (P (1 : Fin 3)) (P (2 : Fin 3)) := hside1
        exact this
      exact flat_interior_joint_absurd (⟨0, by omega⟩ : Fin (2 - 1)) hsau hsav hcol hjoint0
  · -- `0 ∉ hull`: separation gives the strict hemisphere normal directly; normalise to unit length.
    obtain ⟨t, ht⟩ := exists_inner_pos_of_zero_notMem_convexHull s.finite_toSet h0
    have htpos : ∀ r : Fin (n + 1), 0 < (⟪t, (P r : E3)⟫ : ℝ) := by
      intro r
      have hrmem : ((P r : S2) : E3) ∈ s := by rw [hmem_iff]; exact ⟨r, rfl⟩
      exact ht _ hrmem
    have htne : t ≠ 0 := by
      intro h
      have := htpos ⟨0, by omega⟩
      rw [h, inner_zero_left] at this
      exact lt_irrefl _ this
    have htnorm : 0 < ‖t‖ := norm_pos_iff.mpr htne
    refine ⟨(‖t‖⁻¹ : ℝ) • t, ?_, fun r => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm]; field_simp
    · rw [inner_smul_left]
      simp only [RCLike.conj_to_real]
      exact mul_pos (by positivity) (htpos r)



/-- **§3 — wrap ShortArc from the open hemisphere.**  If `h'` is strictly positive against both wrap
endpoints `P last`, `P 0` (an open-hemisphere certificate) and the two endpoints are distinct
(`hdist`), then the wrap edge `(P last, P 0)` is a `ShortArc`: distinctness is `hdist`, and
non-antipodality is forced because `(P last : E3) = -(P 0 : E3)` would give
`0 < ⟪h', P last⟫ = -⟪h', P 0⟫ < 0`. -/
theorem wrap_shortArc_of_hemisphere {n : ℕ} {P : Fin (n + 1) → S2} {h' : E3}
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ))
    (hdist : P (Fin.last n) ≠ P 0) :
    ShortArc (P (Fin.last n)) (P 0) := by
  refine ⟨hdist, fun he => ?_⟩
  have hlast : 0 < (⟪h', (P (Fin.last n) : E3)⟫ : ℝ) := hhem (Fin.last n)
  have hzero : 0 < (⟪h', (P 0 : E3)⟫ : ℝ) := hhem 0
  rw [he, inner_neg_right] at hlast
  linarith



/-- **§4 — the opened wraparound edge IS a short arc at the WBS supremum** (the discharge of the
residual content of FFCT46's `OpenedWrapShortArcAtSupWBS`, instantiated).  Margins-free,
wrap-edge-free: produced by the open-chain hemisphere on the real-edge data, plus the FFCT43-route
distinctness. -/
theorem openedWrapShortArc_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) := by
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set K : Fin (n + 1) := openingAxis k with hK
  set P : Fin (n + 1) → S2 := openTail A K (-δ) with hP
  have hn : 2 ≤ n := hA.two_le
  -- real-edge ShortArc edges (the wrap edge `i = Fin.last n` is excluded).
  have hside : ∀ i : Fin (n + 1), i ≠ Fin.last n → ShortArc (P i) (P (i + 1)) := by
    intro i hi; rw [hP]; exact openTail_nonwrap_shortArc hA K (-δ) hi
  -- real-edge weak supports (the FFCT45 supports hold for ALL `(i, j)`; restrict to real `i`).
  have hsupp : ∀ i j : Fin (n + 1), i ≠ Fin.last n → j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j) := by
    intro i j _hi hji hji1
    rw [hP]; exact supportWBS_sOrient_nonneg hA hka hkt hkdef i j hji hji1
  -- opened joints in `(0, π)`.
  have hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi := by
    rw [hP]; exact openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  -- the wrap-edge-free open hemisphere.
  obtain ⟨h', _hnorm, hhem⟩ := openHemisphere_full_openChain hn hside hsupp hjopen
  -- margins-free distinctness of the wrap endpoints.
  have hdist : P (Fin.last n) ≠ P 0 := by
    rw [hP]
    intro he
    exact openedWrap_distinct_at_supWBS hA hka hkt hkdef he.symm
  exact wrap_shortArc_of_hemisphere hhem hdist















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



/-- The opened arm `A'_WBS := openTail A (openingAxis k) (-δ*_WBS)` at the WBS supremum (the widening
direction, `= openTailW A (openingAxis k) (monitoredSupWBS A B k)`).  All bridge data live on this arm. -/
def openedWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : Fin (n + 1) → S2 :=
  openTail A (openingAxis k) (-(monitoredSupWBS A B k))









/-- **Non-antipodality from the open hemisphere.**  Two opened vertices `A' a`, `A' b` strictly inside an
open hemisphere (`0 < ⟪h', A' a⟫`, `0 < ⟪h', A' b⟫`) are non-antipodal: `(A' a : E3) = -(A' b : E3)` would
give `0 < ⟪h', A' a⟫ = -⟪h', A' b⟫ < 0`.  This is the slot the open hemisphere supplies for `hsa` (the
*non-antipodal* half of `ShortArc`); the *distinctness* half is the named no-repeat residue. -/
theorem hemisphere_nonAntipodal {n : ℕ} {P : Fin (n + 1) → S2} {h' : E3}
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ)) (a b : Fin (n + 1)) :
    (P a : E3) ≠ -(P b : E3) := by
  intro he
  have ha : 0 < (⟪h', (P a : E3)⟫ : ℝ) := hhem a
  have hb : 0 < (⟪h', (P b : E3)⟫ : ℝ) := hhem b
  rw [he, inner_neg_right] at ha
  linarith



/-- **The equal first side at a consecutive cut endpoint.**  For `i + 1 < j ≤ n` the pair `(i, i+1)` is a
real edge (`i.val < n`), so `SameSides A' B` at index `⟨i⟩ : Fin n` reads as
`sDist (B ⟨i+1⟩)(B ⟨i⟩) = sDist (A' ⟨i+1⟩)(A' ⟨i⟩)` — exactly `StuckAtKData.hside`. -/
theorem hside_of_sameSides {n : ℕ} {A' B : Fin (n + 1) → S2} (hside : SameSides A' B)
    {i j : ℕ} (hij1 : i + 1 < j) (hj : j ≤ n) :
    sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩)
      = sDist (A' ⟨i + 1, by omega⟩) (A' ⟨i, by omega⟩) := by
  have hilt : i < n := by omega
  have hsd : sideLen A' (⟨i, hilt⟩ : Fin n) = sideLen B (⟨i, hilt⟩ : Fin n) := hside ⟨i, hilt⟩
  -- `sideLen X ⟨i⟩ = sDist (X ⟨i⟩)(X ⟨i+1⟩)`: castSucc/succ at value `i` are `⟨i⟩`, `⟨i+1⟩`.
  have hcs : ∀ X : Fin (n + 1) → S2,
      sideLen X (⟨i, hilt⟩ : Fin n) = sDist (X ⟨i, by omega⟩) (X ⟨i + 1, by omega⟩) := by
    intro X
    have hcast : ((⟨i, hilt⟩ : Fin n).castSucc) = (⟨i, by omega⟩ : Fin (n + 1)) :=
      Fin.ext (by simp [Fin.castSucc, Fin.castAdd])
    have hsucc : ((⟨i, hilt⟩ : Fin n).succ) = (⟨i + 1, by omega⟩ : Fin (n + 1)) :=
      Fin.ext (by simp [Fin.succ])
    unfold sideLen
    rw [hcast, hsucc]
  rw [hcs A', hcs B] at hsd
  -- hsd : sDist (A' ⟨i⟩)(A' ⟨i+1⟩) = sDist (B ⟨i⟩)(B ⟨i+1⟩)
  -- goal: sDist (B ⟨i+1⟩)(B ⟨i⟩) = sDist (A' ⟨i+1⟩)(A' ⟨i⟩); use sDist_comm + hsd.
  rw [sDist_comm (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩),
    sDist_comm (A' ⟨i + 1, by omega⟩) (A' ⟨i, by omega⟩)]
  exact hsd.symm























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



/-- **Distinctness at a normalized cut, derived.**  For any arm `P : Fin (n+1) → S2` that is weakly convex
and has no nonadjacent repeat, the normalized cut endpoints `P ⟨i+1⟩`, `P ⟨j⟩` (`i + 1 < j ≤ n`) are
distinct.  Adjacent case `j = i + 2`: the edge `(i+1, i+2)` is a `ShortArc` (weak convexity's
`edge_short`), so its two endpoints are distinct.  Nonadjacent case `(i+1) + 2 ≤ j`: `NoNonadjacentRepeat`.

This discharges `WBSCutNormalization.hrepeat`. -/
theorem distinctNormalized_of_noRepeat {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hrep : NoNonadjacentRepeat P) {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ n) :
    P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ := by
  rcases Nat.lt_or_ge (i + 1 + 2) (j + 1) with hadj | hnon
  · -- nonadjacent: (i+1) + 2 ≤ j, use NoNonadjacentRepeat.
    have hle : (i + 1) + 2 ≤ j := by omega
    exact hrep (i + 1) j (by omega) (by omega) hle
  · -- adjacent: j = i + 2 (since i+1 < j ≤ i+2). The edge (i+1, i+2) is a real arm edge.
    have hjeq : j = i + 2 := by omega
    subst hjeq
    -- edge_short at the Fin index ⟨i+1⟩: ShortArc (P ⟨i+1⟩) (P (⟨i+1⟩ + 1)).
    have hedge : ShortArc (P ⟨i + 1, by omega⟩) (P (⟨i + 1, by omega⟩ + 1)) :=
      hP.closed_convex.edge_short ⟨i + 1, by omega⟩
    -- (⟨i+1⟩ + 1 : Fin (n+1)) = ⟨i+2⟩ since i + 2 ≤ n < n + 1.
    have hsucc : (⟨i + 1, by omega⟩ + 1 : Fin (n + 1)) = ⟨i + 2, by omega⟩ := by
      apply Fin.ext
      have : ((⟨i + 1, by omega⟩ + 1 : Fin (n + 1)) : ℕ) = (i + 1 + 1) % (n + 1) := by
        rw [Fin.add_def]; simp
      rw [this]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hsucc] at hedge
    exact hedge.1





/-- The Fin reversal `m ↦ ⟨n − m⟩` on `Fin (n+1)`. -/
def revFin {n : ℕ} (m : Fin (n + 1)) : Fin (n + 1) := ⟨n - m.val, by have := m.isLt; omega⟩

@[simp] theorem revFin_val {n : ℕ} (m : Fin (n + 1)) : (revFin m).val = n - m.val := rfl

/-- The reversed arm: `revArm P m = P ⟨n − m⟩`. -/
def revArm {n : ℕ} (P : Fin (n + 1) → S2) : Fin (n + 1) → S2 := fun m => P (revFin m)



/-- `revArm P` at a value index `v ≤ n` reads `P` at `n − v`. -/
theorem revArm_index {n : ℕ} (P : Fin (n + 1) → S2) {v : ℕ} (hv : v < n + 1) :
    revArm P ⟨v, hv⟩ = P ⟨n - v, by omega⟩ := rfl

/-- **`sOrient` reversal at a normalized triple.**  For a raw binding with `b < a` (so `a + 1 ≤ n`), the
normalized reversed triple `(revArm P ⟨n−a−1⟩, revArm P ⟨n−a⟩, revArm P ⟨n−b⟩)` reads as
`(P ⟨a+1⟩, P ⟨a⟩, P ⟨b⟩)`, whose `sOrient` is `−sOrient (P ⟨a⟩)(P ⟨a+1⟩)(P ⟨b⟩)` (slot-1-2 swap,
`det3_swap12`).  Hence a *vanishing* raw support gives a *vanishing* normalized reversed support. -/
theorem sOrient_revArm_normalized {n : ℕ} (P : Fin (n + 1) → S2) {a b : ℕ}
    (ha1 : a + 1 < n + 1) (hb : b < a) :
    sOrient (revArm P ⟨n - a - 1, by omega⟩) (revArm P ⟨n - a, by omega⟩)
        (revArm P ⟨n - b, by omega⟩)
      = - sOrient (P ⟨a, by omega⟩) (P ⟨a + 1, by omega⟩) (P ⟨b, by omega⟩) := by
  -- evaluate the reversed indices: n−(n−a−1) = a+1, n−(n−a) = a, n−(n−b) = b.
  rw [revArm_index P (by omega), revArm_index P (by omega), revArm_index P (by omega)]
  have e1 : n - (n - a - 1) = a + 1 := by omega
  have e2 : n - (n - a) = a := by omega
  have e3 : n - (n - b) = b := by omega
  rw [show (⟨n - (n - a - 1), by omega⟩ : Fin (n + 1)) = ⟨a + 1, by omega⟩ from Fin.ext (by omega),
     show (⟨n - (n - a), by omega⟩ : Fin (n + 1)) = ⟨a, by omega⟩ from Fin.ext (by omega),
     show (⟨n - (n - b), by omega⟩ : Fin (n + 1)) = ⟨b, by omega⟩ from Fin.ext (by omega)]
  -- sOrient (P(a+1))(P a)(P b) = -sOrient (P a)(P(a+1))(P b) by slot-1-2 swap.
  exact det3_swap12 _ _ _

/-- **`sideLen` reversal.**  Side `i` of `revArm P` (`i : Fin n`) is the parent's side `n − 1 − i` with its
two endpoints swapped; `sDist_comm` makes them equal.  Concretely `sideLen (revArm P) i =
sDist (P ⟨n−i⟩)(P ⟨n−i−1⟩) = sDist (P ⟨n−i−1⟩)(P ⟨n−i⟩) = sideLen P ⟨n−1−i⟩`. -/
theorem revArm_sideLen {n : ℕ} (P : Fin (n + 1) → S2) (i : Fin n) :
    sideLen (revArm P) i = sideLen P ⟨n - 1 - i.val, by have := i.isLt; omega⟩ := by
  have hi := i.isLt
  unfold sideLen
  -- index equalities (as Fin equalities, so rewriting is motive-safe).
  have l0 : revArm P i.castSucc = P ⟨n - i.val, by omega⟩ := by
    show P (revFin i.castSucc) = _
    exact congrArg P (Fin.ext (by simp only [revFin_val, Fin.val_castSucc]))
  have l1 : revArm P i.succ = P ⟨n - i.val - 1, by omega⟩ := by
    show P (revFin i.succ) = _
    exact congrArg P (Fin.ext (by simp only [revFin_val, Fin.val_succ]; omega))
  have r0 : P ((⟨n - 1 - i.val, by omega⟩ : Fin n).castSucc) = P ⟨n - i.val - 1, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [Fin.val_castSucc]; omega))
  have r1 : P ((⟨n - 1 - i.val, by omega⟩ : Fin n).succ) = P ⟨n - i.val, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [Fin.val_succ]; omega))
  rw [l0, l1, r0, r1]
  -- goal: sDist (P ⟨n−i⟩)(P ⟨n−i−1⟩) = sDist (P ⟨n−i−1⟩)(P ⟨n−i⟩).
  exact sDist_comm _ _

/-- **`jointAngle` reversal.**  Interior joint `i` of `revArm P` (`i : Fin (n−1)`) is the parent's interior
joint `n − 2 − i` read backwards; `sphAngle_comm` (swap the two neighbours) makes the value invariant. -/
theorem revArm_jointAngle {n : ℕ} (P : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    jointAngle (revArm P) i = jointAngle P ⟨n - 2 - i.val, by have := i.isLt; omega⟩ := by
  have hi := i.isLt
  unfold jointAngle
  -- LHS = sphAngle (revArm P ⟨i⟩)(revArm P ⟨i+1⟩)(revArm P ⟨i+2⟩); each reads P at n−i, n−i−1, n−i−2.
  have v0 : (revArm P ⟨i.val, by omega⟩ : S2) = P ⟨n - 2 - i.val + 2, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [revFin_val]; omega))
  have v1 : (revArm P ⟨i.val + 1, by omega⟩ : S2) = P ⟨n - 2 - i.val + 1, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [revFin_val]; omega))
  have v2 : (revArm P ⟨i.val + 2, by omega⟩ : S2) = P ⟨n - 2 - i.val, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [revFin_val]; omega))
  -- rewrite each LHS vertex; LHS becomes sphAngle (P j+2)(P j+1)(P j) with j = n−2−i.
  show sphAngle (revArm P ⟨i.val, _⟩) (revArm P ⟨i.val + 1, _⟩) (revArm P ⟨i.val + 2, _⟩) = _
  rw [v0, v1, v2, sphAngle_comm]





/-- The no-nonadjacent-repeat fact transports under reversal: a nonadjacent repeat of `revArm P` at
`r + 2 ≤ s` is a nonadjacent repeat of `P` at the reversed indices `n − s + 2 ≤ n − r`. -/
theorem revArm_noNonadjacentRepeat {n : ℕ} {P : Fin (n + 1) → S2}
    (hrep : NoNonadjacentRepeat P) : NoNonadjacentRepeat (revArm P) := by
  intro r s hr hs hrs he
  -- revArm P ⟨r⟩ = P ⟨n−r⟩, revArm P ⟨s⟩ = P ⟨n−s⟩; he : P ⟨n−r⟩ = P ⟨n−s⟩.
  rw [revArm_index P hr, revArm_index P hs] at he
  -- nonadjacent on P: (n−s) + 2 ≤ n−r since r + 2 ≤ s.
  exact hrep (n - s) (n - r) (by omega) (by omega) (by omega) he.symm



/-- **The orientation-normalized vanishing support, both branches.**  From the raw Fin binding
`sOrient (P a)(P (a+1))(P b) = 0` with `b ≠ a` and `b ≠ a+1` (as Fin), the normalized cut exists:
* if `a.val + 1 < b.val`: on `P` itself, `(i, j) = (a, b)`, support unchanged;
* if `b.val < a.val`: on `revArm P`, `(i, j) = (n − a − 1, n − b)`, support flipped (`= 0` is sign-free);
in both branches `i + 1 < j ≤ n` and `sOrient (Q ⟨i⟩)(Q ⟨i+1⟩)(Q ⟨j⟩) = 0` for the chosen arm `Q`. -/
theorem orientationNormalized {n : ℕ} (P : Fin (n + 1) → S2) {a b : Fin (n + 1)}
    (hne : b ≠ a) (hne1 : b ≠ a + 1)
    (hsupp : sOrient (P a) (P (a + 1)) (P b) = 0)
    (hadj : a.val + 1 < n + 1) :
    (∃ i j : ℕ, ∃ (hij1 : i + 1 < j) (hj : j ≤ n),
        sOrient (P ⟨i, by omega⟩) (P ⟨i + 1, by omega⟩) (P ⟨j, by omega⟩) = 0)
    ∨ (∃ i j : ℕ, ∃ (hij1 : i + 1 < j) (hj : j ≤ n),
        sOrient (revArm P ⟨i, by omega⟩) (revArm P ⟨i + 1, by omega⟩) (revArm P ⟨j, by omega⟩) = 0) := by
  have hai := a.isLt
  have hbi := b.isLt
  -- the Fin (a+1) reads as value a.val + 1 (since a.val + 1 < n + 1, no wrap).
  have hav : a.val + 1 < n + 1 := hadj
  have hfsucc : (a + 1 : Fin (n + 1)) = ⟨a.val + 1, hav⟩ := by
    apply Fin.ext
    have : ((a + 1 : Fin (n + 1)) : ℕ) = (a.val + 1) % (n + 1) := by rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt hav]
  -- ℕ-disequalities from the Fin ones.
  have hbne : b.val ≠ a.val := fun h => hne (Fin.ext h)
  have hbne1 : b.val ≠ a.val + 1 := by
    intro h; apply hne1; rw [hfsucc]; exact Fin.ext h
  rcases Nat.lt_or_ge (a.val + 1) b.val with hgt | hle
  · -- a.val + 1 < b.val: normalize on P directly with (i, j) = (a.val, b.val).
    left
    refine ⟨a.val, b.val, hgt, by have := b.isLt; omega, ?_⟩
    -- rewrite the goal's Fin indices to a, a+1, b.
    rw [show (⟨a.val, by omega⟩ : Fin (n + 1)) = a from Fin.ext rfl,
       show (⟨a.val + 1, by omega⟩ : Fin (n + 1)) = a + 1 from hfsucc.symm,
       show (⟨b.val, by omega⟩ : Fin (n + 1)) = b from Fin.ext rfl]
    exact hsupp
  · -- b.val < a.val (since b ≠ a, b ≠ a+1 and ¬ a+1 < b): normalize on revArm P.
    have hblt : b.val < a.val := by omega
    right
    refine ⟨n - a.val - 1, n - b.val, by omega, by have := b.isLt; omega, ?_⟩
    -- the reversed normalized support = -(raw support) = 0.
    have hrev := sOrient_revArm_normalized P (a := a.val) (b := b.val) (by omega) hblt
    -- align the goal's middle index `(n-a-1)+1` to `n-a` (the form `hrev` uses).
    have hmid : (⟨(n - a.val - 1) + 1, by omega⟩ : Fin (n + 1)) = ⟨n - a.val, by omega⟩ :=
      Fin.ext (show (n - a.val - 1) + 1 = n - a.val by omega)
    rw [hmid, hrev]
    -- raw support in value form = hsupp after aligning a, a+1, b.
    rw [show (⟨a.val, by omega⟩ : Fin (n + 1)) = a from Fin.ext rfl,
       show (⟨a.val + 1, by omega⟩ : Fin (n + 1)) = a + 1 from hfsucc.symm,
       show (⟨b.val, by omega⟩ : Fin (n + 1)) = b from Fin.ext rfl]
    rw [hsupp]; ring



/-- The wrap-edge data of the ear `intervalArm A a m` (the diagonal chord `(A ⟨a+m⟩, A ⟨a⟩)` and its
supports): a `ShortArc` on the wrap chord, and the nonnegativity of every support whose base is the wrap
edge `(A ⟨a+m⟩, A ⟨a⟩)`.  These are exactly the certificates the parent's weak convexity at an *arbitrary*
interval does NOT supply (the wrap chord is a diagonal, not a parent edge); everything else restricts. -/
structure IntervalWrapData {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) : Prop where
  /-- The wrap (diagonal) edge is a short arc. -/
  wrap_short : ShortArc (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩)
  /-- Every vertex is supported on the nonnegative side of the oriented wrap edge. -/
  wrap_support : ∀ v : ℕ, (hv : v < m + 1) →
    0 ≤ sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by have := hv; omega⟩)





/-- **Interior edges of the ear are parent edges, hence short.**  For a strictly/weakly convex parent and
an interior ear edge index `t < m`, the ear edge `(ear ⟨t⟩, ear ⟨t+1⟩) = (A ⟨a+t⟩, A ⟨a+t+1⟩)` is the
parent edge `t' = a + t`, which is a `ShortArc` (parent `edge_short`). -/
theorem intervalArm_interiorEdgeShort {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hb : a + m ≤ N) {t : ℕ} (ht : t < m) :
    ShortArc (A ⟨a + t, by omega⟩) (A ⟨a + t + 1, by omega⟩) := by
  have hedge := hA.closed_convex.edge_short ⟨a + t, by omega⟩
  -- (⟨a+t⟩ + 1 : Fin (N+1)) = ⟨a+t+1⟩ since a+t+1 ≤ N < N+1.
  have hsucc : (⟨a + t, by omega⟩ + 1 : Fin (N + 1)) = ⟨a + t + 1, by omega⟩ := by
    apply Fin.ext
    have : ((⟨a + t, by omega⟩ + 1 : Fin (N + 1)) : ℕ) = (a + t + 1) % (N + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rwa [hsucc] at hedge

/-- **Interior-base supports of the ear are parent supports, hence ≥ 0.**  For a weakly convex parent, an
interior ear edge `(A ⟨a+t⟩, A ⟨a+t+1⟩)` (`t < m`) supports any ear vertex `A ⟨a+v⟩` (`v ≤ m`) on the
nonnegative side, because it is the parent non-incident support `sOrient (A ⟨a+t⟩)(A ⟨a+t+1⟩)(A ⟨a+v⟩) ≥ 0`
(parent `edge_support`). -/
theorem intervalArm_interiorSupport {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hb : a + m ≤ N) {t v : ℕ} (ht : t < m) (hv : v < m + 1) :
    0 ≤ sOrient (A ⟨a + t, by omega⟩) (A ⟨a + t + 1, by omega⟩) (A ⟨a + v, by omega⟩) := by
  have hsupp := hA.closed_convex.edge_support ⟨a + t, by omega⟩ ⟨a + v, by omega⟩
  have hsucc : (⟨a + t, by omega⟩ + 1 : Fin (N + 1)) = ⟨a + t + 1, by omega⟩ := by
    apply Fin.ext
    have : ((⟨a + t, by omega⟩ + 1 : Fin (N + 1)) : ℕ) = (a + t + 1) % (N + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rwa [hsucc] at hsupp

/-- **The open hemisphere restricts to the ear.**  The parent's open-hemisphere normal `h` works verbatim
for the ear (the ear vertices are a subset of the parent vertices). -/
theorem intervalArm_openHemisphere {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hb : a + m ≤ N) :
    ∃ h : E3, ‖h‖ = 1 ∧ ∀ x : Fin (m + 1), 0 < (⟪h, (intervalArm A a m hb x : E3)⟫ : ℝ) := by
  obtain ⟨h, hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  exact ⟨h, hnorm, fun x => hhem _⟩



/-- **Component 3, sharpened.**  The ear `intervalArm A a m` (`2 ≤ m`, `a + m ≤ N`) of a weakly convex
parent `A` is itself weakly convex PROVIDED the wrap-edge data `IntervalWrapData` (the diagonal chord's
`ShortArc` and the nonnegativity of the supports based at the diagonal).  All other fields restrict from
the parent.

This isolates the genuine Component-3 residue (the wrap diagonal) and discharges the rest. -/
theorem weakConvex_intervalArm_of_wrap {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ N)
    (hwrap : IntervalWrapData A a m hb) :
    WeakConvexSphArm (intervalArm A a m hb) := by
  have hNz : NeZero (m + 1) := ⟨by omega⟩
  refine ⟨hm, ?_⟩
  refine ⟨by omega, ?_, ?_, ?_⟩
  · -- edge_short for every cyclic edge `i : Fin (m+1)`: interior (i < m) parent edge, or wrap (i = m).
    intro i
    by_cases hi : i.val < m
    · -- interior edge: (ear i, ear (i+1)) = (A ⟨a+i⟩, A ⟨a+i+1⟩).
      have hsucc : (i + 1 : Fin (m + 1)) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
        rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [intervalArm_apply, intervalArm_apply, hsucc]
      have := intervalArm_interiorEdgeShort hA hb (t := i.val) hi
      -- align ⟨a + (i+1).val⟩ to ⟨a + i + 1⟩.
      simpa only [show a + (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (m + 1)).val = a + i.val + 1 from rfl]
        using this
    · -- wrap edge: i.val = m, (i+1) wraps to 0.
      have him : i.val = m := by have := i.isLt; omega
      have hi0 : (i + 1 : Fin (m + 1)) = 0 := by
        apply Fin.ext
        have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
        rw [this, him]; simp [Nat.mod_self]
      rw [intervalArm_apply, hi0, intervalArm_apply]
      simp only [Fin.val_zero, Nat.add_zero]
      have halign : (A ⟨a + i.val, by have := i.isLt; omega⟩ : S2) = A ⟨a + m, by omega⟩ :=
        congrArg A (Fin.ext (by simp only [him]))
      rw [halign]
      exact hwrap.wrap_short
  · -- edge_support for every base edge `i` and vertex `j`.
    intro i j
    by_cases hi : i.val < m
    · -- interior base edge: parent support.
      have hsucc : (i + 1 : Fin (m + 1)) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
        rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [intervalArm_apply, intervalArm_apply, intervalArm_apply, hsucc]
      have := intervalArm_interiorSupport hA hb (t := i.val) (v := j.val) hi j.isLt
      simpa only [show a + (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (m + 1)).val = a + i.val + 1 from rfl]
        using this
    · -- wrap base edge: i.val = m, base = (A ⟨a+m⟩, A ⟨a⟩); use wrap_support at v = j.val.
      have him : i.val = m := by have := i.isLt; omega
      have hi0 : (i + 1 : Fin (m + 1)) = 0 := by
        apply Fin.ext
        have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
        rw [this, him]; simp [Nat.mod_self]
      rw [intervalArm_apply, hi0, intervalArm_apply, intervalArm_apply]
      simp only [Fin.val_zero, Nat.add_zero]
      have halign : (A ⟨a + i.val, by have := i.isLt; omega⟩ : S2) = A ⟨a + m, by omega⟩ :=
        congrArg A (Fin.ext (by simp only [him]))
      rw [halign]
      exact hwrap.wrap_support j.val j.isLt
  · -- open hemisphere restricts.
    obtain ⟨h, hnorm, hhem⟩ := intervalArm_openHemisphere hA hb (a := a) (m := m)
    exact ⟨h, hnorm, hhem⟩

/-- **Interior strict supports restrict.**  For a *strictly* convex parent, an interior ear edge
`(A ⟨a+t⟩, A ⟨a+t+1⟩)` (`t < m`) supports a non-incident ear vertex `A ⟨a+v⟩` strictly on the positive
side, whenever `a+v` is non-incident to the parent edge `a+t` (i.e. `a+v ≠ a+t` and `a+v ≠ a+t+1`). -/
theorem intervalArm_interiorStrictSupport {N : ℕ} {A : Fin (N + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hb : a + m ≤ N) {t v : ℕ} (ht : t < m) (hv : v < m + 1)
    (hne : v ≠ t) (hne1 : v ≠ t + 1) :
    0 < sOrient (A ⟨a + t, by omega⟩) (A ⟨a + t + 1, by omega⟩) (A ⟨a + v, by omega⟩) := by
  have hj1 : (⟨a + v, by omega⟩ : Fin (N + 1)) ≠ ⟨a + t, by omega⟩ := by
    intro h; apply hne
    have : a + v = a + t := congrArg Fin.val h
    omega
  -- the parent edge `a+t` and its `+1` as Fin: align `(⟨a+t⟩ + 1)` to `⟨a+t+1⟩`.
  have hsucc : (⟨a + t, by omega⟩ + 1 : Fin (N + 1)) = ⟨a + t + 1, by omega⟩ := by
    apply Fin.ext
    have : ((⟨a + t, by omega⟩ + 1 : Fin (N + 1)) : ℕ) = (a + t + 1) % (N + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hj2 : (⟨a + v, by omega⟩ : Fin (N + 1)) ≠ (⟨a + t, by omega⟩ : Fin (N + 1)) + 1 := by
    rw [hsucc]; intro h; apply hne1
    have : a + v = a + t + 1 := congrArg Fin.val h
    omega
  have hstr := hA.closed_convex.strict_nonincident ⟨a + t, by omega⟩ ⟨a + v, by omega⟩ hj1 hj2
  rwa [hsucc] at hstr

/-- The strict-ear wrap data: as `IntervalWrapData`, plus the *strict* support of every non-incident
vertex against the wrap (diagonal) edge.  This is the only genuinely-new strict field for the ear; the
interior strict non-incidence restricts from the parent. -/
structure IntervalWrapDataStrict {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) : Prop where
  toWeak : IntervalWrapData A a m hb
  /-- The wrap (diagonal) edge supports every NON-incident vertex strictly.  Non-incidence against the
  cyclic wrap edge `(vertex m, vertex 0)` means `v ≠ m` (not the base tail) and `v ≠ 0`... but vertex `0`
  IS the wrap edge's head, so the non-incident condition for the wrap edge `(m, 0)` is `v ≠ m ∧ v ≠ 0`.
  -/
  wrap_strict : ∀ v : ℕ, (hv : v < m + 1) → v ≠ m → v ≠ 0 →
    0 < sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by have := hv; omega⟩)

/-- **Component 3, strict version.**  The ear `intervalArm A a m` (`2 ≤ m`) of a *strictly* convex parent
`A` is strictly convex GIVEN the strict wrap data.  The interior strict non-incidences restrict from the
parent; the wrap base's strict non-incidence is the residue (`wrap_strict`). -/
theorem strictConvex_intervalArm_of_wrap {N : ℕ} {A : Fin (N + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ N)
    (hwrap : IntervalWrapDataStrict A a m hb) :
    StrictConvexSphArm (intervalArm A a m hb) := by
  have hNz : NeZero (m + 1) := ⟨by omega⟩
  -- reuse the weak assembly for edge_short / edge_support / open_hemisphere.
  have hweak := weakConvex_intervalArm_of_wrap (strictConvexSphArm_toWeak hA) hm hb hwrap.toWeak
  refine ⟨hm, ?_⟩
  refine ⟨by omega, hweak.closed_convex.edge_short, hweak.closed_convex.edge_support, ?_,
    hweak.closed_convex.open_hemisphere⟩
  -- strict_nonincident: tested vertex `j` non-incident to base edge `i`.
  intro i j hji hji1
  by_cases hi : i.val < m
  · -- interior base edge: parent strict non-incidence at (a+i, a+j).
    have hsucc : (i + 1 : Fin (m + 1)) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
      apply Fin.ext
      have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
      rw [this, Nat.mod_eq_of_lt (by omega)]
    -- ear non-incidence j ≠ i, j ≠ i+1 transfers to value non-incidence v ≠ t, v ≠ t+1.
    have hvne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hvne1 : j.val ≠ i.val + 1 := by
      intro h; apply hji1; rw [hsucc]; exact Fin.ext h
    rw [intervalArm_apply, intervalArm_apply, intervalArm_apply, hsucc]
    have := intervalArm_interiorStrictSupport hA hb (t := i.val) (v := j.val) hi j.isLt hvne hvne1
    simpa only [show a + (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (m + 1)).val = a + i.val + 1 from rfl]
      using this
  · -- wrap base edge: i.val = m, base = (A ⟨a+m⟩, A ⟨a⟩); use wrap_strict at v = j.val (j ≠ m, j ≠ 0).
    have him : i.val = m := by have := i.isLt; omega
    have hi0 : (i + 1 : Fin (m + 1)) = 0 := by
      apply Fin.ext
      have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
      rw [this, him]; simp [Nat.mod_self]
    -- j ≠ i means j.val ≠ m; j ≠ i+1 = 0 means j.val ≠ 0.
    have hjm : j.val ≠ m := by intro h; apply hji; apply Fin.ext; rw [him]; exact h
    have hj0 : j.val ≠ 0 := by intro h; apply hji1; rw [hi0]; apply Fin.ext; simp [h]
    rw [intervalArm_apply, hi0, intervalArm_apply, intervalArm_apply]
    simp only [Fin.val_zero, Nat.add_zero]
    have halign : (A ⟨a + i.val, by have := i.isLt; omega⟩ : S2) = A ⟨a + m, by omega⟩ :=
      congrArg A (Fin.ext (by simp only [him]))
    rw [halign]
    exact hwrap.wrap_strict j.val j.isLt hjm hj0















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













/-- **(Brick 2) Adjacent fold contradicts `PositiveJoints`.**  When `j = i + 2` the betweenness
`A i ∈ span≥0 {A (i+1), A (i+2)}` puts the cut vertex `A i` on the minor arc between the apex's two
neighbours, forcing the interior joint at index `i` (apex `A (i+1)`) to angle `0`
(`lastCorner_hcol_forces_joint_zero`), contradicting `PositiveJoints A`. -/
theorem foldedFlat_adjacent_contradiction {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hpos : PositiveJoints A)
    {i : ℕ} (hi2 : i + 2 < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨i + 2, hi2⟩ : E3)} : Set E3)) :
    False := by
  -- short edge `(A (i+1), A i)` from the arm edge `(A i, A (i+1))` reversed.
  have hedge : ShortArc (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) := by
    have he := hA.closed_convex.edge_short ⟨i, by omega⟩
    have hsucc : ((⟨i, by omega⟩ : Fin (n + 1)) + 1) = (⟨i + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc] at he
  have hsa : ShortArc (A ⟨i + 1, by omega⟩) (A ⟨i, by omega⟩) := hedge.symm
  -- the betweenness forces `jointAngle A ⟨i⟩ = 0`.
  have hzero : jointAngle A ⟨i, by omega⟩ = 0 :=
    lastCorner_hcol_forces_joint_zero (N := n) (A := A) (k := i) (by omega) hsa hcol
  -- contradict `PositiveJoints`.
  have hposi := hpos ⟨i, by omega⟩
  rw [hzero] at hposi
  exact lt_irrefl 0 hposi







/-- **The `(0, n-1)` tail-fold premise** (design §8 residue).  At the `(0, n-1)` boundary fold, the
last vertex `A (last)` is folded onto the ray from `A 0` to `A ⟨n-1⟩`:
`sDist (A 0)(A ⟨n-1⟩) = endpt A + sDist (A last)(A ⟨n-1⟩)`.  Genuinely exceeds the `(0, n-1)`
betweenness (`A 0 ∈ span≥0 {A 1, A ⟨n-1⟩}`); the design §8 master brick produces it from the two
boundary edge supports + the positive-coefficient fold datum.  Named, satisfiable. -/
def TailFoldBoundary {n : ℕ} (A : Fin (n + 1) → S2) (hn1 : n - 1 < n + 1) : Prop :=
  sDist (A ⟨0, by omega⟩) (A ⟨n - 1, hn1⟩)
    = endpt A + sDist (A (Fin.last n)) (A ⟨n - 1, hn1⟩)



/-- **(Brick 5) The `(0, n-1)` boundary transport.**  From the named tail-fold premise, the diagonal
inequality `sDist (A 0)(A ⟨n-1⟩) ≤ sDist (B 0)(B ⟨n-1⟩)`, and the equal last side
(`SameSides` at side `n-1`), `ZinanFFCT18.endpoint_le_of_tail_fold` gives `endpt A ≤ endpt B`. -/
theorem foldedFlat_boundary_j_eq_n_minus_one {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hside : SameSides A B)
    (htail : TailFoldBoundary A (by omega))
    (hdiag : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
      ≤ sDist (B ⟨0, by omega⟩) (B ⟨n - 1, by omega⟩)) :
    endpt A ≤ endpt B := by
  -- the tail-fold equation in the `endpoint_le_of_tail_fold` shape.
  have hflat : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
      = sDist (A ⟨0, by omega⟩) (A (Fin.last n)) + sDist (A (Fin.last n)) (A ⟨n - 1, by omega⟩) := by
    have h := htail
    rw [TailFoldBoundary, endpt] at h
    -- `endpt A = sDist (A 0)(A last)`; reconcile the `⟨0,_⟩` and `0` indices.
    have h00 : (A ⟨0, by omega⟩ : S2) = A 0 := by congr 1
    rw [h00] at h ⊢
    linarith [h]
  -- the equal last side: `sDist (A last)(A ⟨n-1⟩) = sDist (B last)(B ⟨n-1⟩)`.
  have hs := hside ⟨n - 1, by omega⟩
  -- `(⟨n-1,_⟩ : Fin n).castSucc = ⟨n-1,_⟩` and `.succ = ⟨n,_⟩` (values, with `hn`).
  have hcast : ((⟨n - 1, by omega⟩ : Fin n).castSucc) = (⟨n - 1, by omega⟩ : Fin (n + 1)) :=
    Fin.ext (by simp)
  have hsucc : ((⟨n - 1, by omega⟩ : Fin n).succ) = (⟨n, by omega⟩ : Fin (n + 1)) :=
    Fin.ext (by simp; omega)
  have hsA : sideLen A (⟨n - 1, by omega⟩ : Fin n)
      = sDist (A ⟨n - 1, by omega⟩) (A ⟨n, by omega⟩) := by
    rw [sideLen, hcast, hsucc]
  have hsB : sideLen B (⟨n - 1, by omega⟩ : Fin n)
      = sDist (B ⟨n - 1, by omega⟩) (B ⟨n, by omega⟩) := by
    rw [sideLen, hcast, hsucc]
  rw [hsA, hsB] at hs
  -- `A (Fin.last n) = A ⟨n, _⟩`, then symmetrise to the `(last, n-1)` orientation.
  have hlastA : (A (Fin.last n) : S2) = A ⟨n, by omega⟩ := by congr 1
  have hlastB : (B (Fin.last n) : S2) = B ⟨n, by omega⟩ := by congr 1
  have hsideLast : sDist (A (Fin.last n)) (A ⟨n - 1, by omega⟩)
      = sDist (B (Fin.last n)) (B ⟨n - 1, by omega⟩) := by
    rw [hlastA, hlastB, sDist_comm (A ⟨n, by omega⟩) (A ⟨n - 1, by omega⟩),
        sDist_comm (B ⟨n, by omega⟩) (B ⟨n - 1, by omega⟩)]
    exact hs
  -- assemble via the landed FFCT18 arithmetic.
  have hkey := endpoint_le_of_tail_fold (A0 := A ⟨0, by omega⟩) (An1 := A ⟨n - 1, by omega⟩)
    (An := A (Fin.last n)) (B0 := B ⟨0, by omega⟩) (Bn1 := B ⟨n - 1, by omega⟩)
    (Bn := B (Fin.last n)) hflat hdiag hsideLast
  -- `hkey : sDist (A 0)(A last) ≤ sDist (B 0)(B last)`, i.e. `endpt A ≤ endpt B`.
  have heA : endpt A = sDist (A ⟨0, by omega⟩) (A (Fin.last n)) := by
    rw [endpt]; congr 1
  have heB : endpt B = sDist (B ⟨0, by omega⟩) (B (Fin.last n)) := by
    rw [endpt]; congr 1
  rw [heA, heB]; exact hkey
























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



/-- **`endpt` is reversal-invariant.**  `endpt (revArm A) = sDist (revArm A 0)(revArm A (last)) =
sDist (A n)(A 0) = sDist (A 0)(A n) = endpt A` (`sDist_comm`). -/
theorem endpt_revArm {n : ℕ} (A : Fin (n + 1) → S2) : endpt (revArm A) = endpt A := by
  unfold endpt
  have h0 : (revArm A 0 : S2) = A (Fin.last n) := by
    show A (revFin 0) = _
    exact congrArg A (Fin.ext (by simp [revFin_val, Fin.last]))
  have hl : (revArm A (Fin.last n) : S2) = A 0 := by
    show A (revFin (Fin.last n)) = _
    exact congrArg A (Fin.ext (by simp [revFin_val, Fin.last]))
  rw [h0, hl, sDist_comm]



















/-- **The det3 row-expansion identity.**  With `a•A 1 + b•A n = A 0`,
`a·det3 (A n)(A 1)(A m) = det3 (A n)(A 0)(A m)` (the `b•A n` term vanishes, `det3 x x y = 0`). -/
theorem det3_rowExpand_wrap {a b : ℝ} {An A1 An0 Am : E3}
    (hcoeff : a • A1 + b • An = An0) :
    a * det3 An A1 Am = det3 An An0 Am := by
  rw [← hcoeff, det3_add_mid, det3_smul_mid, det3_smul_mid]
  have hself : det3 An An Am = 0 := by simp only [det3]; ring
  rw [hself, mul_zero, add_zero]

/-- **The A-side wrap supports are derivable from the `(0, n)` betweenness.**  Given the nondegenerate
decomposition `a•A 1 + b•A n = A 0` (`0 < a`) and the parent weak convexity, every interior vertex
`A ⟨1 + v⟩` (`v < n`) is on the nonnegative side of the wrap diagonal `(A n, A 1)`:
`0 ≤ sOrient (A n)(A 1)(A ⟨1+v⟩)`.  The parent wrap-edge `(n, 0)` support
`0 ≤ sOrient (A n)(A 0)(A ⟨1+v⟩)` row-expands through the betweenness. -/
theorem intervalWrap_support_of_betweenness {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hn : 2 ≤ n)
    {a b : ℝ} (hapos : 0 < a)
    (hcoeff : a • (A ⟨1, by omega⟩ : E3) + b • (A ⟨n, by omega⟩ : E3) = (A ⟨0, by omega⟩ : E3))
    {v : ℕ} (hv : v < n) :
    0 ≤ sOrient (A ⟨n, by omega⟩) (A ⟨1, by omega⟩) (A ⟨1 + v, by omega⟩) := by
  -- parent wrap-edge `(n, 0)` support: edge index `⟨n⟩ : Fin (n+1)`, its `+1` wraps to `⟨0⟩`.
  have hwrapEdge : (⟨n, by omega⟩ + 1 : Fin (n + 1)) = (⟨0, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have : ((⟨n, by omega⟩ + 1 : Fin (n + 1)) : ℕ) = (n + 1) % (n + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_self]
  have hpar : 0 ≤ sOrient (A ⟨n, by omega⟩) (A (⟨n, by omega⟩ + 1)) (A ⟨1 + v, by omega⟩) :=
    hA.closed_convex.edge_support ⟨n, by omega⟩ ⟨1 + v, by omega⟩
  rw [hwrapEdge] at hpar
  -- `hpar : 0 ≤ sOrient (A n)(A 0)(A ⟨1+v⟩)`, i.e. `0 ≤ det3 (A n)(A 0)(A ⟨1+v⟩)`.
  -- row expansion: `a · det3 (A n)(A 1)(A ⟨1+v⟩) = det3 (A n)(A 0)(A ⟨1+v⟩) ≥ 0`.
  have hrow := det3_rowExpand_wrap (a := a) (b := b)
    (An := (A ⟨n, by omega⟩ : E3)) (A1 := (A ⟨1, by omega⟩ : E3))
    (An0 := (A ⟨0, by omega⟩ : E3)) (Am := (A ⟨1 + v, by omega⟩ : E3)) hcoeff
  -- unfold sOrient = det3 and conclude.
  have hpar' : 0 ≤ det3 (A ⟨n, by omega⟩ : E3) (A ⟨0, by omega⟩ : E3) (A ⟨1 + v, by omega⟩ : E3) :=
    hpar
  have hge : 0 ≤ a * det3 (A ⟨n, by omega⟩ : E3) (A ⟨1, by omega⟩ : E3)
      (A ⟨1 + v, by omega⟩ : E3) := by rw [hrow]; exact hpar'
  -- `a > 0` and `a * x ≥ 0` ⟹ `x ≥ 0`.
  exact (mul_nonneg_iff_of_pos_left hapos).mp hge

/-- **The A-side wrap `ShortArc` is derivable.**  `A n ≠ A 1` from `NoNonadjacentRepeat` (the pair
`(1, n)` is nonadjacent for `n ≥ 3`); non-antipodal from the parent open hemisphere. -/
theorem intervalWrap_shortArc_of_parent {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A) (hn3 : 3 ≤ n) :
    ShortArc (A ⟨n, by omega⟩) (A ⟨1, by omega⟩) := by
  -- distinctness from NoNonadjacentRepeat at (1, n): 1 + 2 ≤ n.
  have hdist : A ⟨1, by omega⟩ ≠ A ⟨n, by omega⟩ := hnr 1 n (by omega) (by omega) (by omega)
  -- non-antipodality from the open hemisphere.
  obtain ⟨h, _, hhem⟩ := hA.closed_convex.open_hemisphere
  refine ⟨fun he => hdist he.symm, fun hanti => ?_⟩
  -- `(A n : E3) = -(A 1 : E3)` would give `0 < ⟪h, A n⟫ = -⟪h, A 1⟫ < 0`.
  have hn0 : 0 < (⟪h, (A ⟨n, by omega⟩ : E3)⟫ : ℝ) := hhem ⟨n, by omega⟩
  have h10 : 0 < (⟪h, (A ⟨1, by omega⟩ : E3)⟫ : ℝ) := hhem ⟨1, by omega⟩
  rw [hanti, inner_neg_right] at hn0
  linarith

/-- **The A-side weak interval wrap data, from the `(0, n)` betweenness.**  Assembles
`IntervalWrapData A 1 (n-1)` (the wrap diagonal `(A n, A 1)`) from the parent + the betweenness, with
`a > 0` supplied by FFCT23's nondegenerate datum. -/
theorem intervalWrapData_of_betweenness {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A) (hn3 : 3 ≤ n)
    {a b : ℝ} (hapos : 0 < a)
    (hcoeff : a • (A ⟨1, by omega⟩ : E3) + b • (A ⟨n, by omega⟩ : E3) = (A ⟨0, by omega⟩ : E3)) :
    IntervalWrapData A 1 (n - 1) (by omega) := by
  have hn : 2 ≤ n := by omega
  have h1n : 1 + (n - 1) = n := by omega
  have hidx : (⟨1 + (n - 1), by omega⟩ : Fin (n + 1)) = (⟨n, by omega⟩ : Fin (n + 1)) := Fin.ext h1n
  refine
    { wrap_short := ?_
      wrap_support := ?_ }
  · -- the wrap diagonal `(A ⟨1+(n-1)⟩, A ⟨1⟩) = (A n, A 1)`.
    rw [hidx]
    exact intervalWrap_shortArc_of_parent hA hnr hn3
  · intro v hv
    -- `1 + (n-1) = n`; support at `A ⟨1+v⟩`, `v < (n-1)+1 = n`.
    rw [hidx]
    exact intervalWrap_support_of_betweenness hA hn hapos hcoeff (v := v) (by have := hv; omega)

/-- **The weak ear `hAe` from the `(0, n)` betweenness, DISCHARGED.**  Combining
`intervalWrapData_of_betweenness` with FFCT52's `weakConvex_intervalArm_of_wrap`: the interval `[1..n]`
of `A` is weakly convex, no certificate needed beyond the parent + the betweenness coefficients. -/
theorem weakEar_of_betweenness {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A) (hn3 : 3 ≤ n)
    {a b : ℝ} (hapos : 0 < a)
    (hcoeff : a • (A ⟨1, by omega⟩ : E3) + b • (A ⟨n, by omega⟩ : E3) = (A ⟨0, by omega⟩ : E3)) :
    WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)) :=
  weakConvex_intervalArm_of_wrap hA (by omega) (by omega)
    (intervalWrapData_of_betweenness hA hnr hn3 hapos hcoeff)

/-- **The A-side wrap from the raw NNReal span membership.**  Extracts the FFCT23 nondegenerate datum
(`0 < a`, `0 < b`, `a•A 1 + b•A n = A 0`) from the betweenness `A 0 ∈ span≥0 {A 1, A n}` and feeds
`weakEar_of_betweenness`.  This is the end-to-end `hAe` supplier the `(0, n)` branch consumes — fully
discharged. -/
theorem weakEar_of_span {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    (hn3 : 3 ≤ n)
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3)) :
    WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)) := by
  -- FFCT23's nondegenerate datum at `(i, j) = (0, n)` (needs `0 + 2 < n`, i.e. `n ≥ 3`).
  have hcol' : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨0 + 1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3) := by
    have hidx : (⟨0 + 1, by omega⟩ : Fin (n + 1)) = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
    rwa [hidx]
  obtain ⟨a, b, hapos, _hbpos, hcoeff⟩ :=
    far_fold_nondeg_datum_of_no_repeat hA hnr (i := 0) (j := n) (by omega) (by omega) hcol'
  -- align the `0 + 1` index to `1`.
  have hcoeff' : (a : ℝ) • (A ⟨1, by omega⟩ : E3) + (b : ℝ) • (A ⟨n, by omega⟩ : E3)
      = (A ⟨0, by omega⟩ : E3) := by
    have hidx : (⟨0 + 1, by omega⟩ : Fin (n + 1)) = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
    rwa [hidx] at hcoeff
  exact weakEar_of_betweenness hA hnr hn3 hapos hcoeff'



/-- **The B-side strict diagonal support** — the genuine residue.  For a strictly convex `B` and the
interval `[1..n]`, every interior vertex `B ⟨1+v⟩` (`v ≠ 0`, `v ≠ n−1`, i.e. not a diagonal endpoint)
is **strictly** on the positive side of the wrap diagonal `(B n, B 1)`:
`0 < sOrient (B n)(B 1)(B ⟨1+v⟩)`.  This is the convex-position fact (diagonal of a strictly convex
polygon); NOT a parent edge support (FFCT52 §4), so genuinely beyond the strict-non-incidence the
substrate banks. -/
def StrictDiagonalSupport {n : ℕ} (B : Fin (n + 1) → S2) (hn3 : 3 ≤ n) : Prop :=
  ∀ v : ℕ, (hv : v < n) → v ≠ 0 → v ≠ n - 1 →
    0 < sOrient (B ⟨n, by omega⟩) (B ⟨1, by omega⟩) (B ⟨1 + v, by have := hv; omega⟩)



/-- **The B-side strict wrap `ShortArc` is derivable** (same hemisphere/no-repeat route as the A side):
`B n ≠ B 1` from strict convexity's distinctness; non-antipodal from the hemisphere. -/
theorem intervalWrap_shortArc_strict {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    ShortArc (B ⟨n, by omega⟩) (B ⟨1, by omega⟩) := by
  -- distinctness: the strict non-incidence at the wrap edge `(n, 0)` with tested vertex `1`.
  -- simplest: `(1, n)` strict support is positive ⟹ distinct; but we route through hemisphere + a
  -- direct distinctness from strict_nonincident of edge `0` at vertex `n`.
  -- distinct: B ⟨1⟩ ≠ B ⟨n⟩ since edge `(0,1)` strictly supports `n` (non-incident), so positive,
  -- hence the three points are not collinear ⟹ in particular B 1 ≠ B n.
  obtain ⟨h, _, hhem⟩ := hB.closed_convex.open_hemisphere
  -- distinctness via strict non-incidence of the parent edge `(1, 2)` is awkward; use the wrap-edge
  -- strict support of vertex `1` against edge `(n, 0)`.
  have hne_fin : (⟨1, by omega⟩ : Fin (n + 1)) ≠ (⟨n, by omega⟩ : Fin (n + 1)) :=
    fun he => by have : (1 : ℕ) = n := congrArg Fin.val he; omega
  -- the parent edge `⟨n⟩` with `+1 = ⟨0⟩`; vertex `1` is non-incident (`1 ≠ n`, `1 ≠ 0`).
  have hwrapEdge : (⟨n, by omega⟩ + 1 : Fin (n + 1)) = (⟨0, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have : ((⟨n, by omega⟩ + 1 : Fin (n + 1)) : ℕ) = (n + 1) % (n + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_self]
  have hjne : (⟨1, by omega⟩ : Fin (n + 1)) ≠ (⟨n, by omega⟩ : Fin (n + 1)) := hne_fin
  have hjne1 : (⟨1, by omega⟩ : Fin (n + 1)) ≠ (⟨n, by omega⟩ : Fin (n + 1)) + 1 := by
    rw [hwrapEdge]; intro he; have : (1 : ℕ) = 0 := congrArg Fin.val he; omega
  have hstr := hB.closed_convex.strict_nonincident ⟨n, by omega⟩ ⟨1, by omega⟩ hjne hjne1
  rw [hwrapEdge] at hstr
  -- `hstr : 0 < sOrient (B n)(B 0)(B 1)`, so in particular B n, B 1 distinct.
  refine ⟨?_, fun hanti => ?_⟩
  · -- distinctness: if B n = B 1 then sOrient (B n)(B 0)(B 1) = sOrient (B n)(B 0)(B n) = 0 < 0.
    intro he
    rw [he] at hstr
    have hz : sOrient (B ⟨1, by omega⟩) (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) = 0 := by
      simp only [sOrient, det3]; ring
    rw [hz] at hstr; exact lt_irrefl 0 hstr
  · -- non-antipodality from the hemisphere.
    have hn0 : 0 < (⟪h, (B ⟨n, by omega⟩ : E3)⟫ : ℝ) := hhem ⟨n, by omega⟩
    have h10 : 0 < (⟪h, (B ⟨1, by omega⟩ : E3)⟫ : ℝ) := hhem ⟨1, by omega⟩
    rw [hanti, inner_neg_right] at hn0
    linarith

/-- **The B-side strict interval wrap data, from the named residue.**  Assembles
`IntervalWrapDataStrict B 1 (n-1)` from the parent (the weak wrap supports of `B` restrict trivially —
`B`'s edge supports are nonneg) and the named `StrictDiagonalSupport`. -/
theorem intervalWrapDataStrict_of_diagonal {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n)
    (hdiag : StrictDiagonalSupport B (by omega)) :
    IntervalWrapDataStrict B 1 (n - 1) (by omega) := by
  have hn : 2 ≤ n := by omega
  have h1n : 1 + (n - 1) = n := by omega
  have hidx : (⟨1 + (n - 1), by omega⟩ : Fin (n + 1)) = (⟨n, by omega⟩ : Fin (n + 1)) := Fin.ext h1n
  -- weak wrap supports of B: from B's strict (hence weak) edge support at the wrap edge.
  have hBw : WeakConvexSphArm B := strictConvexSphArm_toWeak hB
  refine
    { toWeak :=
        { wrap_short := ?_
          wrap_support := ?_ }
      wrap_strict := ?_ }
  · rw [hidx]
    exact intervalWrap_shortArc_strict hB hn3
  · -- weak support: the wrap diagonal `(B n, B 1)` supports every interior vertex nonneg.  For the two
    -- diagonal endpoints (`v = 0` ⟹ vertex `B 1`; `v = n-1` ⟹ vertex `B n`) the support is `0` (a
    -- repeated argument); for the rest it is the strict residue weakened.
    intro v hv
    rw [hidx]
    by_cases hv0 : v = 0
    · subst hv0
      have hidx0 : (⟨1 + 0, by omega⟩ : Fin (n + 1)) = (⟨1, by omega⟩ : Fin (n + 1)) :=
        Fin.ext rfl
      rw [hidx0, sOrient]
      have hz : det3 (B ⟨n, by omega⟩ : E3) (B ⟨1, by omega⟩ : E3) (B ⟨1, by omega⟩ : E3) = 0 := by
        simp only [det3]; ring
      rw [hz]
    · by_cases hvn : v = n - 1
      · subst hvn
        rw [sOrient, hidx]
        have hz : det3 (B ⟨n, by omega⟩ : E3) (B ⟨1, by omega⟩ : E3) (B ⟨n, by omega⟩ : E3) = 0 := by
          simp only [det3]; ring
        rw [hz]
      · exact le_of_lt (hdiag v (by have := hv; omega) hv0 hvn)
  · -- the strict wrap support: exactly the named residue (for `v ≠ 0`, `v ≠ m = n-1`).
    intro v hv hvm hv0
    rw [hidx]
    exact hdiag v (by have := hv; omega) hv0 hvm

/-- **The strict ear `hBe` from the named diagonal residue, DISCHARGED modulo `StrictDiagonalSupport`.**
Combining `intervalWrapDataStrict_of_diagonal` with FFCT52's `strictConvex_intervalArm_of_wrap`. -/
theorem strictEar_of_diagonal {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n)
    (hdiag : StrictDiagonalSupport B (by omega)) :
    StrictConvexSphArm (intervalArm B 1 (n - 1) (by omega)) :=
  strictConvex_intervalArm_of_wrap hB (by omega) (by omega)
    (intervalWrapDataStrict_of_diagonal hB hn3 hdiag)







/-- **The interval certs `(hAe, hBe)` for the `(0, n)` branch.**  The weak ear `hAe` is **discharged
unconditionally** from the betweenness (the A-side row expansion); the strict ear `hBe` is supplied by
the named B-side residue `StrictDiagonalSupport`.  This is the precise content of FFCT53's `hivl` at the
boundary fold, with the A side eliminated and the B side named. -/
theorem intervalCerts_of_betweenness_and_strictDiagonal {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n)
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3))
    (hdiag : StrictDiagonalSupport B (by omega)) :
    WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)) ∧
      StrictConvexSphArm (intervalArm B 1 (n - 1) (by omega)) :=
  ⟨weakEar_of_span hA hnr hn3 hcol, strictEar_of_diagonal hB hn3 hdiag⟩



























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



/-- Index arithmetic for `Fin (n + 1)`: the successor of `⟨k, _⟩` is `⟨k+1, _⟩` when `k + 1 < n + 1`. -/
theorem succ_mk {n k : ℕ} (hk : k < n + 1) (hk1 : k + 1 < n + 1) :
    ((⟨k, hk⟩ : Fin (n + 1)) + 1) = (⟨k + 1, hk1⟩ : Fin (n + 1)) := by
  apply Fin.ext
  have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show k + 1 < n + 1 by omega)]

/-- **Brick 1 base case (`v = 1`).**  The arc-interior vertex `B 2` is strictly on the positive side
of the wrap diagonal `(B n, B 1)`:  `0 < sOrient (B n) (B 1) (B 2)`.

Proof: `sOrient (B n)(B 1)(B 2) = det3 (B n)(B 1)(B 2)`.  By the cyclic rotation
`det3 (B n)(B 1)(B 2) = det3 (B 1)(B 2)(B n)`, this is the *strict non-incidence* support of the
parent edge `(B 1, B 2)` at the vertex `B n` (which is non-incident: `n ≠ 1` and `n ≠ 2` as `n ≥ 3`). -/
theorem strictDiagonal_base {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    0 < sOrient (B ⟨n, by omega⟩) (B ⟨1, by omega⟩) (B ⟨2, by omega⟩) := by
  -- the parent edge `(1, 2)`: `⟨1⟩ + 1 = ⟨2⟩`.
  have hsucc : ((⟨1, by omega⟩ : Fin (n + 1)) + 1) = (⟨2, by omega⟩ : Fin (n + 1)) :=
    succ_mk (by omega) (by omega)
  -- vertex `n` is non-incident to edge `(1, 2)`.
  have hne1 : (⟨n, by omega⟩ : Fin (n + 1)) ≠ (⟨1, by omega⟩ : Fin (n + 1)) := by
    intro he; have : n = 1 := congrArg Fin.val he; omega
  have hne2 : (⟨n, by omega⟩ : Fin (n + 1)) ≠ (⟨1, by omega⟩ : Fin (n + 1)) + 1 := by
    rw [hsucc]; intro he; have : n = 2 := congrArg Fin.val he; omega
  have hstr := hB.closed_convex.strict_nonincident ⟨1, by omega⟩ ⟨n, by omega⟩ hne1 hne2
  rw [hsucc] at hstr
  -- `hstr : 0 < sOrient (B 1) (B 2) (B n)`.  Cyclically rotate to `sOrient (B n) (B 1) (B 2)`.
  rw [sOrient] at hstr ⊢
  rwa [det3_cyclic (B ⟨n, by omega⟩ : E3) (B ⟨1, by omega⟩ : E3) (B ⟨2, by omega⟩ : E3)]

/-- **Brick 1 top case (`v = n − 2`).**  The arc-interior vertex `B ⟨n−1⟩` is strictly on the
positive side of the wrap diagonal `(B n, B 1)`:  `0 < sOrient (B n) (B 1) (B ⟨n−1⟩)`.

Proof: `det3 (B n)(B 1)(B ⟨n−1⟩) = det3 (B ⟨n−1⟩)(B n)(B 1)` (cyclic), the strict non-incidence
support of the parent edge `(B ⟨n−1⟩, B n)` at the vertex `B 1` (non-incident: `1 ≠ n−1` and `1 ≠ n`
as `n ≥ 3`). -/
theorem strictDiagonal_top {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    0 < sOrient (B ⟨n, by omega⟩) (B ⟨1, by omega⟩) (B ⟨n - 1, by omega⟩) := by
  -- the parent edge `(n-1, n)`: `⟨n-1⟩ + 1 = ⟨n⟩`.
  have hsucc : ((⟨n - 1, by omega⟩ : Fin (n + 1)) + 1) = (⟨n, by omega⟩ : Fin (n + 1)) := by
    have h := succ_mk (n := n) (k := n - 1) (by omega) (by omega)
    have he : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = (⟨n, by omega⟩ : Fin (n + 1)) :=
      Fin.ext (show n - 1 + 1 = n by omega)
    rw [he] at h; exact h
  -- vertex `1` is non-incident to edge `(n-1, n)`.
  have hne1 : (⟨1, by omega⟩ : Fin (n + 1)) ≠ (⟨n - 1, by omega⟩ : Fin (n + 1)) := by
    intro he; have : (1 : ℕ) = n - 1 := congrArg Fin.val he; omega
  have hne2 : (⟨1, by omega⟩ : Fin (n + 1)) ≠ (⟨n - 1, by omega⟩ : Fin (n + 1)) + 1 := by
    rw [hsucc]; intro he; have : (1 : ℕ) = n := congrArg Fin.val he; omega
  have hstr := hB.closed_convex.strict_nonincident ⟨n - 1, by omega⟩ ⟨1, by omega⟩ hne1 hne2
  rw [hsucc] at hstr
  -- `hstr : 0 < sOrient (B ⟨n-1⟩) (B n) (B 1)`.  Rotate to `sOrient (B n) (B 1) (B ⟨n-1⟩)`.
  rw [sOrient] at hstr ⊢
  -- det3 (B n)(B 1)(B ⟨n-1⟩) = det3 (B ⟨n-1⟩)(B n)(B 1) by two cyclic rotations.
  rw [det3_cyclic (B ⟨n, by omega⟩ : E3) (B ⟨1, by omega⟩ : E3) (B ⟨n - 1, by omega⟩ : E3),
      det3_cyclic (B ⟨1, by omega⟩ : E3) (B ⟨n - 1, by omega⟩ : E3) (B ⟨n, by omega⟩ : E3)]
  exact hstr



/-- **The genuine interior residue of `StrictDiagonalSupport`.**  Only the *strictly interior* arc
vertices (`2 ≤ v`, `v ≤ n − 3`, i.e. excluding both the base vertex `B 2` and the top vertex
`B ⟨n−1⟩`, which are discharged unconditionally) on the positive side of the wrap diagonal.  This is
the irreducible spherical convex-position core; the local Grassmann–Plücker route is provably
sign-indeterminate, so a faithful proof needs a 2D-projection / global-hemisphere argument. -/
def StrictDiagonalInteriorSupport {n : ℕ} (B : Fin (n + 1) → S2) (hn3 : 3 ≤ n) : Prop :=
  ∀ v : ℕ, (hv : v < n) → 2 ≤ v → v ≤ n - 3 →
    0 < sOrient (B ⟨n, by omega⟩) (B ⟨1, by omega⟩) (B ⟨1 + v, by have := hv; omega⟩)





/-- **Brick 1 assembled: `StrictDiagonalSupport` from the interior residue + the discharged base/top
cases.**  Splitting the arc-interior range `v ∈ {1, …, n−2}`: `v = 1` is `strictDiagonal_base`,
`v = n − 2` is `strictDiagonal_top`, and the strict interior `2 ≤ v ≤ n − 3` is the named residue.
This is the precise content of FFCT54's `StrictDiagonalSupport`, with the two boundary cases of the
arc KILLED unconditionally. -/
theorem strictDiagonalSupport_of_interior {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n)
    (hint : StrictDiagonalInteriorSupport B hn3) :
    ProofsInTheBook.ZinanFFCT54.StrictDiagonalSupport B hn3 := by
  intro v hv hv0 hvn
  -- `v ∈ {1, …, n-2}` (from `v < n`, `v ≠ 0`, `v ≠ n-1`).  Split base / interior / top.
  rcases Nat.lt_or_ge v 2 with hlt2 | hge2
  · -- `v = 1` (since `v ≠ 0`, `v < 2`).
    have hv1 : v = 1 := by omega
    subst hv1
    -- align `B ⟨1+1⟩ = B ⟨2⟩`.
    have hidx : (⟨1 + 1, by have := hv; omega⟩ : Fin (n + 1)) = (⟨2, by omega⟩ : Fin (n + 1)) :=
      Fin.ext rfl
    rw [hidx]
    exact strictDiagonal_base hB hn3
  · rcases Nat.lt_or_ge (n - 3) v with hgt3 | hle3
    · -- `v ≥ n - 2`; with `v ≠ n - 1` and `v < n`, this forces `v = n - 2`.
      have hvtop : v = n - 2 := by omega
      subst hvtop
      -- align `B ⟨1 + (n-2)⟩ = B ⟨n-1⟩`.
      have hidx : (⟨1 + (n - 2), by have := hv; omega⟩ : Fin (n + 1))
          = (⟨n - 1, by omega⟩ : Fin (n + 1)) := Fin.ext (show 1 + (n - 2) = n - 1 by omega)
      rw [hidx]
      exact strictDiagonal_top hB hn3
    · -- strict interior: `2 ≤ v ≤ n - 3`.
      exact hint v hv hge2 hle3



/-- **The genuine core of `TailFoldBoundary`: the tail vertex's ray membership.**  At the `(0, n−1)`
boundary fold, the last vertex `A (last)` lies on the *nonnegative cone* (the short geodesic ray)
spanned by `A 0` and `A ⟨n−1⟩`.  This is exactly the FFCT22 audited master gap (the out-of-plane cone
re-extraction beyond `det3 = 0`); `far_fold_tail_collinear_step` gives only the line (`det3 = 0`), not
the ray.  Named, satisfiable, context-carrying. -/
def TailRayMembership {n : ℕ} (A : Fin (n + 1) → S2) (hn1 : n - 1 < n + 1) : Prop :=
  (A (Fin.last n) : E3) ∈ Submodule.span NNReal
    ({(A ⟨0, by omega⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)} : Set E3)

/-- **Brick 2 reduction (unconditional): `TailFoldBoundary` from `TailRayMembership`.**  The metric
collinearity is the betweenness equation `sDist_betweenness_of_collinear` applied to the ray
membership of `A (last)` on `span≥0 {A 0, A ⟨n−1⟩}`, reconciled with `endpt A = sDist (A 0)(A last)`.
Fully discharged modulo the named ray residue. -/
theorem tailFoldBoundary_of_rayMembership {n : ℕ} {A : Fin (n + 1) → S2} (hn1 : n - 1 < n + 1)
    (hray : TailRayMembership A hn1) :
    ProofsInTheBook.ZinanFFCT53.TailFoldBoundary A hn1 := by
  -- the betweenness equation: `sDist p r = sDist p q + sDist q r` with `q = A last` between
  -- `p = A 0` and `r = A ⟨n-1⟩`.
  have hbtw := sDist_betweenness_of_collinear (p := A ⟨0, by omega⟩) (q := A (Fin.last n))
    (r := A ⟨n - 1, hn1⟩) hray
  -- unfold `TailFoldBoundary`: `sDist (A 0)(A ⟨n-1⟩) = endpt A + sDist (A last)(A ⟨n-1⟩)`.
  rw [ProofsInTheBook.ZinanFFCT53.TailFoldBoundary, endpt]
  -- reconcile `A 0` (from `endpt`) with `A ⟨0,_⟩`.
  have h00 : (A 0 : S2) = A ⟨0, by omega⟩ := by congr 1
  rw [h00]
  -- `hbtw : sDist (A 0)(A ⟨n-1⟩) = sDist (A 0)(A last) + sDist (A last)(A ⟨n-1⟩)`.
  linarith [hbtw]




























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















/-- **The `a`-readout.**  Under the weak support of edge `(j-1, j)` at `Aδ i`
(`0 ≤ det3 (Aδ(j-1))(Aδ j)(Aδ i)`) and the span decomposition, `0 ≤ a · E` where
`E := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))`.

Expansion: `det3 z'' q p = det3 z'' q (a•mid + b•q) = a·det3 z'' q mid + b·det3 z'' q q
= a·det3 z'' q mid = a·E` (right-argument linearity, `det3 z'' q q = 0`). -/
theorem nearSide_a_readout {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1)
    {a b : ℝ}
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hsupp : 0 ≤ det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i, by omega⟩ : E3)) :
    0 ≤ a * det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
  have hexp : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i, by omega⟩ : E3)
      = a * det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
    rw [hp, det3_add_right, det3_smul_right, det3_smul_right]
    have h0 : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨j, hj⟩ : E3) = 0 := by
      simp only [det3]; ring
    rw [h0]; ring
  rw [hexp] at hsupp
  exact hsupp





/-- **The `j+1`-side `a`-readout.**  Under the weak support of edge `(j, j+1)` at `Aδ i`, the same
expansion gives `0 ≤ a · E'` where `E' := det3 (Aδ j) (Aδ(j+1)) (Aδ(i+1))`. -/
theorem nearSide_a_readout_succ {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1)
    {a b : ℝ}
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hsupp : 0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i, by omega⟩ : E3)) :
    0 ≤ a * det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
  have hexp : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i, by omega⟩ : E3)
      = a * det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
    rw [hp, det3_add_right, det3_smul_right, det3_smul_right]
    have h0 : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨j, hj⟩ : E3) = 0 := by
      simp only [det3]; ring
    rw [h0]; ring
  rw [hexp] at hsupp
  exact hsupp


































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



/-- From `ShortArc mid q` (`mid ≠ q`, `(mid:E3) ≠ -(q:E3)`), the swapped base pair `(q, mid)` is
independent: `q ≠ mid` (as `S2`) and `(q : E3) ≠ -(mid : E3)`. -/
theorem base_ne_of_shortArc {mid q : S2} (hsa : ShortArc mid q) :
    q ≠ mid ∧ (q : E3) ≠ -(mid : E3) := by
  refine ⟨fun h => hsa.1 h.symm, fun h => hsa.2 ?_⟩
  rw [h, neg_neg]



/-- **`E_{pred} = 0` puts `Aδ(j-1)` in the plane.**  `det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1)) = 0` gives
`Aδ(j-1) = c•(Aδ j) + d•(Aδ(i+1))` for reals `c, d`. -/
theorem witnessPred_mem_plane {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hE : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0) :
    ∃ c d : ℝ, c • (A ⟨j, hj⟩ : E3) + d • (A ⟨i + 1, hi1⟩ : E3) = (A ⟨j - 1, hjm1⟩ : E3) := by
  have hcyc : det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3) = 0 := by
    rw [show det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3)
        = det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) by
      simp only [det3]; ring]
    exact hE
  obtain ⟨hne, hanti⟩ := base_ne_of_shortArc hsa
  obtain ⟨c, d, hcd⟩ := lin_indep_span_of_det3_zero (A ⟨j, hj⟩).2 (A ⟨i + 1, hi1⟩).2
    (fun h => hne (S2.ext h)) hanti hcyc
  exact ⟨c, d, hcd.symm⟩

/-- **`E_{succ} = 0` puts `Aδ(j+1)` in the plane.**  `det3 (Aδ j) (Aδ(j+1)) (Aδ(i+1)) = 0` gives
`Aδ(j+1) = c•(Aδ j) + d•(Aδ(i+1))`. -/
theorem witnessSucc_mem_plane {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hE' : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0) :
    ∃ c d : ℝ, c • (A ⟨j, hj⟩ : E3) + d • (A ⟨i + 1, hi1⟩ : E3) = (A ⟨j + 1, hjp1⟩ : E3) := by
  have hswap : det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) = 0 := by
    rw [show det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3)
        = - det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) by
      simp only [det3]; ring]
    rw [hE']; ring
  obtain ⟨hne, hanti⟩ := base_ne_of_shortArc hsa
  obtain ⟨c, d, hcd⟩ := lin_indep_span_of_det3_zero (A ⟨j, hj⟩).2 (A ⟨i + 1, hi1⟩).2
    (fun h => hne (S2.ext h)) hanti hswap
  exact ⟨c, d, hcd.symm⟩



/-- **(The dichotomy core) Both witnesses degenerating is impossible.**  At an interior binding
(`i + 2 ≤ j`, `j + 1 < n + 1`) with the independent edge base `ShortArc (Aδ(i+1)) (Aδ j)`, the two
apex arcs at `Aδ j`, `PositiveJoints A`, and the non-flat bound, the witness determinants
`E_{pred} := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))` and `E_{succ} := det3 (Aδ j) (Aδ(j+1)) (Aδ(i+1))`
cannot both vanish: both vanishing puts `Aδ(j-1), Aδ j, Aδ(j+1)` coplanar in `Π`, flattening the
joint at `Aδ j`. -/
theorem not_both_witness_zero {n : ℕ} {A B : Fin (n + 1) → S2}
    (hposA : PositiveJoints A) (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hjm1 : j - 1 < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hsau : ShortArc (A ⟨j, hj⟩) (A ⟨j - 1, hjm1⟩))
    (hsav : ShortArc (A ⟨j, hj⟩) (A ⟨j + 1, hjp1⟩))
    (hEpred : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0)
    (hEsucc : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0) :
    False := by
  have hxpred := witnessPred_mem_plane hi1 hj hjm1 hsa hEpred
  have hzsucc := witnessSucc_mem_plane hi1 hj hjp1 hsa hEsucc
  have hymid : ∃ c d : ℝ,
      c • (A ⟨j, hj⟩ : E3) + d • (A ⟨i + 1, hi1⟩ : E3) = (A ⟨j, hj⟩ : E3) :=
    ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
  have hcol : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) = 0 :=
    coplanar_triple_det3_zero hxpred hymid hzsucc
  exact far_fold_tail_not_interior (B := B) hposA hB hangle
    (t := j) (by omega) hjp1 hjm1 hj hjp1 hsau hsav hcol

































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



/-- **(Brick C2) `b = 0` is impossible under a short edge `(p, mid)`.**  If `p = a • mid + b • q`
with `b = 0`, then `p = a • mid` with `a` a real scalar; taking norms forces `a = ±1`, hence
`p = mid` or `p = -mid`, both excluded by `ShortArc p mid` (whose two conjuncts are `p ≠ mid` and
`(p : E3) ≠ -(mid : E3)`). -/
theorem bcoef_ne_zero_of_short_edge {p mid q : S2} {a b : ℝ}
    (hpm : ShortArc p mid)
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3))
    (hb0 : b = 0) :
    False := by
  -- `p = a • mid`.
  have hpa : (p : E3) = a • (mid : E3) := by rw [hp, hb0, zero_smul, add_zero]
  -- norms: `1 = |a| · 1 = |a|`.
  have hnp : ‖(p : E3)‖ = 1 := p.2
  have hnm : ‖(mid : E3)‖ = 1 := mid.2
  have habs : |a| = 1 := by
    have := congrArg (fun x : E3 => ‖x‖) hpa
    simp only [norm_smul, Real.norm_eq_abs] at this
    rw [hnp, hnm, mul_one] at this
    linarith [this]
  -- `a = 1` (⟹ `p = mid`) or `a = -1` (⟹ `p = -mid`).
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.1 habs with ha1 | ham1
  · exact hpm.1 (S2.ext (by rw [hpa, ha1, one_smul]))
  · exact hpm.2 (by rw [hpa, ham1, neg_one_smul])

/-- **(Brick C1) Rearrange a `b < 0` fold to a positive-coefficient mid-fold.**  Given the open
hemisphere (a unit `h` strictly positive against every vertex), `P i = a • P(i+1) + b • P j` and
`b < 0`, the leading coefficient is `a > 0`, and `P(i+1) = (1/a) • P i + (-b/a) • P j` with both
coefficients strictly positive. -/
theorem midFold_coeffs_of_bneg {n : ℕ} {P : Fin (n + 1) → S2} {i j : ℕ}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hp : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hb : b < 0) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      (P ⟨i + 1, hi1⟩ : E3) = c • (P ⟨i, hi⟩ : E3) + d • (P ⟨j, hj⟩ : E3) := by
  obtain ⟨h, _hnorm, hpos⟩ := hhem
  -- inner product against `h`: `⟪h, P i⟫ = a ⟪h, P(i+1)⟫ + b ⟪h, P j⟫`.
  have hinner : (⟪h, (P ⟨i, hi⟩ : E3)⟫ : ℝ)
      = a * (⟪h, (P ⟨i + 1, hi1⟩ : E3)⟫ : ℝ) + b * (⟪h, (P ⟨j, hj⟩ : E3)⟫ : ℝ) := by
    rw [hp]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  -- all three inner products are strictly positive.
  have h0 := hpos ⟨i, hi⟩
  have h1 := hpos ⟨i + 1, hi1⟩
  have h2 := hpos ⟨j, hj⟩
  -- `a > 0`: else `a ⟪h,P(i+1)⟫ ≤ 0` and `b ⟪h,P j⟫ < 0`, so `⟪h,P i⟫ < 0`, contradiction.
  have ha : 0 < a := by nlinarith [hinner, h0, h1, h2, hb]
  -- rearrange `a • P(i+1) = P i - b • P j`, then scale by `1/a`.
  have hane : a ≠ 0 := ne_of_gt ha
  refine ⟨1 / a, (-b) / a, by positivity, div_pos (neg_pos.2 hb) ha, ?_⟩
  -- `a • P(i+1) = P i - b • P j`.
  have hav : a • (P ⟨i + 1, hi1⟩ : E3) = (P ⟨i, hi⟩ : E3) - b • (P ⟨j, hj⟩ : E3) := by
    rw [hp]; abel
  -- `P(i+1) = (1/a) • (a • P(i+1)) = (1/a) • (P i - b • P j) = (1/a)•P i + ((-b)/a)•P j`.
  have hkey : (P ⟨i + 1, hi1⟩ : E3) = (1 / a) • (a • (P ⟨i + 1, hi1⟩ : E3)) := by
    rw [smul_smul, one_div, inv_mul_cancel₀ hane, one_smul]
  rw [hkey, hav]
  match_scalars <;> field_simp



/-- **(Brick C3) The mid-fold local contradiction.**  Suppose the between-vertex
`M = P(i+1) = c • P i + d • P j` with `c, d > 0`, the two short edges `(P i, P(i+1))`,
`(P(i+1), P(i+2))`, the weak supports of the successor edge `(P(i+1), P(i+2))` at the two fold
neighbours `P i` and `P j`, `PositiveJoints P` and the non-flat bound `jointAngle P · < π`.  Then
`False`.

The audited algebra (`P0 = P i`, `M = P(i+1)`, `R = P(i+2)`, `Q = P j`, `M = c P0 + d Q`):
`det3 M R P0 = d · det3 Q R P0`, `det3 M R Q = -c · det3 Q R P0`; the two supports with `c, d > 0`
force `det3 Q R P0 = 0`, hence `det3 P0 M R = d · det3 P0 Q R = 0` — the adjacent joint triple at
apex `M = P(i+1)` (joint index `i`) vanishes, so the joint is in `{0, π}`, excluded. -/
theorem midFold_interior_contradiction {n : ℕ} {P : Fin (n + 1) → S2}
    {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hi2 : i + 2 < n + 1) (hj : j < n + 1)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hmid : (P ⟨i + 1, hi1⟩ : E3) = c • (P ⟨i, hi⟩ : E3) + d • (P ⟨j, hj⟩ : E3))
    (hsuppP0 : 0 ≤ sOrient (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) (P ⟨i, hi⟩))
    (hsuppQ : 0 ≤ sOrient (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) (P ⟨j, hj⟩))
    (hposJoint : 0 < jointAngle P ⟨i, by omega⟩)
    (hltJoint : jointAngle P ⟨i, by omega⟩ < Real.pi)
    (hsmp : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i, hi⟩))
    (hsmr : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩)) :
    False := by
  -- name the four sphere points.
  set P0 : E3 := (P ⟨i, hi⟩ : E3) with hP0
  set M : E3 := (P ⟨i + 1, hi1⟩ : E3) with hM
  set R : E3 := (P ⟨i + 2, hi2⟩ : E3) with hR
  set Q : E3 := (P ⟨j, hj⟩ : E3) with hQ
  -- the supports are `det3` (unfold `sOrient`).
  have hsuppP0' : 0 ≤ det3 M R P0 := hsuppP0
  have hsuppQ' : 0 ≤ det3 M R Q := hsuppQ
  -- the mid-fold representation: `M = c • P0 + d • Q`.
  have hMrep : M = c • P0 + d • Q := hmid
  -- `det3 M R P0 = c·det3 P0 R P0 + d·det3 Q R P0 = d·(det3 Q R P0)`.
  have hidP0 : det3 M R P0 = d * det3 Q R P0 := by
    rw [hMrep]
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `det3 M R Q = c·det3 P0 R Q + d·det3 Q R Q = -c·(det3 Q R P0)`.
  have hidQ : det3 M R Q = -c * det3 Q R P0 := by
    rw [hMrep]
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- from the two supports + positivity: `det3 Q R P0 = 0`.
  have hD0 : det3 Q R P0 = 0 := by
    have h1 : 0 ≤ d * det3 Q R P0 := hidP0 ▸ hsuppP0'
    have h2 : 0 ≤ -c * det3 Q R P0 := hidQ ▸ hsuppQ'
    nlinarith [h1, h2, hc, hd, mul_pos hc hd]
  -- the adjacent triple `det3 P0 M R = d·det3 P0 Q R = d·(det3 Q R P0) = 0`.
  have hadj0 : det3 P0 M R = 0 := by
    have hexpand : det3 P0 M R = d * det3 Q R P0 := by
      rw [hMrep]
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hexpand, hD0, mul_zero]
  -- bridge: `det3 P0 M R = 0` ⟹ `sphAngle (P i) (P(i+1)) (P(i+2)) ∈ {0, π}`.
  -- short arcs at the apex `M = P(i+1)`: `(P(i+1), P i)` and `(P(i+1), P(i+2))`.
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero (u := P ⟨i, hi⟩) (v := P ⟨i + 1, hi1⟩)
    (w := P ⟨i + 2, hi2⟩) hsmp hsmr (by rw [← hP0, ← hM, ← hR]; exact hadj0)
  -- the joint angle at index `i` is this spherical angle.
  have hjoint_eq : jointAngle P ⟨i, by omega⟩
      = sphAngle (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) := by
    rw [jointAngle]
  -- contradiction: the joint is in `(0, π)` but the bridge forces it into `{0, π}`.
  rcases hbridge with h0 | hπ
  · rw [hjoint_eq, h0] at hposJoint; exact lt_irrefl 0 hposJoint
  · rw [hjoint_eq, hπ] at hltJoint; exact lt_irrefl Real.pi hltJoint



/-- **The mid-fold kill from a `b < 0` span datum on a weakly convex `PositiveJoints` arm.**  Given a
weakly convex `P` with positive joints, a strictly convex comparison `B` with `JointLe P B`, the
interior apex `i + 2 < n + 1`, the strict open hemisphere, and the `b < 0` span datum
`P i = a • P(i+1) + b • P j`, the configuration is impossible. -/
theorem midFold_bneg_false {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B) (hangle : JointLe P B)
    {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hi2 : i + 2 < n + 1) (hj : j < n + 1)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {a b : ℝ}
    (hp : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hb : b < 0) :
    False := by
  -- rearrange to the positive mid-fold.
  obtain ⟨c, d, hc, hd, hmid⟩ := midFold_coeffs_of_bneg hhem hi hi1 hj hp hb
  have hn2 : 2 ≤ n := hP.two_le
  -- the successor edge `(P(i+1), P(i+2))` of the closed polygon.
  have hsucc : ((⟨i + 1, hi1⟩ : Fin (n + 1)) + 1) = (⟨i + 2, hi2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    show ((⟨i + 1, hi1⟩ : Fin (n + 1)) + 1).val = i + 2
    rw [Fin.val_add, Fin.val_mk, hone,
      Nat.mod_eq_of_lt (show (i + 1) + 1 < n + 1 by omega)]
  -- weak supports of the successor edge at the two fold neighbours `P i` and `P j`.
  have hsuppP0 : 0 ≤ sOrient (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) (P ⟨i, hi⟩) := by
    have h := hP.closed_convex.edge_support ⟨i + 1, hi1⟩ ⟨i, hi⟩
    rwa [hsucc] at h
  have hsuppQ : 0 ≤ sOrient (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) (P ⟨j, hj⟩) := by
    have h := hP.closed_convex.edge_support ⟨i + 1, hi1⟩ ⟨j, hj⟩
    rwa [hsucc] at h
  -- the short edge `(P i, P(i+1))`.
  have hedge1 : ShortArc (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) := by
    have h := hP.closed_convex.edge_short ⟨i, hi⟩
    have hsucc1 : ((⟨i, hi⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc1] at h
  have hsmp : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i, hi⟩) := hedge1.symm
  -- the short edge `(P(i+1), P(i+2))`.
  have hsmr : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) := by
    have h := hP.closed_convex.edge_short ⟨i + 1, hi1⟩
    rwa [hsucc] at h
  -- positivity and non-flat bound at joint index `i`.
  have hposJoint : 0 < jointAngle P ⟨i, by omega⟩ := hpos ⟨i, by omega⟩
  have hltJoint : jointAngle P ⟨i, by omega⟩ < Real.pi :=
    jointAngle_lt_pi hB hangle ⟨i, by omega⟩
  exact midFold_interior_contradiction hi hi1 hi2 hj hc hd hmid hsuppP0 hsuppQ
    hposJoint hltJoint hsmp hsmr

























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



/-- Reflection in the `z = 0` coordinate plane: `(x,y,z) ↦ (x,y,-z)`. -/
def reflectZ (v : E3) : E3 := !₂[v 0, v 1, -v 2]

@[simp] theorem reflectZ_apply_zero (v : E3) : reflectZ v 0 = v 0 := rfl
@[simp] theorem reflectZ_apply_one (v : E3) : reflectZ v 1 = v 1 := rfl
@[simp] theorem reflectZ_apply_two (v : E3) : reflectZ v 2 = -v 2 := rfl

theorem reflectZ_involutive (v : E3) : reflectZ (reflectZ v) = v := by
  apply ext_coord <;> simp [reflectZ]

theorem reflectZ_injective : Function.Injective reflectZ := by
  intro x y h
  have h' := congrArg reflectZ h
  simpa [reflectZ_involutive] using h'

theorem reflectZ_neg (v : E3) : reflectZ (-v) = -reflectZ v := by
  apply ext_coord <;> simp [reflectZ]



theorem reflectZ_sub (u v : E3) : reflectZ (u - v) = reflectZ u - reflectZ v := by
  apply ext_coord
  · simp [reflectZ]
  · simp [reflectZ]
  · simp [reflectZ]; ring_nf

theorem reflectZ_smul (a : ℝ) (v : E3) : reflectZ (a • v) = a • reflectZ v := by
  apply ext_coord <;> simp [reflectZ]

theorem inner_reflectZ_reflectZ (u v : E3) :
    (⟪reflectZ u, reflectZ v⟫ : ℝ) = ⟪u, v⟫ := by
  rw [inner_eq_coord, inner_eq_coord]
  simp [reflectZ]

theorem norm_reflectZ (v : E3) : ‖reflectZ v‖ = ‖v‖ := by
  have hsq : ‖reflectZ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_reflectZ_reflectZ]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hn1 : (0 : ℝ) ≤ ‖reflectZ v‖ := norm_nonneg _
    have hn2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
    linarith

theorem det3_reflectZ (x y z : E3) :
    det3 (reflectZ x) (reflectZ y) (reflectZ z) = -det3 x y z := by
  simp only [det3, reflectZ_apply_zero, reflectZ_apply_one, reflectZ_apply_two]
  ring

/-- The induced reflection of `S²`. -/
def mirrorS2 (p : S2) : S2 :=
  ⟨reflectZ (p : E3), by rw [norm_reflectZ, p.2]⟩

@[simp] theorem mirrorS2_coe (p : S2) : (mirrorS2 p : E3) = reflectZ (p : E3) := rfl

theorem mirrorS2_injective : Function.Injective mirrorS2 := by
  intro p q h
  apply S2.ext
  apply reflectZ_injective
  exact congrArg (fun r : S2 => (r : E3)) h



theorem sInner_mirrorS2 (p q : S2) :
    sInner (mirrorS2 p) (mirrorS2 q) = sInner p q := by
  simp [sInner, inner_reflectZ_reflectZ]

theorem sDist_mirrorS2 (p q : S2) :
    sDist (mirrorS2 p) (mirrorS2 q) = sDist p q := by
  simp [sDist, sInner_mirrorS2]

theorem shortArc_mirrorS2 {p q : S2} (h : ShortArc p q) :
    ShortArc (mirrorS2 p) (mirrorS2 q) := by
  refine ⟨?_, ?_⟩
  · intro heq
    exact h.1 (mirrorS2_injective heq)
  · intro hanti
    apply h.2
    apply reflectZ_injective
    rw [reflectZ_neg]
    exact hanti

theorem angle_reflectZ (u v : E3) :
    InnerProductGeometry.angle (reflectZ u) (reflectZ v) =
      InnerProductGeometry.angle u v := by
  simp [InnerProductGeometry.angle, inner_reflectZ_reflectZ, norm_reflectZ]

theorem tangentTo_mirrorS2 (p q : S2) :
    tangentTo (mirrorS2 p) (mirrorS2 q) = reflectZ (tangentTo p q) := by
  rw [tangentTo_eq, tangentTo_eq]
  show (mirrorS2 q : E3) - sInner (mirrorS2 q) (mirrorS2 p) • (mirrorS2 p : E3)
    = reflectZ ((q : E3) - sInner q p • (p : E3))
  rw [mirrorS2_coe, mirrorS2_coe, sInner_mirrorS2, reflectZ_sub, reflectZ_smul]

theorem sphAngle_mirrorS2 (u v w : S2) :
    sphAngle (mirrorS2 u) (mirrorS2 v) (mirrorS2 w) = sphAngle u v w := by
  rw [sphAngle, sphAngle, tangentTo_mirrorS2, tangentTo_mirrorS2, angle_reflectZ]

theorem sOrient_mirrorS2 (a b c : S2) :
    sOrient (mirrorS2 a) (mirrorS2 b) (mirrorS2 c) = -sOrient a b c := by
  simp [sOrient, det3_reflectZ]



/-- The corrected tail arm: reverse the index order and then reflect in one coordinate. -/
def mirrorArm {n : ℕ} (P : Fin (n + 1) → S2) : Fin (n + 1) → S2 :=
  fun m => mirrorS2 (revArm P m)

@[simp] theorem mirrorArm_apply {n : ℕ} (P : Fin (n + 1) → S2) (m : Fin (n + 1)) :
    mirrorArm P m = mirrorS2 (revArm P m) := rfl

theorem sideLen_mirrorArm {n : ℕ} (P : Fin (n + 1) → S2) (i : Fin n) :
    sideLen (mirrorArm P) i = sideLen P ⟨n - 1 - i.val, by have := i.isLt; omega⟩ := by
  rw [show sideLen (mirrorArm P) i = sideLen (revArm P) i by
    unfold sideLen mirrorArm
    rw [sDist_mirrorS2]]
  exact revArm_sideLen P i

theorem jointAngle_mirrorArm {n : ℕ} (P : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    jointAngle (mirrorArm P) i = jointAngle P ⟨n - 2 - i.val, by have := i.isLt; omega⟩ := by
  rw [show jointAngle (mirrorArm P) i = jointAngle (revArm P) i by
    unfold jointAngle mirrorArm
    rw [sphAngle_mirrorS2]]
  exact revArm_jointAngle P i

theorem endpt_mirrorArm {n : ℕ} (P : Fin (n + 1) → S2) :
    endpt (mirrorArm P) = endpt P := by
  rw [show endpt (mirrorArm P) = endpt (revArm P) by
    unfold endpt mirrorArm
    rw [sDist_mirrorS2]]
  exact endpt_revArm P

theorem sameSides_mirrorArm {n : ℕ} {A B : Fin (n + 1) → S2} (h : SameSides A B) :
    SameSides (mirrorArm A) (mirrorArm B) := by
  intro i
  rw [sideLen_mirrorArm, sideLen_mirrorArm]
  exact h _

theorem jointLe_mirrorArm {n : ℕ} {A B : Fin (n + 1) → S2} (h : JointLe A B) :
    JointLe (mirrorArm A) (mirrorArm B) := by
  intro i
  rw [jointAngle_mirrorArm, jointAngle_mirrorArm]
  exact h _

theorem positiveJoints_mirrorArm {n : ℕ} {A : Fin (n + 1) → S2} (h : PositiveJoints A) :
    PositiveJoints (mirrorArm A) := by
  intro i
  rw [jointAngle_mirrorArm]
  exact h _

theorem noNonadjacentRepeat_mirrorArm {n : ℕ} {A : Fin (n + 1) → S2}
    (h : NoNonadjacentRepeat A) : NoNonadjacentRepeat (mirrorArm A) := by
  intro r s hr hs hrs he
  have hrev : revArm A ⟨r, hr⟩ = revArm A ⟨s, hs⟩ := mirrorS2_injective he
  exact revArm_noNonadjacentRepeat h r s hr hs hrs hrev

theorem neg_sOrient_eq_swap12 (a b c : S2) :
    -sOrient a b c = sOrient b a c := by
  rw [sOrient, sOrient, det3_swap12 (b : E3) (a : E3) (c : E3)]

theorem mirrorArm_edge_short {n : ℕ} {P : Fin (n + 1) → S2}
    (hshort : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1))) :
    ∀ i : Fin (n + 1), ShortArc (mirrorArm P i) (mirrorArm P (i + 1)) := by
  intro i
  by_cases hi : i.val < n
  · have hsucc_i : (i + 1 : Fin (n + 1)) = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def]
      omega
    have hsucc_e : (⟨n - i.val - 1, by omega⟩ + 1 : Fin (n + 1))
        = ⟨n - i.val, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt (show n - i.val - 1 + 1 < n + 1 by omega)]
      omega
    have hbase := hshort ⟨n - i.val - 1, by omega⟩
    rw [hsucc_e] at hbase
    have ri : revArm P i = P ⟨n - i.val, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have ris : revArm P (i + 1) = P ⟨n - i.val - 1, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (⟨i.val + 1, by omega⟩ : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
    rw [mirrorArm_apply, mirrorArm_apply, ri, ris]
    exact shortArc_mirrorS2 hbase.symm
  · have hin : i.val = n := by omega
    have hsucc_i : (i + 1 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.add_def, hin, Nat.mod_self]
    have hwrap : (⟨n, by omega⟩ + 1 : Fin (n + 1)) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_self]
    have hbase := hshort ⟨n, by omega⟩
    rw [hwrap] at hbase
    have ri : revArm P i = P ⟨0, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val, hin]))
    have ris : revArm P (i + 1) = P ⟨n, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (0 : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    rw [mirrorArm_apply, mirrorArm_apply, ri, ris]
    exact shortArc_mirrorS2 hbase.symm

theorem mirrorArm_edge_support {n : ℕ} {P : Fin (n + 1) → S2}
    (hsupp : ∀ i j : Fin (n + 1), 0 ≤ sOrient (P i) (P (i + 1)) (P j)) :
    ∀ i j : Fin (n + 1),
      0 ≤ sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j) := by
  intro i j
  by_cases hi : i.val < n
  · have hsucc_i : (i + 1 : Fin (n + 1)) = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def]
      omega
    have hsucc_e : (⟨n - i.val - 1, by omega⟩ + 1 : Fin (n + 1))
        = ⟨n - i.val, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt (show n - i.val - 1 + 1 < n + 1 by omega)]
      omega
    have hbase := hsupp ⟨n - i.val - 1, by omega⟩ ⟨n - j.val, by omega⟩
    rw [hsucc_e] at hbase
    have ri : revArm P i = P ⟨n - i.val, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have ris : revArm P (i + 1) = P ⟨n - i.val - 1, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (⟨i.val + 1, by omega⟩ : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
    have rj : revArm P j = P ⟨n - j.val, by omega⟩ := by
      change P (revFin j) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have heq : sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j)
        = sOrient (P ⟨n - i.val - 1, by omega⟩) (P ⟨n - i.val, by omega⟩)
            (P ⟨n - j.val, by omega⟩) := by
      rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, ri, ris, rj,
        sOrient_mirrorS2, neg_sOrient_eq_swap12]
    rw [heq]
    exact hbase
  · have hin : i.val = n := by omega
    have hsucc_i : (i + 1 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.add_def, hin, Nat.mod_self]
    have hwrap : (⟨n, by omega⟩ + 1 : Fin (n + 1)) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_self]
    have hbase := hsupp ⟨n, by omega⟩ ⟨n - j.val, by omega⟩
    rw [hwrap] at hbase
    have ri : revArm P i = P ⟨0, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val, hin]))
    have ris : revArm P (i + 1) = P ⟨n, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (0 : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have rj : revArm P j = P ⟨n - j.val, by omega⟩ := by
      change P (revFin j) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have heq : sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j)
        = sOrient (P ⟨n, by omega⟩) (P ⟨0, by omega⟩)
            (P ⟨n - j.val, by omega⟩) := by
      rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, ri, ris, rj,
        sOrient_mirrorS2, neg_sOrient_eq_swap12]
    rw [heq]
    exact hbase

theorem weakConvex_mirrorArm {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) : WeakConvexSphArm (mirrorArm P) := by
  refine ⟨hP.two_le, ?_⟩
  refine
    { three_le := hP.closed_convex.three_le
      edge_short := mirrorArm_edge_short hP.closed_convex.edge_short
      edge_support := mirrorArm_edge_support hP.closed_convex.edge_support
      open_hemisphere := ?_ }
  obtain ⟨h, hnorm, hhem⟩ := hP.closed_convex.open_hemisphere
  refine ⟨reflectZ h, by rw [norm_reflectZ, hnorm], ?_⟩
  intro r
  rw [mirrorArm_apply, mirrorS2_coe, inner_reflectZ_reflectZ]
  exact hhem (revFin r)

theorem strictConvex_mirrorArm {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : StrictConvexSphArm P) : StrictConvexSphArm (mirrorArm P) := by
  have hweak : WeakConvexSphArm (mirrorArm P) :=
    weakConvex_mirrorArm (strictConvexSphArm_toWeak hP)
  refine ⟨hP.two_le, ?_⟩
  refine
    { three_le := hweak.closed_convex.three_le
      edge_short := hweak.closed_convex.edge_short
      edge_support := hweak.closed_convex.edge_support
      strict_nonincident := ?_
      open_hemisphere := hweak.closed_convex.open_hemisphere }
  intro i j hji hji1
  by_cases hi : i.val < n
  · have hsucc_i : (i + 1 : Fin (n + 1)) = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def]
      omega
    have hsucc_e : (⟨n - i.val - 1, by omega⟩ + 1 : Fin (n + 1))
        = ⟨n - i.val, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt (show n - i.val - 1 + 1 < n + 1 by omega)]
      omega
    have hv_ne_e : (⟨n - j.val, by omega⟩ : Fin (n + 1))
        ≠ ⟨n - i.val - 1, by omega⟩ := by
      intro hv
      apply hji1
      apply Fin.ext
      have hsval : ((i + 1 : Fin (n + 1)) : ℕ) = i.val + 1 := by
        rw [hsucc_i]
      rw [hsval]
      have hvval : n - j.val = n - i.val - 1 := congrArg Fin.val hv
      have hjlt := j.isLt
      have hilt := i.isLt
      omega
    have hv_ne_succ : (⟨n - j.val, by omega⟩ : Fin (n + 1))
        ≠ (⟨n - i.val - 1, by omega⟩ : Fin (n + 1)) + 1 := by
      rw [hsucc_e]
      intro hv
      apply hji
      apply Fin.ext
      have hvval : n - j.val = n - i.val := congrArg Fin.val hv
      omega
    have hbase := hP.closed_convex.strict_nonincident
      ⟨n - i.val - 1, by omega⟩ ⟨n - j.val, by omega⟩ hv_ne_e hv_ne_succ
    rw [hsucc_e] at hbase
    have ri : revArm P i = P ⟨n - i.val, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have ris : revArm P (i + 1) = P ⟨n - i.val - 1, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (⟨i.val + 1, by omega⟩ : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
    have rj : revArm P j = P ⟨n - j.val, by omega⟩ := by
      change P (revFin j) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have heq : sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j)
        = sOrient (P ⟨n - i.val - 1, by omega⟩) (P ⟨n - i.val, by omega⟩)
            (P ⟨n - j.val, by omega⟩) := by
      rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, ri, ris, rj,
        sOrient_mirrorS2, neg_sOrient_eq_swap12]
    rw [heq]
    exact hbase
  · have hin : i.val = n := by omega
    have hsucc_i : (i + 1 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.add_def, hin, Nat.mod_self]
    have hwrap : (⟨n, by omega⟩ + 1 : Fin (n + 1)) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_self]
    have hv_ne_e : (⟨n - j.val, by omega⟩ : Fin (n + 1))
        ≠ ⟨n, by omega⟩ := by
      intro hv
      apply hji1
      apply Fin.ext
      have hsval : ((i + 1 : Fin (n + 1)) : ℕ) = 0 := by
        rw [hsucc_i]
        simp
      rw [hsval]
      have hvval : n - j.val = n := congrArg Fin.val hv
      have hjlt := j.isLt
      omega
    have hv_ne_succ : (⟨n - j.val, by omega⟩ : Fin (n + 1))
        ≠ (⟨n, by omega⟩ : Fin (n + 1)) + 1 := by
      rw [hwrap]
      intro hv
      apply hji
      apply Fin.ext
      have hvval : n - j.val = 0 := congrArg Fin.val hv
      omega
    have hbase := hP.closed_convex.strict_nonincident
      ⟨n, by omega⟩ ⟨n - j.val, by omega⟩ hv_ne_e hv_ne_succ
    rw [hwrap] at hbase
    have ri : revArm P i = P ⟨0, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val, hin]))
    have ris : revArm P (i + 1) = P ⟨n, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (0 : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have rj : revArm P j = P ⟨n - j.val, by omega⟩ := by
      change P (revFin j) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have heq : sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j)
        = sOrient (P ⟨n, by omega⟩) (P ⟨0, by omega⟩)
            (P ⟨n - j.val, by omega⟩) := by
      rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, ri, ris, rj,
        sOrient_mirrorS2, neg_sOrient_eq_swap12]
    rw [heq]
    exact hbase




















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



/-- If the far coefficient is zero, a span relation across a short edge is impossible. -/
theorem span_bzero_false_of_weak {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hb0 : b = 0) :
    False := by
  have hedge : ShortArc (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) := by
    have h := hP.closed_convex.edge_short ⟨i, hi⟩
    have hsucc : ((⟨i, hi⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc] at h
  exact bcoef_ne_zero_of_short_edge hedge hspan hb0

/-- If `b > 0` and `a = 0`, the span relation forces a forbidden nonadjacent repeat. -/
theorem span_azero_bpos_false_of_noRepeat {n : ℕ} {P : Fin (n + 1) → S2}
    (hnr : NoNonadjacentRepeat P) {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hij : i + 2 ≤ j) {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (ha0 : a = 0) :
    False := by
  have hpj : (P ⟨i, hi⟩ : E3) = b • (P ⟨j, hj⟩ : E3) := by
    rw [hspan, ha0, zero_smul, zero_add]
  have hbabs : |b| = 1 := by
    have hnorm := congrArg (fun x : E3 => ‖x‖) hpj
    simp only [norm_smul, Real.norm_eq_abs] at hnorm
    rw [(P ⟨i, hi⟩).2, (P ⟨j, hj⟩).2, mul_one] at hnorm
    linarith
  have hb1 : b = 1 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 hbabs with hb | hb
    · exact hb
    · linarith
  have hpeq : P ⟨i, hi⟩ = P ⟨j, hj⟩ := by
    apply S2.ext
    rw [hpj, hb1, one_smul]
  exact (hnr i j hi hj hij) hpeq































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



/-- The remaining B-side strict-diagonal content after FFCT63: only the strict interior range
`2 ≤ v ≤ n-3`, and only in the nonempty regime `n ≥ 5`. -/
def StrictDiagonalInteriorCore : Prop :=
  ∀ {n : ℕ} (hn3 : 3 ≤ n) (_hn5 : 5 ≤ n) (B : Fin (n + 1) → S2),
    StrictConvexSphArm B → StrictDiagonalInteriorSupport B hn3

/-- For `n = 3, 4`, FFCT63's interior range is empty; for `n ≥ 5`, use the named core. -/
theorem strictDiagonalSupport_of_interiorCore
    (hcore : StrictDiagonalInteriorCore) {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    StrictDiagonalSupport B hn3 := by
  apply strictDiagonalSupport_of_interior hB hn3
  by_cases hn5 : 5 ≤ n
  · exact hcore hn3 hn5 B hB
  · intro v hv hv2 hvn
    omega

/-- The `(0,n)` interval certificates with FFCT63's smaller B-side core threaded in.  The B ear is
free for `n ∈ {3,4}` and uses `StrictDiagonalInteriorCore` only for `n ≥ 5`. -/
theorem intervalCerts_of_betweenness_and_interiorCore
    (hcore : StrictDiagonalInteriorCore) {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n)
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3)) :
    WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)) ∧
      StrictConvexSphArm (intervalArm B 1 (n - 1) (by omega)) :=
  intervalCerts_of_betweenness_and_strictDiagonal hA hnr hB hn3 hcol
    (strictDiagonalSupport_of_interiorCore hcore hB hn3)

























/-- In FFCT64's normalized surface, the retained `b < 0` tail branch is arithmetically empty:
`i+1<j` and `j<n+1` imply `i+2<n+1`. -/
theorem bneg_tail_closed_by_normalization {n : ℕ} {P B : Fin (n + 1) → S2}
    (_hP : WeakConvexSphArm P) (_hpos : PositiveJoints P) (_hB : StrictConvexSphArm B)
    (_hside : SameSides P B) (_hangle : JointLe P B) (_hnr : NoNonadjacentRepeat P)
    (_hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {i j : ℕ} (hij : i + 1 < j)
    (_hi : i < n + 1) (_hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (_hspan : (P ⟨i, by omega⟩ : E3) = a • (P ⟨i + 1, by omega⟩ : E3)
      + b • (P ⟨j, hj⟩ : E3))
    (_hbneg : b < 0) (hnot : ¬ i + 2 < n + 1) :
    endpt P ≤ endpt B := by
  exfalso
  apply hnot
  omega

































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



/-- Cyclic rotation for `sOrient`. -/
theorem sOrient_cyclic (a b c : S2) :
    sOrient a b c = sOrient b c a := by
  rw [sOrient]
  exact ProofsInTheBook.PlanarConvexDiag.det3_cyclic (a : E3) (b : E3) (c : E3)

/-- The wrap diagonal `(B n, B 1)` strictly supports every arc-interior vertex `B (1+v)`. -/
theorem strictDiagonal_arcInterior_of_cyclicTriple
    {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B)
    {v : ℕ} (hv1 : 1 ≤ v) (hvn : v ≤ n - 2) :
    0 < sOrient
      (B ⟨n, by omega⟩)
      (B ⟨1, by omega⟩)
      (B ⟨1 + v, by omega⟩) := by
  have hcyc :
      ProofsInTheBook.SphericalCyclicTriple.CyclicTriplePos (n := n + 1) B :=
    ProofsInTheBook.PlanarConvexDiag.cyclicTriplePos_unconditional hB.closed_convex
  have hpos :
      0 < sOrient
        (B ⟨1, by omega⟩)
        (B ⟨1 + v, by omega⟩)
        (B ⟨n, by omega⟩) := by
    exact hcyc
      ⟨1, by omega⟩
      ⟨1 + v, by omega⟩
      ⟨n, by omega⟩
      (by exact_mod_cast (show (1 : ℕ) < 1 + v by omega))
      (by exact_mod_cast (show (1 + v : ℕ) < n by omega))
  rw [sOrient_cyclic (B ⟨n, by omega⟩) (B ⟨1, by omega⟩)
        (B ⟨1 + v, by omega⟩)]
  exact hpos

/-- FFCT63's strict-diagonal interior residue is fully discharged. -/
theorem StrictDiagonalInteriorSupport_holds
    {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    StrictDiagonalInteriorSupport B hn3 := by
  intro v hv hv2 hvn
  exact strictDiagonal_arcInterior_of_cyclicTriple (B := B) hB (by omega) (by omega)



/-- FFCT65's `StrictDiagonalInteriorCore` field, now supplied unconditionally. -/
theorem StrictDiagonalInteriorCore_holds :
    StrictDiagonalInteriorCore := by
  intro n hn3 _hn5 B hB
  exact StrictDiagonalInteriorSupport_holds hB hn3



/-- Convert the real coefficient signs from the tail-line computation into the desired NNReal cone. -/
theorem tail_rayMembership_of_coeff_signs
    {u v p q : E3} {a b α β : ℝ}
    (ha : 0 < a)
    (hfold : p = a • u + b • v)
    (hq : q = α • u + β • v)
    (hα : 0 ≤ α)
    (hμ : 0 ≤ β * a - α * b) :
    q ∈ Submodule.span NNReal ({p, v} : Set E3) := by
  have hane : a ≠ 0 := ne_of_gt ha
  rw [Submodule.mem_span_pair]
  refine ⟨⟨α / a, div_nonneg hα (le_of_lt ha)⟩,
    ⟨(β * a - α * b) / a, div_nonneg hμ (le_of_lt ha)⟩, ?_⟩
  have hcalc :
      (α / a) • p + ((β * a - α * b) / a) • v = α • u + β • v := by
    rw [hfold, smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]
    have hca : (α / a) * a = α := by field_simp [hane]
    have hcb : (α / a) * b + (β * a - α * b) / a = β := by
      field_simp [hane]
      ring
    rw [hca, hcb]
  change (α / a : ℝ) • p + ((β * a - α * b) / a : ℝ) • v = q
  rw [hcalc, ← hq]

/-- The actual `(0,n-1)` tail fold supplies the last vertex on the ray `span≥0 {A0,A(n-1)}` when
the comparison-arm non-flat bound is in scope. -/
theorem TailRayMembership_holds_context
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn3 : 3 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    (hnr : NoNonadjacentRepeat A)
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨1, by omega⟩ : E3), (A ⟨n - 1, by omega⟩ : E3)} : Set E3)) :
    TailRayMembership A (by omega) := by
  by_cases hn4 : 4 ≤ n
  · have h0 : 0 < n + 1 := by omega
    have h1 : 1 < n + 1 := by omega
    have h2 : 2 < n + 1 := by omega
    have hj : n - 1 < n + 1 := by omega
    have hnn : n < n + 1 := by omega
    have hcol' : (A ⟨0, by omega⟩ : E3) ∈
        Submodule.span NNReal
          ({(A ⟨0 + 1, by omega⟩ : E3), (A ⟨n - 1, hj⟩ : E3)} : Set E3) := by
      have hidx1 : (⟨0 + 1, by omega⟩ : Fin (n + 1)) =
          (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
      have hidxj : (⟨n - 1, hj⟩ : Fin (n + 1)) =
          (⟨n - 1, by omega⟩ : Fin (n + 1)) := rfl
      rwa [hidx1, hidxj]
    obtain ⟨a, b, ha, hb, hcoeff⟩ :=
      far_fold_nondeg_datum_of_no_repeat hA hnr (i := 0) (j := n - 1)
        (by omega) hj hcol'
    have hfold : (A ⟨0, h0⟩ : E3) =
        (a : ℝ) • (A ⟨1, h1⟩ : E3) + (b : ℝ) • (A ⟨n - 1, hj⟩ : E3) := by
      have hidx1 : (⟨0 + 1, by omega⟩ : Fin (n + 1)) =
          (⟨1, h1⟩ : Fin (n + 1)) := Fin.ext rfl
      have hidx0 : (⟨0, by omega⟩ : Fin (n + 1)) =
          (⟨0, h0⟩ : Fin (n + 1)) := rfl
      rw [hidx1, hidx0] at hcoeff
      exact hcoeff.symm
    -- The `A2` witness gives the oriented area `D = det3 A(n-1) A1 A2` strictly positive.
    have hDneg :
        det3 (A ⟨1, h1⟩ : E3) (A ⟨n - 1, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0 :=
      fold_A2_witness_negative hA hpos hB hangle hj (by omega) h1 h2 h0 hb hfold
    have hDpos :
        0 < det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) := by
      rw [ProofsInTheBook.ZinanFFCT12.det3_swap12
        (A ⟨n - 1, hj⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3)]
      linarith
    -- First put `A n` on the real line spanned by `A1` and `A(n-1)`.
    have hsucc01 : ((⟨0, h0⟩ : Fin (n + 1)) + 1) = (⟨1, h1⟩ : Fin (n + 1)) :=
      succ_mk (by omega) (by omega)
    have htn : n - 1 + 1 < n + 1 := by omega
    have hidxn : (⟨n - 1 + 1, htn⟩ : Fin (n + 1)) =
        (⟨n, hnn⟩ : Fin (n + 1)) := Fin.ext (show n - 1 + 1 = n by omega)
    have hsuccj : ((⟨n - 1, hj⟩ : Fin (n + 1)) + 1) = (⟨n, hnn⟩ : Fin (n + 1)) := by
      have h := succ_mk (n := n) (k := n - 1) hj htn
      exact h.trans hidxn
    have hsupp1 : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨n, hnn⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨0, h0⟩ ⟨n, hnn⟩
      rwa [hsucc01] at h
    have hsupp2 : 0 ≤ det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨n, hnn⟩ : E3)
        (A ⟨1, h1⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨n - 1, hj⟩ ⟨1, h1⟩
      rwa [hsuccj] at h
    have hseed : (A ⟨n - 1, hj⟩ : E3) =
        (0 : ℝ) • (A ⟨1, h1⟩ : E3) + (1 : ℝ) • (A ⟨n - 1, hj⟩ : E3) := by
      rw [zero_smul, one_smul, zero_add]
    have hline0 : det3 (A ⟨1, h1⟩ : E3) (A ⟨n - 1, hj⟩ : E3)
        (A ⟨n - 1 + 1, htn⟩ : E3) = 0 :=
      have hsupp1t : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3)
          (A ⟨n - 1 + 1, htn⟩ : E3) := by
        rw [hidxn]
        exact hsupp1
      have hsupp2t : 0 ≤ det3 (A ⟨n - 1, hj⟩ : E3)
          (A ⟨n - 1 + 1, htn⟩ : E3) (A ⟨1, h1⟩ : E3) := by
        rw [hidxn]
        exact hsupp2
      tail_step_collinear (j := n - 1) (t := n - 1) hj h1 h0 hj htn hb
        (by norm_num : (0 : ℝ) < 1) hfold hseed hsupp1t hsupp2t
    have hline : det3 (A ⟨1, h1⟩ : E3) (A ⟨n - 1, hj⟩ : E3)
        (A ⟨n, hnn⟩ : E3) = 0 := by
      rwa [hidxn] at hline0
    obtain ⟨α, β, hq⟩ :=
      repr_of_collinear hA hnr h1 hj hnn (by omega) hline
    -- Edge `(n-1,n)` at `2` gives `0 ≤ α`.
    have hsuppVq : 0 ≤ det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨n, hnn⟩ : E3)
        (A ⟨2, h2⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨n - 1, hj⟩ ⟨2, h2⟩
      rwa [hsuccj] at h
    have hαexp : det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨n, hnn⟩ : E3)
        (A ⟨2, h2⟩ : E3)
        = α * det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨1, h1⟩ : E3)
            (A ⟨2, h2⟩ : E3) := by
      rw [hq]
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hα : 0 ≤ α := by
      rw [hαexp] at hsuppVq
      nlinarith [hsuppVq, hDpos]
    -- Wrap edge `(n,0)` at `2` gives `0 ≤ β*a - α*b`.
    have hsuccn : ((⟨n, hnn⟩ : Fin (n + 1)) + 1) = (⟨0, h0⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have : ((⟨n, hnn⟩ + 1 : Fin (n + 1)) : ℕ) = (n + 1) % (n + 1) := by
        rw [Fin.add_def]; simp
      rw [this, Nat.mod_self]
    have hsuppqp : 0 ≤ det3 (A ⟨n, hnn⟩ : E3) (A ⟨0, h0⟩ : E3)
        (A ⟨2, h2⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨n, hnn⟩ ⟨2, h2⟩
      rwa [hsuccn] at h
    have hμexp : det3 (A ⟨n, hnn⟩ : E3) (A ⟨0, h0⟩ : E3)
        (A ⟨2, h2⟩ : E3)
        = (β * (a : ℝ) - α * (b : ℝ))
            * det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨1, h1⟩ : E3)
              (A ⟨2, h2⟩ : E3) := by
      rw [hq, hfold]
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hμ : 0 ≤ β * (a : ℝ) - α * (b : ℝ) := by
      rw [hμexp] at hsuppqp
      nlinarith [hsuppqp, hDpos]
    -- Convert the signs to the desired ray membership.
    unfold TailRayMembership
    have hidxLast : (Fin.last n : Fin (n + 1)) = ⟨n, hnn⟩ := rfl
    have hidx0 : (⟨0, by omega⟩ : Fin (n + 1)) = ⟨0, h0⟩ := rfl
    have hidxj : (⟨n - 1, by omega⟩ : Fin (n + 1)) = ⟨n - 1, hj⟩ := rfl
    rw [hidxLast, hidx0, hidxj]
    exact tail_rayMembership_of_coeff_signs (a := (a : ℝ)) (b := (b : ℝ))
      (α := α) (β := β) ha hfold hq hα hμ
  · have hn_eq : n = 3 := by omega
    subst hn_eq
    exfalso
    have hcolAdj : (A ⟨0, by omega⟩ : E3) ∈
        Submodule.span NNReal
          ({(A ⟨0 + 1, by omega⟩ : E3), (A ⟨0 + 2, by omega⟩ : E3)} : Set E3) := by
      simpa using hcol
    exact foldedFlat_adjacent_contradiction (i := 0) hA hpos (by omega) hcolAdj

/-- Metric tail boundary from the contextual ray-membership proof. -/
theorem TailFoldBoundary_holds_context
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn3 : 3 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    (hnr : NoNonadjacentRepeat A)
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨1, by omega⟩ : E3), (A ⟨n - 1, by omega⟩ : E3)} : Set E3)) :
    TailFoldBoundary A (by omega) :=
  tailFoldBoundary_of_rayMembership (by omega)
    (TailRayMembership_holds_context hn3 hA hpos hB hangle hnr hcol)
























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



/-- A strict arm has no repeated vertices at nonadjacent positions. -/
theorem strictConvex_noNonadjacentRepeat {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) : NoNonadjacentRepeat A := by
  intro r s hr hs hrs heq
  have hr1 : r + 1 < n + 1 := by omega
  have hsucc : ((⟨r, hr⟩ : Fin (n + 1)) + 1) = (⟨r + 1, hr1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show r + 1 < n + 1 by omega)]
  have hnon :
      0 < sOrient (A ⟨r, hr⟩) (A ⟨r + 1, hr1⟩) (A ⟨s, hs⟩) := by
    have hbase := hA.closed_convex.strict_nonincident
      (⟨r, hr⟩ : Fin (n + 1)) (⟨s, hs⟩ : Fin (n + 1))
      (by
        intro h
        have hv : s = r := by simpa using congrArg Fin.val h
        omega)
      (by
        rw [hsucc]
        intro h
        have hv : s = r + 1 := by simpa using congrArg Fin.val h
        omega)
    rwa [hsucc] at hbase
  have hzero : sOrient (A ⟨r, hr⟩) (A ⟨r + 1, hr1⟩) (A ⟨s, hs⟩) = 0 := by
    rw [← heq, sOrient]
    exact ProofsInTheBook.SphericalDiagCut.det3_self_right _ _
  linarith

/-- The induced rotation on `S²` is injective. -/
theorem rotS2_injective (k : S2) (θ : ℝ) : Function.Injective (rotS2 k θ) := by
  intro p q hpq
  apply S2.ext
  apply rot_injective k.2 θ
  exact congrArg (fun x : S2 => (x : E3)) hpq



































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









/-- Reflection converts a reversed-arm zero support into a mirror-arm zero support. -/
theorem mirrorArm_sOrient_zero_of_revArm_zero {n : ℕ} (P : Fin (n + 1) → S2)
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hzero :
      sOrient (revArm P ⟨i, hi⟩) (revArm P ⟨i + 1, hi1⟩)
        (revArm P ⟨j, hj⟩) = 0) :
    sOrient (mirrorArm P ⟨i, hi⟩) (mirrorArm P ⟨i + 1, hi1⟩)
      (mirrorArm P ⟨j, hj⟩) = 0 := by
  rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, sOrient_mirrorS2, hzero, neg_zero]


























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









/-- In the normalized `b > 0, a < 0` branch, a real successor edge at the far
vertex forces both adjacent witness determinants at `j` to vanish.  The
FFCT32 two-witness flat-joint core then contradicts positive, non-flat joints. -/
theorem bpos_aneg_false_of_successor {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hj1 : j + 1 < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
        a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (_hb : 0 < b) (ha : a < 0) :
    False := by
  have hij2 : i + 2 ≤ j := by omega
  have hjle : j ≤ n := by omega
  have hdist0 : P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ :=
    distinctNormalized_of_noRepeat hP hnr hij hjle
  have hdist : P ⟨i + 1, hi1⟩ ≠ P ⟨j, hj⟩ := by
    simpa using hdist0
  obtain ⟨h, _hnorm, hhemPos⟩ := hhem
  have hanti : (P ⟨i + 1, hi1⟩ : E3) ≠ -(P ⟨j, hj⟩ : E3) :=
    hemisphere_nonAntipodal hhemPos ⟨i + 1, hi1⟩ ⟨j, hj⟩
  have hbaseShort : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) :=
    ⟨hdist, hanti⟩
  have hjm1 : j - 1 < n + 1 := by omega
  have hspan' : (P ⟨i, by omega⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) := by
    simpa using hspan
  have hpredSucc : ((⟨j - 1, hjm1⟩ : Fin (n + 1)) + 1) =
      (⟨j, hj⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone,
      Nat.mod_eq_of_lt (show (j - 1) + 1 < n + 1 by omega)]
    change (j - 1) + 1 = j
    omega
  have hsucc : ((⟨j, hj⟩ : Fin (n + 1)) + 1) =
      (⟨j + 1, hj1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone,
      Nat.mod_eq_of_lt (show j + 1 < n + 1 by omega)]
  have hpredShort : ShortArc (P ⟨j, hj⟩) (P ⟨j - 1, hjm1⟩) := by
    have h := hP.closed_convex.edge_short ⟨j - 1, hjm1⟩
    rw [hpredSucc] at h
    exact h.symm
  have hsuccShort : ShortArc (P ⟨j, hj⟩) (P ⟨j + 1, hj1⟩) := by
    have h := hP.closed_convex.edge_short ⟨j, hj⟩
    rwa [hsucc] at h
  have hEpred_mid : 0 ≤ det3 (P ⟨j - 1, hjm1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) := by
    have h := hP.closed_convex.edge_support ⟨j - 1, hjm1⟩ ⟨i + 1, hi1⟩
    rw [hpredSucc] at h
    exact h
  have hEpred_i : 0 ≤ det3 (P ⟨j - 1, hjm1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i, by omega⟩ : E3) := by
    have h := hP.closed_convex.edge_support ⟨j - 1, hjm1⟩ ⟨i, by omega⟩
    rw [hpredSucc] at h
    exact h
  have hEpred_read :
      0 ≤ a * det3 (P ⟨j - 1, hjm1⟩ : E3) (P ⟨j, hj⟩ : E3)
        (P ⟨i + 1, hi1⟩ : E3) :=
    nearSide_a_readout hi1 hj hjm1 hspan' hEpred_i
  have hEpred0 : det3 (P ⟨j - 1, hjm1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) = 0 := by
    nlinarith [hEpred_read, hEpred_mid, ha]
  have hEsucc_mid : 0 ≤ det3 (P ⟨j, hj⟩ : E3) (P ⟨j + 1, hj1⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) := by
    have h := hP.closed_convex.edge_support ⟨j, hj⟩ ⟨i + 1, hi1⟩
    rw [hsucc] at h
    exact h
  have hEsucc_i : 0 ≤ det3 (P ⟨j, hj⟩ : E3) (P ⟨j + 1, hj1⟩ : E3)
      (P ⟨i, by omega⟩ : E3) := by
    have h := hP.closed_convex.edge_support ⟨j, hj⟩ ⟨i, by omega⟩
    rw [hsucc] at h
    exact h
  have hEsucc_read :
      0 ≤ a * det3 (P ⟨j, hj⟩ : E3) (P ⟨j + 1, hj1⟩ : E3)
        (P ⟨i + 1, hi1⟩ : E3) :=
    nearSide_a_readout_succ hi1 hj hj1 hspan' hEsucc_i
  have hEsucc0 : det3 (P ⟨j, hj⟩ : E3) (P ⟨j + 1, hj1⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) = 0 := by
    nlinarith [hEsucc_read, hEsucc_mid, ha]
  exact not_both_witness_zero (B := B) hpos hB hangle hi1 hj hjm1 hj1 hij2
    hbaseShort hpredShort hsuccShort hEpred0 hEsucc0


















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







/-- Row expansion at the parent edge `(Ai, Aip1)`: if
`Ai = a • Aip1 + b • Aj`, then the support of the diagonal `(Aj, Aip1)`
multiplied by `b` is the parent edge support. -/
theorem det3_rowExpand_edge {a b : ℝ} {Ai Aip1 Aj V : E3}
    (hspan : Ai = a • Aip1 + b • Aj) :
    b * det3 Aj Aip1 V = det3 Ai Aip1 V := by
  rw [hspan, det3_add_fst, det3_smul_fst, det3_smul_fst]
  have hself : det3 Aip1 Aip1 V = 0 := by
    simp only [det3]
    ring
  rw [hself]
  ring

/-- A positive real span relation gives the NNReal betweenness consumed by the
folded-flat forward transport. -/
theorem span_mem_of_positive_coeffs {n : ℕ} {P : Fin (n + 1) → S2}
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (hapos : 0 < a) :
    (P ⟨i, hi⟩ : E3) ∈
      Submodule.span NNReal
        ({(P ⟨i + 1, hi1⟩ : E3), (P ⟨j, hj⟩ : E3)} : Set E3) := by
  rw [Submodule.mem_span_pair]
  refine ⟨⟨a, le_of_lt hapos⟩, ⟨b, le_of_lt hbpos⟩, ?_⟩
  rw [NNReal.smul_def, NNReal.smul_def]
  exact hspan.symm

/-- The A-side interval wrap data for `P[i+1..j]`, derived from the positive
span relation and the parent weak convexity. -/
theorem intervalWrapData_of_positive_span {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hnr : NoNonadjacentRepeat P)
    {i j : ℕ} (hij : i + 1 < j) (hfar : i + 2 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) :
    IntervalWrapData P (i + 1) (j - (i + 1)) (by omega) := by
  have hidxj :
      (⟨(i + 1) + (j - (i + 1)), by omega⟩ : Fin (n + 1)) = ⟨j, hj⟩ :=
    Fin.ext (by simp; omega)
  refine
    { wrap_short := ?_
      wrap_support := ?_ }
  · rw [hidxj]
    have hdist0 : P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ :=
      distinctNormalized_of_noRepeat hP hnr hij (by omega)
    obtain ⟨h, _hnorm, hhem⟩ := hP.closed_convex.open_hemisphere
    refine ⟨?_, ?_⟩
    · intro heq
      exact hdist0 (by simpa using heq.symm)
    · exact hemisphere_nonAntipodal hhem ⟨j, hj⟩ ⟨i + 1, hi1⟩
  · intro v hv
    rw [hidxj]
    have hsucc : ((⟨i, hi⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    have hpar :
        0 ≤ sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩)
          (P ⟨i + 1 + v, by have := hv; omega⟩) := by
      have hs := hP.closed_convex.edge_support ⟨i, hi⟩
        ⟨i + 1 + v, by have := hv; omega⟩
      rwa [hsucc] at hs
    have hrow := det3_rowExpand_edge (a := a) (b := b)
      (Ai := (P ⟨i, hi⟩ : E3)) (Aip1 := (P ⟨i + 1, hi1⟩ : E3))
      (Aj := (P ⟨j, hj⟩ : E3))
      (V := (P ⟨i + 1 + v, by have := hv; omega⟩ : E3)) hspan
    have hge :
        0 ≤ b * det3 (P ⟨j, hj⟩ : E3) (P ⟨i + 1, hi1⟩ : E3)
          (P ⟨i + 1 + v, by have := hv; omega⟩ : E3) := by
      rw [hrow]
      exact hpar
    have hdiag :
        0 ≤ det3 (P ⟨j, hj⟩ : E3) (P ⟨i + 1, hi1⟩ : E3)
          (P ⟨i + 1 + v, by have := hv; omega⟩ : E3) :=
      (mul_nonneg_iff_of_pos_left hbpos).mp hge
    simpa [sOrient]
      using hdiag

/-- Strict interval wrap data for `B[i+1..j]`, from the unconditional cyclic
triple theorem for strict spherical polygons. -/
theorem intervalWrapDataStrict_of_cyclicTriple {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B)
    {i j : ℕ} (_hij : i + 1 < j) (hfar : i + 2 < j) (hj : j < n + 1) :
    IntervalWrapDataStrict B (i + 1) (j - (i + 1)) (by omega) := by
  have hcyc :
      ProofsInTheBook.SphericalCyclicTriple.CyclicTriplePos (n := n + 1) B :=
    ProofsInTheBook.PlanarConvexDiag.cyclicTriplePos_unconditional hB.closed_convex
  have hidxj :
      (⟨(i + 1) + (j - (i + 1)), by omega⟩ : Fin (n + 1)) = ⟨j, hj⟩ :=
    Fin.ext (by simp; omega)
  refine
    { toWeak :=
        { wrap_short := ?_
          wrap_support := ?_ }
      wrap_strict := ?_ }
  · rw [hidxj]
    have hpos :
        0 < sOrient (B ⟨i + 1, by omega⟩) (B ⟨i + 2, by omega⟩) (B ⟨j, hj⟩) :=
      hcyc ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ ⟨j, hj⟩
        (by exact_mod_cast (show i + 1 < i + 2 by omega))
        (by exact_mod_cast (show i + 2 < j by omega))
    obtain ⟨h, _hnorm, hhem⟩ := hB.closed_convex.open_hemisphere
    refine ⟨?_, ?_⟩
    · intro heq
      rw [heq] at hpos
      have hz :
          sOrient (B ⟨i + 1, by omega⟩) (B ⟨i + 2, by omega⟩)
            (B ⟨i + 1, by omega⟩) = 0 := by
        simp only [sOrient, det3]
        ring
      rw [hz] at hpos
      exact lt_irrefl 0 hpos
    · exact hemisphere_nonAntipodal hhem ⟨j, hj⟩ ⟨i + 1, by omega⟩
  · intro v hv
    rw [hidxj]
    by_cases hv0 : v = 0
    · subst hv0
      have hidx0 :
          (⟨i + 1 + 0, by omega⟩ : Fin (n + 1)) =
            (⟨i + 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
      rw [hidx0, sOrient]
      have hz :
          det3 (B ⟨j, hj⟩ : E3) (B ⟨i + 1, by omega⟩ : E3)
            (B ⟨i + 1, by omega⟩ : E3) = 0 := by
        simp only [det3]
        ring
      rw [hz]
    · by_cases hvm : v = j - (i + 1)
      · subst hvm
        have hidxv :
            (⟨i + 1 + (j - (i + 1)), by omega⟩ : Fin (n + 1)) = ⟨j, hj⟩ :=
          Fin.ext (by omega)
        rw [hidxv, sOrient]
        have hz :
            det3 (B ⟨j, hj⟩ : E3) (B ⟨i + 1, by omega⟩ : E3)
              (B ⟨j, hj⟩ : E3) = 0 := by
          simp only [det3]
          ring
        rw [hz]
      · have hmid_lt : i + 1 < i + 1 + v := by omega
        have hmid_j : i + 1 + v < j := by omega
        have hpos :
            0 < sOrient (B ⟨i + 1, by omega⟩)
              (B ⟨i + 1 + v, by have := hv; omega⟩) (B ⟨j, hj⟩) :=
          hcyc ⟨i + 1, by omega⟩ ⟨i + 1 + v, by have := hv; omega⟩ ⟨j, hj⟩
            (by exact_mod_cast hmid_lt) (by exact_mod_cast hmid_j)
        rw [sOrient_cyclic (B ⟨j, hj⟩) (B ⟨i + 1, by omega⟩)
          (B ⟨i + 1 + v, by have := hv; omega⟩)]
        exact le_of_lt hpos
  · intro v hv hvm hv0
    rw [hidxj]
    have hmid_lt : i + 1 < i + 1 + v := by omega
    have hmid_j : i + 1 + v < j := by omega
    have hpos :
        0 < sOrient (B ⟨i + 1, by omega⟩)
          (B ⟨i + 1 + v, by have := hv; omega⟩) (B ⟨j, hj⟩) :=
      hcyc ⟨i + 1, by omega⟩ ⟨i + 1 + v, by have := hv; omega⟩ ⟨j, hj⟩
        (by exact_mod_cast hmid_lt) (by exact_mod_cast hmid_j)
    rw [sOrient_cyclic (B ⟨j, hj⟩) (B ⟨i + 1, by omega⟩)
      (B ⟨i + 1 + v, by have := hv; omega⟩)]
    exact hpos




























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



/-- `MainPlus` with `NoNonadjacentRepeat` threaded on the weak left arm. -/
def MainPlusNR (n : ℕ) : Prop :=
  ∀ A B : Fin (n + 1) → S2,
    WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
    StrictConvexSphArm B → SameSides A B → JointLe A B →
    endpt A ≤ endpt B

/-- The opening step consumed by the `MainPlusNR` recursion. -/
def SZOpeningStepPlusNR : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → MainPlusNR m) →
    (∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      (∀ A' B' : Fin (n + 1) → S2,
        WeakConvexSphArm A' → PositiveJoints A' → NoNonadjacentRepeat A' →
        StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
        deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B') →
      endpt A ≤ endpt B)

































































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



namespace DeleteSet





















end DeleteSet

open DeleteSet











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























section OrbitSplit



open scoped Classical















end OrbitSplit





section RawRestrict



open scoped Classical







































open scoped Classical













































































end RawRestrict



section ChordThreading



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

open Equiv Equiv.Perm



section ListBridge









end ListBridge



section OrbitBridge











end OrbitBridge



section StrictBridge













end StrictBridge



section ActiveComponent















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

open Equiv Equiv.Perm





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

open Equiv Equiv.Perm































































































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
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13Realization



namespace List



end List

















































































namespace ConvexPolytopeRealization










































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








namespace ConvexEuclideanPolyhedron











end ConvexEuclideanPolyhedron



































































































































































namespace ListCyclicOrder



















end ListCyclicOrder

















































































































namespace RotTwoBlockCert




























end RotTwoBlockCert








































































































































end ProofsInTheBook.Ch13Cauchy3D

end
end


