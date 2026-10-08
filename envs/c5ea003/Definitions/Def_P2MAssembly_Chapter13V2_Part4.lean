-- Prove2me | Definitions.Def_P2MAssembly_Chapter13V2_Part4
-- name    : P2MAssembly_Chapter13V2_Part4
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T20:42:32.595533+00:00
-- url     : https://prove2.me/theorems/2337a020-b563-465a-bbbf-27b56a085925
-- title:
--   Spherical boundary cases, signed maps, and boundary cycles
-- statement:
--   This part continues weak and strict spherical boundary-support cases and the arm-monotonicity interfaces. It introduces positive, negative and zero edge signs, cyclic sign-change counts with zeros omitted, and structures describing opening or closing obstructions at a fixed endpoint chord. It also provides simple-map, permutation restriction, and boundary-cycle data. Obstruction structures describe configurations that later results refute; defining them does not assert their existence. Boundary paths and arc-split certificates retain the exact combinatorial fields of the source rather than an added geometric embedding claim.
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
import Definitions.Def_P2MAssembly_Chapter13V2_Part3

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







theorem mainPlusNR_of_lt_two {m : ℕ} (hm : m < 2) : MainPlusNR m :=
  fun A B hA _ _ hB hside hangle => main_of_lt_two hm A B hA hB hside hangle



/-- Interval subarms inherit no nonadjacent repeats. -/
theorem intervalArm_noNonadjacentRepeat {N : ℕ} {A : Fin (N + 1) → S2}
    (hnr : NoNonadjacentRepeat A) {a m : ℕ} (hb : a + m ≤ N) :
    NoNonadjacentRepeat (intervalArm A a m hb) := by
  intro r s hr hs hrs heq
  have hAeq : A ⟨a + r, by omega⟩ = A ⟨a + s, by omega⟩ := by
    simpa [intervalArm_apply] using heq
  exact hnr (a + r) (a + s) (by omega) (by omega) (by omega) hAeq

/-- Ear chord comparison from the `MainPlusNR` IH. -/
theorem ear_chord_le_of_MainPlusNR {N : ℕ} {A B : Fin (N + 1) → S2} {a m : ℕ}
    (hb : a + m ≤ N)
    (hMm : MainPlusNR m)
    (hposA : PositiveJoints A)
    (hnrA : NoNonadjacentRepeat A)
    (hAe : WeakConvexSphArm (intervalArm A a m hb))
    (hBe : StrictConvexSphArm (intervalArm B a m hb))
    (hside : ∀ i : Fin N, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (N - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩)
      ≤ sDist (B ⟨a, by omega⟩) (B ⟨a + m, by omega⟩) := by
  have hposEar : PositiveJoints (intervalArm A a m hb) :=
    intervalArm_positiveJoints a m hb hposA
  have hnrEar : NoNonadjacentRepeat (intervalArm A a m hb) :=
    intervalArm_noNonadjacentRepeat hnrA hb
  have hcmp : endpt (intervalArm A a m hb) ≤ endpt (intervalArm B a m hb) :=
    hMm (intervalArm A a m hb) (intervalArm B a m hb) hAe hposEar hnrEar hBe
      (intervalArm_sameSides hb hside) (intervalArm_jointLe hb hangle)
  rwa [intervalArm_endpt A a m hb, intervalArm_endpt B a m hb] at hcmp

/-- `(0,n)` folded-flat boundary close with the NR induction hypothesis. -/
theorem foldedFlat_boundary_j_eq_n_nr {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (ih : ∀ m : ℕ, m < n → MainPlusNR m)
    (hposA : PositiveJoints A)
    (hnrA : NoNonadjacentRepeat A)
    (hside : SameSides A B)
    (hangle : JointLe A B)
    (hAe : WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)))
    (hBe : StrictConvexSphArm (intervalArm B 1 (n - 1) (by omega)))
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3)) :
    endpt A ≤ endpt B := by
  have h1n : 1 + (n - 1) = n := by omega
  have hbtw : sDist (A ⟨1, by omega⟩) (A ⟨n, by omega⟩)
      = sDist (A ⟨1, by omega⟩) (A ⟨0, by omega⟩)
        + sDist (A ⟨0, by omega⟩) (A ⟨n, by omega⟩) :=
    sDist_betweenness_of_collinear (p := A ⟨1, by omega⟩) (q := A ⟨0, by omega⟩)
      (r := A ⟨n, by omega⟩) hcol
  have hMm : MainPlusNR (n - 1) := ih (n - 1) (by omega)
  have hear0 := ear_chord_le_of_MainPlusNR (A := A) (B := B) (a := 1) (m := n - 1)
    (by omega) hMm hposA hnrA hAe hBe hside hangle
  have hidx : (⟨1 + (n - 1), by omega⟩ : Fin (n + 1)) = (⟨n, by omega⟩ : Fin (n + 1)) :=
    Fin.ext h1n
  rw [hidx] at hear0
  have hear : sDist (A ⟨1, by omega⟩) (A ⟨n, by omega⟩)
      ≤ sDist (B ⟨1, by omega⟩) (B ⟨n, by omega⟩) := hear0
  have hs0 := hside ⟨0, by omega⟩
  have hsA : sideLen A (⟨0, by omega⟩ : Fin n) =
      sDist (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) := by
    rw [sideLen]; rfl
  have hsB : sideLen B (⟨0, by omega⟩ : Fin n) =
      sDist (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) := by
    rw [sideLen]; rfl
  rw [hsA, hsB] at hs0
  have htriB : sDist (B ⟨1, by omega⟩) (B ⟨n, by omega⟩)
      ≤ sDist (B ⟨1, by omega⟩) (B ⟨0, by omega⟩)
        + sDist (B ⟨0, by omega⟩) (B ⟨n, by omega⟩) :=
    sDist_triangle (B ⟨1, by omega⟩) (B ⟨0, by omega⟩) (B ⟨n, by omega⟩)
  have hsymmA : sDist (A ⟨1, by omega⟩) (A ⟨0, by omega⟩) =
      sDist (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) := sDist_comm _ _
  have hsymmB : sDist (B ⟨1, by omega⟩) (B ⟨0, by omega⟩) =
      sDist (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) := sDist_comm _ _
  have heA : endpt A = sDist (A ⟨0, by omega⟩) (A ⟨n, by omega⟩) := by
    rw [endpt]; congr 1
  have heB : endpt B = sDist (B ⟨0, by omega⟩) (B ⟨n, by omega⟩) := by
    rw [endpt]; congr 1
  rw [heA, heB]
  linarith [hbtw, hear, hs0, htriB, hsymmA, hsymmB]

/-- Forward folded-flat transport with the NR dimension IH. -/
theorem foldedFlatCutTransportPlusForwardNR_holds :
    ∀ n : ℕ, 2 ≤ n →
      (∀ m : ℕ, m < n → MainPlusNR m) →
      ∀ A B : Fin (n + 1) → S2,
        WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
        StrictConvexSphArm B → SameSides A B → JointLe A B →
        ∀ i j : ℕ, i + 1 < j →
          ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
          (A ⟨i, by omega⟩ : E3) ∈
            Submodule.span NNReal ({(A ⟨i + 1, hi1⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3) →
          sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
          endpt A ≤ endpt B := by
  intro n hn ih A B hA hposA hnr hB hside hangle i j hij1 hi1 hj hcol hdiag
  rcases Nat.lt_or_ge j (i + 2) with hj2 | hj2
  · omega
  · rcases Nat.eq_or_lt_of_le hj2 with hjeq | hjfar
    · subst hjeq
      exact absurd (foldedFlat_adjacent_contradiction (i := i) hA hposA (by omega) hcol)
        (by exact fun h => h)
    · have hnd := far_fold_nondeg_datum_of_no_repeat hA hnr hjfar hj hcol
      have hclass : i = 0 ∧ (j = n ∨ j = n - 1) :=
        far_fold_boundary_classification_final hA hposA hB hangle hnr hjfar hj hnd
      obtain ⟨hi0, hjcase⟩ := hclass
      subst hi0
      rcases hjcase with hjn | hjn1
      · have hcol' : (A ⟨0, by omega⟩ : E3) ∈
            Submodule.span NNReal
              ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3) := by
          have hidx1 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) =
              (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          have hidxj : (⟨j, hj⟩ : Fin (n + 1)) =
              (⟨n, by omega⟩ : Fin (n + 1)) := Fin.ext hjn
          rwa [hidx1, hidxj] at hcol
        obtain ⟨hAe, hBe⟩ :=
          intervalCerts_of_betweenness_and_interiorCore
            StrictDiagonalInteriorCore_holds hA hnr hB (by omega) hcol'
        exact foldedFlat_boundary_j_eq_n_nr hn ih hposA hnr hside hangle hAe hBe hcol'
      · subst hjn1
        have hcol' : (A ⟨0, by omega⟩ : E3) ∈
            Submodule.span NNReal
              ({(A ⟨1, by omega⟩ : E3), (A ⟨n - 1, by omega⟩ : E3)} : Set E3) := by
          have hidx1 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) =
              (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          have hidxj : (⟨n - 1, hj⟩ : Fin (n + 1)) =
              (⟨n - 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          rwa [hidx1, hidxj] at hcol
        have htail : TailFoldBoundary A (by omega) :=
          TailFoldBoundary_holds_context (by omega) hA hposA hB hangle hnr hcol'
        have hdiag' : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
            ≤ sDist (B ⟨0, by omega⟩) (B ⟨n - 1, by omega⟩) := hdiag
        exact foldedFlat_boundary_j_eq_n_minus_one hn hside htail hdiag'



/-- Diagonal inequality for the positive-positive branch using the NR dimension IH. -/
theorem diag_le_of_positive_span_at_level_nr
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j) (hfar : i + 2 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (hapos : 0 < a) :
    sDist (P ⟨i, hi⟩) (P ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) := by
  have hcol := span_mem_of_positive_coeffs hi hi1 hj hspan hbpos hapos
  have hm : 2 ≤ j - (i + 1) := by omega
  have hbnd : (i + 1) + (j - (i + 1)) ≤ n := by omega
  have hAe : WeakConvexSphArm (intervalArm P (i + 1) (j - (i + 1)) hbnd) :=
    weakConvex_intervalArm_of_wrap hP hm hbnd
      (intervalWrapData_of_positive_span hP hnr hij hfar hi hi1 hj hspan hbpos)
  have hBe : StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1)) hbnd) :=
    strictConvex_intervalArm_of_wrap hB hm hbnd
      (intervalWrapDataStrict_of_cyclicTriple hB hij hfar hj)
  have hMm : MainPlusNR (j - (i + 1)) := ihdim (j - (i + 1)) (by omega)
  have hear0 := ear_chord_le_of_MainPlusNR (A := P) (B := B)
    (a := i + 1) (m := j - (i + 1)) hbnd hMm hpos hnr hAe hBe hside hangle
  have hear : sDist (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩)
      ≤ sDist (B ⟨i + 1, by omega⟩) (B ⟨j, hj⟩) := by
    have hidx1 : (⟨i + 1, by omega⟩ : Fin (n + 1)) = ⟨i + 1, hi1⟩ := rfl
    have hidxj :
        (⟨i + 1 + (j - (i + 1)), by omega⟩ : Fin (n + 1)) = ⟨j, hj⟩ :=
      Fin.ext (by simp; omega)
    rwa [hidx1, hidxj] at hear0
  have hfirst : sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩)
      = sDist (P ⟨i + 1, hi1⟩) (P ⟨i, hi⟩) := by
    simpa using (hside_of_sameSides (A' := P) (B := B) hside hij (by omega))
  have hdiag := diag_le_of_foldedFlat hcol hear hfirst
  simpa using hdiag

/-- Positive-positive coefficient branch at a live NR induction level. -/
theorem bpos_apos_endpoint_at_level_nr
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (hapos : 0 < a) :
    endpt P ≤ endpt B := by
  have hcol := span_mem_of_positive_coeffs hi hi1 hj hspan hbpos hapos
  by_cases hfar : i + 2 < j
  · have hdiag := diag_le_of_positive_span_at_level_nr hP hpos hnr hB hside hangle ihdim
      hij hfar hi hi1 hj hspan hbpos hapos
    exact foldedFlatCutTransportPlusForwardNR_holds n hP.two_le ihdim P B hP hpos hnr hB
      hside hangle i j hij hi1 hj hcol hdiag
  · have hjeq : j = i + 2 := by omega
    subst hjeq
    have hcol2 : (P ⟨i, hi⟩ : E3) ∈
        Submodule.span NNReal
          ({(P ⟨i + 1, hi1⟩ : E3), (P ⟨i + 2, hj⟩ : E3)} : Set E3) := by
      simpa using hcol
    exact False.elim (foldedFlat_adjacent_contradiction (i := i) hP hpos (by omega) hcol2)















































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







/-- A raw weak-entry wrap seed has base index `n`. -/
theorem weak_wrap_base_is_last {n : ℕ} {a : Fin (n + 1)}
    (hwrap : ¬ a.val + 1 < n + 1) :
    a.val = n := by
  have ha := a.isLt
  omega

/-- On a wrap base, the Fin successor is the head vertex. -/
theorem weak_wrap_successor_is_zero {n : ℕ} {a : Fin (n + 1)}
    (hwrap : ¬ a.val + 1 < n + 1) :
    a + 1 = (0 : Fin (n + 1)) := by
  apply Fin.ext
  have ha : a.val = n := weak_wrap_base_is_last hwrap
  have hval : ((a + 1 : Fin (n + 1)) : ℕ) = (a.val + 1) % (n + 1) := by
    rw [Fin.add_def]
    simp
  rw [hval, ha, Nat.mod_self]
  simp












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



/-- A normalized ordinary nonincident support zero, suitable for the landed
cut/seed machinery. -/
def NormalizedInteriorSupportZero {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
    i + 1 < j ∧
      sOrient (A ⟨i, hi⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0

/-- The progress payload produced by a boundary zero. -/
def BoundaryZeroProgress {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  NormalizedInteriorSupportZero A ∨ endpt A ≤ endpt B



/-- A public wrapper around the flat-interior-joint contradiction used by the
wrap-boundary propagation layer. -/
theorem flat_interior_joint_absurd_public
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    {r : ℕ}
    (hr : r + 2 < n + 1)
    (hdet :
      det3 (A ⟨r, by omega⟩ : E3)
           (A ⟨r + 1, by omega⟩ : E3)
           (A ⟨r + 2, by omega⟩ : E3) = 0) :
    False := by
  have hshort_prev : ShortArc (A ⟨r + 1, by omega⟩) (A ⟨r, by omega⟩) := by
    have h := hA.closed_convex.edge_short ⟨r, by omega⟩
    have hsucc :
        ((⟨r, by omega⟩ : Fin (n + 1)) + 1) =
          (⟨r + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show r + 1 < n + 1 by omega)]
    rw [hsucc] at h
    exact h.symm
  have hshort_next : ShortArc (A ⟨r + 1, by omega⟩) (A ⟨r + 2, by omega⟩) := by
    have h := hA.closed_convex.edge_short ⟨r + 1, by omega⟩
    have hsucc :
        ((⟨r + 1, by omega⟩ : Fin (n + 1)) + 1) =
          (⟨r + 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show r + 2 < n + 1 by omega)]
    rwa [hsucc] at h
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero
    (u := A ⟨r, by omega⟩)
    (v := A ⟨r + 1, by omega⟩)
    (w := A ⟨r + 2, by omega⟩)
    hshort_prev hshort_next hdet
  let k : Fin (n - 1) := ⟨r, by omega⟩
  have hposk : 0 < jointAngle A k := hpos k
  have hltk : jointAngle A k < Real.pi := jointAngle_lt_pi hB hangle k
  have hjoint_eq :
      jointAngle A k =
        sphAngle (A ⟨r, by omega⟩) (A ⟨r + 1, by omega⟩)
          (A ⟨r + 2, by omega⟩) := rfl
  rcases hbridge with hzero | hpi
  · rw [hjoint_eq, hzero] at hposk
    exact lt_irrefl 0 hposk
  · rw [hjoint_eq, hpi] at hltk
    exact lt_irrefl Real.pi hltk











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



/-- Boundary progress, allowing the normalized seed to appear on either the arm
or its mirror. -/
def MirrorBoundaryZeroProgress {n : ℕ} (P B : Fin (n + 1) → S2) : Prop :=
  BoundaryZeroProgress P B ∨ BoundaryZeroProgress (mirrorArm P) (mirrorArm B)

/-- The v9 weak-entry wrap seed: the cyclic wrap zero may already close the
endpoint, or may normalize on either orientation. -/
def WeakVanishingWrapSeedResidueV9 : Prop :=
  ∀ {n : ℕ} (P B : Fin (n + 1) → S2),
    WeakConvexSphArm P → PositiveJoints P → NoNonadjacentRepeat P →
    StrictConvexSphArm B → SameSides P B → JointLe P B →
    ∀ a b : Fin (n + 1),
      b ≠ a → b ≠ a + 1 → ¬ a.val + 1 < n + 1 →
      sOrient (P a) (P (a + 1)) (P b) = 0 →
        MirrorBoundaryZeroProgress P B



/-- The v9 signed tail residue: unlike the v8 global tail endpoint field, this
version is consumed at the live NR induction level and therefore carries the
dimension IH needed by the normalized-zero endpoint dispatch. -/
def BPosANegTailCornerResidueV9 : Prop :=
  ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
    SameSides P B → JointLe P B → NoNonadjacentRepeat P →
    (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
    (∀ m : ℕ, m < n → MainPlusNR m) →
    ∀ {i : ℕ}, i + 1 < n →
    ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1),
    ∀ {a b : ℝ},
      (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3) →
      0 < b → a < 0 → endpt P ≤ endpt B



/-- Coefficient dispatch at a fixed NR induction level, using the v9 live tail
residue for the `b > 0, a < 0, j = n` branch. -/
theorem endpoint_of_span_at_level_nr_v9
    (htail : BPosANegTailCornerResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3)) :
    endpt P ≤ endpt B := by
  rcases lt_trichotomy b 0 with hbneg | hb0 | hbpos
  · by_cases hi2 : i + 2 < n + 1
    · exact False.elim (midFold_bneg_false hP hpos hB hangle hi hi1 hi2 hj hhem hspan hbneg)
    · exact bneg_tail_closed_by_normalization hP hpos hB hside hangle hnr hhem
        hij hi hi1 hj hspan hbneg hi2
  · exact False.elim (span_bzero_false_of_weak hP hi hi1 hj hspan hb0)
  · rcases lt_trichotomy a 0 with haneg | ha0 | hapos
    · by_cases hj1 : j + 1 < n + 1
      · exact False.elim
          (bpos_aneg_false_of_successor hP hpos hB hangle hnr hhem
            hij hi hi1 hj hj1 hspan hbpos haneg)
      · have hjn : j = n := by omega
        subst hjn
        exact htail hP hpos hB hside hangle hnr hhem ihdim
          hij hi hi1 hj hspan hbpos haneg
    · have hij2 : i + 2 ≤ j := by omega
      exact False.elim (span_azero_bpos_false_of_noRepeat hnr hi hi1 hj hij2 hspan hbpos ha0)
    · exact bpos_apos_endpoint_at_level_nr hP hpos hnr hB hside hangle ihdim
        hij hi hi1 hj hspan hbpos hapos

/-- A normalized zero support on a weak-positive NR arm closes at a fixed NR
level through the v9 tail residue. -/
theorem endpoint_of_normalized_vanishing_support_at_level_nr_v9
    (htail : BPosANegTailCornerResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hzero : sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) = 0) :
    endpt P ≤ endpt B := by
  obtain ⟨h, hnorm, hhemPos⟩ := hhem
  have hdist : P ⟨i + 1, hi1⟩ ≠ P ⟨j, hj⟩ := by
    have hdist0 : P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ :=
      distinctNormalized_of_noRepeat hP hnr hij (by omega)
    simpa using hdist0
  have hanti : (P ⟨i + 1, hi1⟩ : E3) ≠ -(P ⟨j, hj⟩ : E3) :=
    hemisphere_nonAntipodal hhemPos ⟨i + 1, hi1⟩ ⟨j, hj⟩
  have hdet : det3 (P ⟨i + 1, hi1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i, hi⟩ : E3) = 0 := by
    rw [sOrient] at hzero
    rwa [ProofsInTheBook.ZinanFFCT12.det3_cyclic (P ⟨i, hi⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) (P ⟨j, hj⟩ : E3)] at hzero
  obtain ⟨a, b, hspan⟩ :=
    lin_indep_span_of_det3_zero (P ⟨i + 1, hi1⟩).2 (P ⟨j, hj⟩).2
      (fun h => hdist (S2.ext h)) hanti hdet
  exact endpoint_of_span_at_level_nr_v9 htail hP hpos hnr hB hside hangle
    ⟨h, hnorm, hhemPos⟩ ihdim hij hi hi1 hj hspan

/-- Consume a `BoundaryZeroProgress` payload at a live NR level. -/
theorem endpoint_of_boundaryZeroProgress_at_level_nr
    (htail : BPosANegTailCornerResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (hprog : BoundaryZeroProgress P B) :
    endpt P ≤ endpt B := by
  rcases hprog with hnorm | hend
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hnorm
    exact endpoint_of_normalized_vanishing_support_at_level_nr_v9 htail hP hpos hnr hB
      hside hangle hhem ihdim hij hi hi1 hj hzero
  · exact hend

/-- Consume mirror-aware boundary progress at a live NR level. -/
theorem endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
    (htail : BPosANegTailCornerResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (hprog : MirrorBoundaryZeroProgress P B) :
    endpt P ≤ endpt B := by
  rcases hprog with hdir | hmir
  · exact endpoint_of_boundaryZeroProgress_at_level_nr htail hP hpos hnr hB
      hside hangle hhem ihdim hdir
  · have hmirror : endpt (mirrorArm P) ≤ endpt (mirrorArm B) :=
      endpoint_of_boundaryZeroProgress_at_level_nr htail
        (weakConvex_mirrorArm hP) (positiveJoints_mirrorArm hpos)
        (noNonadjacentRepeat_mirrorArm hnr)
        (strictConvex_mirrorArm hB) (sameSides_mirrorArm hside) (jointLe_mirrorArm hangle)
        (weakConvex_mirrorArm hP).closed_convex.open_hemisphere ihdim hmir
    simpa [endpt_mirrorArm] using hmirror



/-- Raw weak-entry vanishing support normalized or endpoint-closed, modulo only
the v9 wrap-edge residue. -/
theorem weakBoundaryProgress_of_wrapSeedResidueV9
    (hwrap : WeakVanishingWrapSeedResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B) (hside : SameSides P B) (hangle : JointLe P B)
    (hvanish : ∃ a b : Fin (n + 1), b ≠ a ∧ b ≠ a + 1 ∧
      sOrient (P a) (P (a + 1)) (P b) = 0) :
    MirrorBoundaryZeroProgress P B := by
  obtain ⟨a, b, hne, hne1, hsupp⟩ := hvanish
  by_cases hadj : a.val + 1 < n + 1
  · rcases orientationNormalized P hne hne1 hsupp hadj with hdir | hrev
    · obtain ⟨i, j, hij, hj, hzero⟩ := hdir
      left
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      simpa using hzero
    · obtain ⟨i, j, hij, hj, hzero⟩ := hrev
      right
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      exact mirrorArm_sOrient_zero_of_revArm_zero P (by omega) (by omega) (by omega) hzero
  · exact hwrap P B hP hpos hnr hB hside hangle a b hne hne1 hadj hsupp

/-- Static weak-entry endpoint closure under NR, consuming v9 boundary progress
directly. -/
def WeakPositiveCutReadyNRV9 : Prop :=
  WeakVanishingWrapSeedResidueV9 → BPosANegTailCornerResidueV9 →
    ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
      WeakConvexSphArm P → PositiveJoints P → NoNonadjacentRepeat P →
      StrictConvexSphArm B → SameSides P B → JointLe P B →
      (∀ m : ℕ, m < n → MainPlusNR m) →
      (∃ a b : Fin (n + 1), b ≠ a ∧ b ≠ a + 1 ∧
        sOrient (P a) (P (a + 1)) (P b) = 0) →
      endpt P ≤ endpt B

theorem weakPositiveCutReadyNR_v9_holds : WeakPositiveCutReadyNRV9 := by
  intro hwrap htail n P B hP hpos hnr hB hside hangle ihdim hvanish
  have hprog := weakBoundaryProgress_of_wrapSeedResidueV9 hwrap
    hP hpos hnr hB hside hangle hvanish
  exact endpoint_of_mirrorBoundaryZeroProgress_at_level_nr htail
    hP hpos hnr hB hside hangle hP.closed_convex.open_hemisphere ihdim hprog






































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

/-- The Chapter 13 strict spherical-arm monotonicity headline. -/
def SphericalArmMonotone : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ A B : Fin (n + 1) → S2,
    StrictConvexSphArm A → StrictConvexSphArm B →
    (∀ i : Fin n, sideLen A i = sideLen B i) →
    (∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) →
      sDist (A 0) (A (Fin.last n)) ≤
        sDist (B 0) (B (Fin.last n))













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













/-- A wrap-boundary zero places the head vertex `A 0` in the real span of the
two anchors `A n` and `A j`, provided those anchors are not equal or antipodal.
The signs of these coefficients are exactly the missing trichotomy data for the
full propagation theorem. -/
theorem wrap_zero_real_span
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hdist : A (Fin.last n) ≠ A j)
    (hanti : (A (Fin.last n) : E3) ≠ -(A j : E3))
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    ∃ c d : ℝ,
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3) := by
  have hdet :
      det3 (A (Fin.last n) : E3) (A j : E3) (A 0 : E3) = 0 := by
    rw [sOrient] at hzero
    rw [ProofsInTheBook.ZinanFFCT5.det3_swap23
      (A (Fin.last n) : E3) (A 0 : E3) (A j : E3)]
    simp [hzero]
  exact lin_indep_span_of_det3_zero
    (A (Fin.last n)).2 (A j).2
    (fun heq => hdist (S2.ext heq)) hanti hdet

/-- The open-hemisphere certificate supplies the non-antipodal half of the
anchor nondegeneracy needed for `wrap_zero_real_span`. -/
theorem wrap_anchor_nonAntipodal_of_hemisphere
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ)) :
    (A (Fin.last n) : E3) ≠ -(A j : E3) := by
  obtain ⟨_, _, hpos⟩ := hhem
  exact hemisphere_nonAntipodal hpos (Fin.last n) j

/-- The last vertex is distinct from any probe index different from `Fin.last`.
For far probes this is `NoNonadjacentRepeat`; for the predecessor probe it is
the ordinary short edge `(n-1,n)`. -/
theorem wrap_anchor_distinct_of_noRepeat
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hj_ne_last : j ≠ Fin.last n) :
    A (Fin.last n) ≠ A j := by
  intro heq
  have hjlt : j.val < n := by
    have hjn : j.val ≠ n := by
      intro hjn
      apply hj_ne_last
      exact Fin.ext (by simpa using hjn)
    omega
  by_cases hfar : j.val + 2 ≤ n
  · have hbad :
        A ⟨j.val, j.isLt⟩ ≠ A ⟨n, by omega⟩ :=
      hnr j.val n j.isLt (by omega) hfar
    apply hbad
    have hjidx : (⟨j.val, j.isLt⟩ : Fin (n + 1)) = j := Fin.ext rfl
    have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
    simpa [hjidx, hlast] using heq.symm
  · have hjpred : j.val + 1 = n := by omega
    have hedge : ShortArc (A j) (A (j + 1)) :=
      hA.closed_convex.edge_short j
    have hsucc : j + 1 = Fin.last n := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by have hn := hA.two_le; omega)
      rw [Fin.val_add, hone, Nat.mod_eq_of_lt (show j.val + 1 < n + 1 by omega)]
      exact hjpred
    have hneq : A j ≠ A (Fin.last n) := by
      simpa [hsucc] using hedge.1
    exact hneq heq.symm

/-- Contextual form of the initial real-span extraction. -/
theorem wrap_zero_real_span_of_context
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    (hj_ne_last : j ≠ Fin.last n)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    ∃ c d : ℝ,
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3) :=
  wrap_zero_real_span
    (wrap_anchor_distinct_of_noRepeat hA hnr hj_ne_last)
    (wrap_anchor_nonAntipodal_of_hemisphere hhem)
    hzero





/-- A real scalar multiple of one sphere point equal to another sphere point is
equality when both vertices lie in the same strict open hemisphere. -/
theorem s2_eq_of_real_smul_with_positive_inner
    {x y : S2} {h : E3} {a : ℝ}
    (hx : 0 < (⟪h, (x : E3)⟫ : ℝ))
    (hy : 0 < (⟪h, (y : E3)⟫ : ℝ))
    (hxy : (x : E3) = a • (y : E3)) :
    x = y := by
  have hinner :
      (⟪h, (x : E3)⟫ : ℝ) = a * (⟪h, (y : E3)⟫ : ℝ) := by
    rw [hxy, inner_smul_right]
  have ha : 0 < a := by nlinarith [hinner, hx, hy]
  have hnorm := congrArg (fun v : E3 => ‖v‖) hxy
  simp only [norm_smul, Real.norm_eq_abs] at hnorm
  rw [x.2, y.2, mul_one] at hnorm
  have ha1 : a = 1 := by
    rw [abs_of_pos ha] at hnorm
    linarith
  exact S2.ext (by rw [hxy, ha1, one_smul])

/-- The head vertex is distinct from any nonzero probe.  The adjacent case is
the first short edge; the remaining cases are `NoNonadjacentRepeat`. -/
theorem wrap_head_distinct_of_noRepeat
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hj_ne_zero : j ≠ 0) :
    A 0 ≠ A j := by
  intro heq
  have hjpos : 0 < j.val := by
    have hj0 : j.val ≠ 0 := by
      intro hj0
      apply hj_ne_zero
      exact Fin.ext (by simpa using hj0)
    omega
  by_cases hjone : j.val = 1
  · have hedge : ShortArc (A (0 : Fin (n + 1))) (A ((0 : Fin (n + 1)) + 1)) :=
      hA.closed_convex.edge_short 0
    have hsucc : ((0 : Fin (n + 1)) + 1) = j := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by have hn := hA.two_le; omega)
      simp [Nat.mod_eq_of_lt (show 1 < n + 1 by have hn := hA.two_le; omega), hjone]
    have hneq : A 0 ≠ A j := by
      simpa [hsucc] using hedge.1
    exact hneq heq
  · have hfar : 0 + 2 ≤ j.val := by omega
    have hbad : A ⟨0, by omega⟩ ≠ A ⟨j.val, j.isLt⟩ :=
      hnr 0 j.val (by omega) j.isLt hfar
    apply hbad
    have hzero : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
    have hjidx : (⟨j.val, j.isLt⟩ : Fin (n + 1)) = j := Fin.ext rfl
    simpa [hzero, hjidx] using heq

/-- The closing short edge separates the last vertex from the head vertex. -/
theorem wrap_last_head_distinct_of_weak
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) :
    A (Fin.last n) ≠ A 0 := by
  have hedge : ShortArc (A (Fin.last n)) (A (Fin.last n + 1)) :=
    hA.closed_convex.edge_short (Fin.last n)
  have hwrap : ¬ (Fin.last n).val + 1 < n + 1 := by simp
  have hsucc : (Fin.last n + 1 : Fin (n + 1)) = 0 :=
    weak_wrap_successor_is_zero (a := Fin.last n) hwrap
  simpa [hsucc] using hedge.1

/-- In the initial wrap span, the probe coefficient cannot be the only
surviving coefficient. -/
theorem wrap_initial_last_coeff_zero_absurd
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    (hj_ne_zero : j ≠ 0)
    {c d : ℝ}
    (hspan :
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3))
    (hc0 : c = 0) :
    False := by
  obtain ⟨h, _, hpos⟩ := hhem
  have hscalar : (A 0 : E3) = d • (A j : E3) := by
    rw [hspan, hc0, zero_smul, zero_add]
  have heq : A 0 = A j :=
    s2_eq_of_real_smul_with_positive_inner (hpos 0) (hpos j) hscalar
  exact (wrap_head_distinct_of_noRepeat hA hnr hj_ne_zero) heq

/-- In the initial wrap span, the last-anchor coefficient cannot be the only
surviving coefficient. -/
theorem wrap_initial_probe_coeff_zero_absurd
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {c d : ℝ}
    (hspan :
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3))
    (hd0 : d = 0) :
    False := by
  obtain ⟨h, _, hpos⟩ := hhem
  have hscalar : (A 0 : E3) = c • (A (Fin.last n) : E3) := by
    rw [hspan, hd0, zero_smul, add_zero]
  have heq : A 0 = A (Fin.last n) :=
    s2_eq_of_real_smul_with_positive_inner (hpos 0) (hpos (Fin.last n)) hscalar
  exact (wrap_last_head_distinct_of_weak hA) heq.symm

/-- The initial wrap span cannot have both coefficients negative, because all
vertices lie in a strict open hemisphere. -/
theorem wrap_initial_both_negative_absurd
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {c d : ℝ}
    (hspan :
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3))
    (hc : c < 0) (hd : d < 0) :
    False := by
  obtain ⟨h, _, hpos⟩ := hhem
  have hinner :
      (⟪h, (A 0 : E3)⟫ : ℝ) =
        c * (⟪h, (A (Fin.last n) : E3)⟫ : ℝ) +
          d * (⟪h, (A j : E3)⟫ : ℝ) := by
    rw [hspan, inner_add_right, inner_smul_right, inner_smul_right]
  have h0 := hpos 0
  have hn := hpos (Fin.last n)
  have hj := hpos j
  nlinarith [hinner, h0, hn, hj, hc, hd]



































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



/-- A normalized ordinary support zero whose far probe still has an ordinary
successor.  This is the exact side condition that makes the signed tail branch
of the coefficient dispatch vacuous. -/
def NormalizedStrictInteriorSupportZero {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
    i + 1 < j ∧ j + 1 < n + 1 ∧
      sOrient (A ⟨i, hi⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0







/-- Coefficient dispatch for a normalized zero whose far probe has a successor.
The only `b > 0, a < 0` branch is closed by the successor-edge contradiction,
so this consumer has no `BPosANegTailCornerResidueV9` argument. -/
theorem endpoint_of_span_at_level_nr_noTail
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hj1 : j + 1 < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3)) :
    endpt P ≤ endpt B := by
  rcases lt_trichotomy b 0 with hbneg | hb0 | hbpos
  · by_cases hi2 : i + 2 < n + 1
    · exact False.elim (midFold_bneg_false hP hpos hB hangle hi hi1 hi2 hj hhem hspan hbneg)
    · exact bneg_tail_closed_by_normalization hP hpos hB hside hangle hnr hhem
        hij hi hi1 hj hspan hbneg hi2
  · exact False.elim (span_bzero_false_of_weak hP hi hi1 hj hspan hb0)
  · rcases lt_trichotomy a 0 with haneg | ha0 | hapos
    · exact False.elim
        (bpos_aneg_false_of_successor hP hpos hB hangle hnr hhem
          hij hi hi1 hj hj1 hspan hbpos haneg)
    · have hij2 : i + 2 ≤ j := by omega
      exact False.elim (span_azero_bpos_false_of_noRepeat hnr hi hi1 hj hij2 hspan hbpos ha0)
    · exact bpos_apos_endpoint_at_level_nr hP hpos hnr hB hside hangle ihdim
        hij hi hi1 hj hspan hbpos hapos

/-- A normalized zero with a successor on the far probe closes at a live NR
level without invoking the signed-tail residue. -/
theorem endpoint_of_normalized_vanishing_support_at_level_nr_noTail
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hj1 : j + 1 < n + 1)
    (hzero : sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) = 0) :
    endpt P ≤ endpt B := by
  obtain ⟨h, hnorm, hhemPos⟩ := hhem
  have hdist : P ⟨i + 1, hi1⟩ ≠ P ⟨j, hj⟩ := by
    have hdist0 : P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ :=
      distinctNormalized_of_noRepeat hP hnr hij (by omega)
    simpa using hdist0
  have hanti : (P ⟨i + 1, hi1⟩ : E3) ≠ -(P ⟨j, hj⟩ : E3) :=
    hemisphere_nonAntipodal hhemPos ⟨i + 1, hi1⟩ ⟨j, hj⟩
  have hdet : det3 (P ⟨i + 1, hi1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i, hi⟩ : E3) = 0 := by
    rw [sOrient] at hzero
    rwa [ProofsInTheBook.ZinanFFCT12.det3_cyclic (P ⟨i, hi⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) (P ⟨j, hj⟩ : E3)] at hzero
  obtain ⟨a, b, hspan⟩ :=
    lin_indep_span_of_det3_zero (P ⟨i + 1, hi1⟩).2 (P ⟨j, hj⟩).2
      (fun h => hdist (S2.ext h)) hanti hdet
  exact endpoint_of_span_at_level_nr_noTail hP hpos hnr hB hside hangle
    ⟨h, hnorm, hhemPos⟩ ihdim hij hi hi1 hj hj1 hspan

/-- Consume an already-normalized no-tail support zero. -/
theorem endpoint_of_normalizedInteriorZero_noTail
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (hnorm : NormalizedStrictInteriorSupportZero P) :
    endpt P ≤ endpt B := by
  obtain ⟨i, j, hi, hi1, hj, hij, hj1, hzero⟩ := hnorm
  exact endpoint_of_normalized_vanishing_support_at_level_nr_noTail hP hpos hnr hB
    hside hangle hhem ihdim hij hi hi1 hj hj1 hzero


























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



/-- `z` lies in the strict positive real cone spanned by `p` and `q`. -/
def OpenCone (p q z : S2) : Prop :=
  ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
    (z : E3) = c • (p : E3) + d • (q : E3)

/-- A point in `OpenCone p q` is coplanar with the two cone anchors. -/
theorem OpenCone.sOrient_zero {p q z : S2} (h : OpenCone p q z) :
    sOrient p q z = 0 := by
  rcases h with ⟨c, d, _hc, _hd, hrep⟩
  rw [sOrient, hrep]
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring



/-- The `a < 0, b > 0, j = n` span rearranges to
`P n ∈ OpenCone (P i) (P (i+1))`. -/
theorem openCone_tail_of_aneg_bpos
    {n : ℕ} {P : Fin (n + 1) → S2}
    {i : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1)
    {a b : ℝ}
    (hspan :
      (P ⟨i, hi⟩ : E3) =
        a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3))
    (hb : 0 < b) (ha : a < 0) :
    OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n, hn⟩) := by
  refine ⟨1 / b, (-a) / b, div_pos zero_lt_one hb, div_pos (neg_pos.mpr ha) hb, ?_⟩
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbvec :
      b • (P ⟨n, hn⟩ : E3) =
        (P ⟨i, hi⟩ : E3) - a • (P ⟨i + 1, hi1⟩ : E3) := by
    rw [hspan]
    module
  calc
    (P ⟨n, hn⟩ : E3)
        = (1 / b) • (b • (P ⟨n, hn⟩ : E3)) := by
            rw [smul_smul, div_mul_cancel₀ _ hbne, one_smul]
    _ = (1 / b) • ((P ⟨i, hi⟩ : E3) - a • (P ⟨i + 1, hi1⟩ : E3)) := by
            rw [hbvec]
    _ = (1 / b) • (P ⟨i, hi⟩ : E3) + ((-a) / b) • (P ⟨i + 1, hi1⟩ : E3) := by
            rw [smul_sub, smul_smul]
            module



/-- If `C` is in the open cone of fixed anchors `P,Q`, then the two weak
supports of the edge `(Y,C)` at `P` and `Q` force `Y` back into the same
anchor plane. -/
theorem edgeAnchor_prev_plane_of_next_openCone
    {P Q Y C : S2}
    (hC : OpenCone P Q C)
    (hYP : 0 ≤ sOrient Y C P)
    (hYQ : 0 ≤ sOrient Y C Q) :
    sOrient P Q Y = 0 := by
  rcases hC with ⟨c, d, hc, hd, hrep⟩
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hYP' : 0 ≤ -d * D := by
    have hid :
        det3 (Y : E3) (c • (P : E3) + d • (Q : E3)) (P : E3)
          = -d * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [sOrient, hrep] at hYP
    simpa [hid] using hYP
  have hYQ' : 0 ≤ c * D := by
    have hid :
        det3 (Y : E3) (c • (P : E3) + d • (Q : E3)) (Q : E3)
          = c * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [sOrient, hrep] at hYQ
    simpa [hid] using hYQ
  have hDle : D ≤ 0 := by nlinarith [hYP', hd]
  have hDge : 0 ≤ D := by nlinarith [hYQ', hc]
  have hD : D = 0 := by linarith
  simpa [sOrient, D] using hD



/-- An open cone on a consecutive triple contradicts positive non-flat joints. -/
theorem openCone_consecutive_absurd
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B) (hangle : JointLe P B)
    {i : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hi2 : i + 2 < n + 1)
    (hcone : OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩)) :
    False := by
  have hzero := hcone.sOrient_zero
  rw [sOrient] at hzero
  exact flat_interior_joint_absurd_public hP hpos hB hangle (r := i) (by omega) hzero

/-- The signed tail corner is impossible in the adjacent-tail case `i + 2 = n`. -/
theorem bpos_aneg_tail_adjacent_forbidden
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B) (hangle : JointLe P B)
    {i : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1)
    (htight : i + 2 = n)
    {a b : ℝ}
    (hspan :
      (P ⟨i, hi⟩ : E3) =
        a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3))
    (hb : 0 < b) (ha : a < 0) :
    False := by
  have hcone := openCone_tail_of_aneg_bpos hi hi1 hn hspan hb ha
  have hi2 : i + 2 < n + 1 := by omega
  have hidx : (⟨n, hn⟩ : Fin (n + 1)) = ⟨i + 2, hi2⟩ := by
    apply Fin.ext
    exact htight.symm
  have hcone' : OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) := by
    simpa [hidx] using hcone
  exact openCone_consecutive_absurd hP hpos hB hangle hi hi1 hi2 hcone'



















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



/-- In the non-adjacent signed-tail cone, the first backward edge `(n-1,n)`
forces a no-tail normalized support zero on the original edge `(i,i+1)` with
far probe `n-1`. -/
theorem normalizedStrictInteriorSupportZero_of_tail_firstStep
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P)
    {i : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1)
    (hnonadj : i + 2 < n)
    (hcone : OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n, hn⟩)) :
    NormalizedStrictInteriorSupportZero P := by
  have hprev : n - 1 < n + 1 := by omega
  have hsucc :
      (⟨n - 1, hprev⟩ + 1 : Fin (n + 1)) = ⟨n, hn⟩ := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_mk]
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [hone, Nat.mod_eq_of_lt (show n - 1 + 1 < n + 1 by omega)]
    change n - 1 + 1 = n
    omega
  have hYP :
      0 ≤ sOrient (P ⟨n - 1, hprev⟩) (P ⟨n, hn⟩) (P ⟨i, hi⟩) := by
    have h := hP.closed_convex.edge_support ⟨n - 1, hprev⟩ ⟨i, hi⟩
    simpa [hsucc] using h
  have hYQ :
      0 ≤ sOrient (P ⟨n - 1, hprev⟩) (P ⟨n, hn⟩) (P ⟨i + 1, hi1⟩) := by
    have h := hP.closed_convex.edge_support ⟨n - 1, hprev⟩ ⟨i + 1, hi1⟩
    simpa [hsucc] using h
  have hplane :
      sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n - 1, hprev⟩) = 0 :=
    edgeAnchor_prev_plane_of_next_openCone hcone hYP hYQ
  refine ⟨i, n - 1, hi, hi1, hprev, ?_, ?_, hplane⟩ <;> omega

/-- The live signed-tail residue closes directly: the adjacent tail is
impossible, and every non-adjacent tail yields a no-tail normalized support
zero consumed by FFCT81's stratified endpoint dispatcher. -/
theorem bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero :
    BPosANegTailCornerResidueV9 := by
  intro n P B hP hpos hB hside hangle hnr hhem ihdim i hitail hi hi1 hn a b hspan hb ha
  by_cases hnonadj : i + 2 < n
  · have hcone : OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n, hn⟩) :=
      openCone_tail_of_aneg_bpos hi hi1 hn hspan hb ha
    have hnorm : NormalizedStrictInteriorSupportZero P :=
      normalizedStrictInteriorSupportZero_of_tail_firstStep hP hi hi1 hn hnonadj hcone
    exact endpoint_of_normalizedInteriorZero_noTail hP hpos hnr hB
      hside hangle hhem ihdim hnorm
  · have htight : i + 2 = n := by omega
    exact False.elim
      (bpos_aneg_tail_adjacent_forbidden hP hpos hB hangle hi hi1 hn
        htight hspan hb ha)











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



/-- If `C` is the first endpoint of an ordinary edge and lies in the open cone
of anchors `P,Q`, then weak supports of the edge `(C,Y)` at both anchors force
`Y` into the anchor plane. -/
theorem edgeAnchor_next_plane_of_prev_openCone
    {P Q C Y : S2}
    (hC : OpenCone P Q C)
    (hCP : 0 ≤ sOrient C Y P)
    (hCQ : 0 ≤ sOrient C Y Q) :
    sOrient P Q Y = 0 := by
  rcases hC with ⟨c, d, hc, hd, hrep⟩
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hCP' : 0 ≤ d * D := by
    have hid :
        det3 (c • (P : E3) + d • (Q : E3)) (Y : E3) (P : E3) =
          d * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [sOrient, hrep] at hCP
    simpa [hid] using hCP
  have hCQ' : 0 ≤ -c * D := by
    have hid :
        det3 (c • (P : E3) + d • (Q : E3)) (Y : E3) (Q : E3) =
          -c * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [sOrient, hrep] at hCQ
    simpa [hid] using hCQ
  have hDge : 0 ≤ D := by nlinarith [hCP', hd]
  have hDle : D ≤ 0 := by nlinarith [hCQ', hc]
  have hD : D = 0 := by linarith
  simpa [sOrient, D] using hD

/-- Coplanarity with the cone anchors turns the predecessor edge `(Y,C)` into
a zero support with the left anchor as probe. -/
theorem openCone_prevEdge_left_zero_of_plane
    {P Q C Y : S2}
    (hC : OpenCone P Q C)
    (hplane : sOrient P Q Y = 0) :
    sOrient Y C P = 0 := by
  rcases hC with ⟨c, d, _hc, _hd, hrep⟩
  rw [sOrient] at hplane ⊢
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hD : D = 0 := by simpa [D] using hplane
  have hid :
      det3 (Y : E3) (c • (P : E3) + d • (Q : E3)) (P : E3) =
        -d * D := by
    simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hrep, hid, hD, mul_zero]

/-- Coplanarity with the cone anchors turns the predecessor edge `(Y,C)` into
a zero support with the right anchor as probe. -/
theorem openCone_prevEdge_right_zero_of_plane
    {P Q C Y : S2}
    (hC : OpenCone P Q C)
    (hplane : sOrient P Q Y = 0) :
    sOrient Y C Q = 0 := by
  rcases hC with ⟨c, d, _hc, _hd, hrep⟩
  rw [sOrient] at hplane ⊢
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hD : D = 0 := by simpa [D] using hplane
  have hid :
      det3 (Y : E3) (c • (P : E3) + d • (Q : E3)) (Q : E3) =
        c * D := by
    simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hrep, hid, hD, mul_zero]

/-- Coplanarity with the cone anchors turns the successor edge `(C,Y)` into
a zero support with the left anchor as probe. -/
theorem openCone_nextEdge_left_zero_of_plane
    {P Q C Y : S2}
    (hC : OpenCone P Q C)
    (hplane : sOrient P Q Y = 0) :
    sOrient C Y P = 0 := by
  rcases hC with ⟨c, d, _hc, _hd, hrep⟩
  rw [sOrient] at hplane ⊢
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hD : D = 0 := by simpa [D] using hplane
  have hid :
      det3 (c • (P : E3) + d • (Q : E3)) (Y : E3) (P : E3) =
        d * D := by
    simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hrep, hid, hD, mul_zero]



/-- Any ordinary raw zero support can be packaged as the v9 mirror-aware
boundary-progress payload by the landed orientation normalizer. -/
theorem mirrorBoundaryProgress_of_raw_ordinary_zero
    {n : ℕ} (P B : Fin (n + 1) → S2) {a b : Fin (n + 1)}
    (hne : b ≠ a) (hne1 : b ≠ a + 1)
    (hadj : a.val + 1 < n + 1)
    (hsupp : sOrient (P a) (P (a + 1)) (P b) = 0) :
    MirrorBoundaryZeroProgress P B := by
  rcases orientationNormalized P hne hne1 hsupp hadj with hdir | hrev
  · left
    left
    obtain ⟨i, j, hij, hj, hzero⟩ := hdir
    refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
    simpa using hzero
  · right
    left
    obtain ⟨i, j, hij, hj, hzero⟩ := hrev
    refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
    exact mirrorArm_sOrient_zero_of_revArm_zero P (by omega) (by omega) (by omega) hzero



theorem openCone_last_of_head_span_opposite
    {n : ℕ} {P : Fin (n + 1) → S2} {j : Fin (n + 1)}
    {c d : ℝ}
    (hspan :
      (P 0 : E3) =
        c • (P (Fin.last n) : E3) + d • (P j : E3))
    (hc : 0 < c) (hd : d < 0) :
    OpenCone (P 0) (P j) (P (Fin.last n)) := by
  refine ⟨1 / c, (-d) / c, div_pos zero_lt_one hc,
    div_pos (neg_pos.mpr hd) hc, ?_⟩
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcvec :
      c • (P (Fin.last n) : E3) =
        (P 0 : E3) - d • (P j : E3) := by
    rw [hspan]
    module
  calc
    (P (Fin.last n) : E3)
        = (1 / c) • (c • (P (Fin.last n) : E3)) := by
            rw [smul_smul, div_mul_cancel₀ _ hcne, one_smul]
    _ = (1 / c) • ((P 0 : E3) - d • (P j : E3)) := by
            rw [hcvec]
    _ = (1 / c) • (P 0 : E3) + ((-d) / c) • (P j : E3) := by
            rw [smul_sub, smul_smul]
            module

theorem openCone_probe_of_head_span_opposite
    {n : ℕ} {P : Fin (n + 1) → S2} {j : Fin (n + 1)}
    {c d : ℝ}
    (hspan :
      (P 0 : E3) =
        c • (P (Fin.last n) : E3) + d • (P j : E3))
    (hc : c < 0) (hd : 0 < d) :
    OpenCone (P 0) (P (Fin.last n)) (P j) := by
  refine ⟨1 / d, (-c) / d, div_pos zero_lt_one hd,
    div_pos (neg_pos.mpr hc) hd, ?_⟩
  have hdne : d ≠ 0 := ne_of_gt hd
  have hdvec :
      d • (P j : E3) =
        (P 0 : E3) - c • (P (Fin.last n) : E3) := by
    rw [hspan]
    module
  calc
    (P j : E3)
        = (1 / d) • (d • (P j : E3)) := by
            rw [smul_smul, div_mul_cancel₀ _ hdne, one_smul]
    _ = (1 / d) • ((P 0 : E3) - c • (P (Fin.last n) : E3)) := by
            rw [hdvec]
    _ = (1 / d) • (P 0 : E3) + ((-c) / d) • (P (Fin.last n) : E3) := by
            rw [smul_sub, smul_smul]
            module

/-- A wrap zero at `(n,0,j)` gives v9 mirror-aware boundary progress by one
adjacent-edge step from whichever vertex is the open-cone holder. -/
theorem mirrorBoundaryProgress_of_wrap_firstStep
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hP : WeakConvexSphArm P)
    (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {j : Fin (n + 1)}
    (hj_ne_last : j ≠ Fin.last n)
    (hj_ne_zero : j ≠ 0)
    (hzero : sOrient (P (Fin.last n)) (P 0) (P j) = 0) :
    MirrorBoundaryZeroProgress P B := by
  obtain ⟨c, d, hspan⟩ :=
    wrap_zero_real_span_of_context hP hnr hhem hj_ne_last hzero
  rcases lt_trichotomy c 0 with hcneg | hc0 | hcpos
  · rcases lt_trichotomy d 0 with hdneg | hd0 | hdpos
    · exact False.elim (wrap_initial_both_negative_absurd hhem hspan hcneg hdneg)
    · exact False.elim (wrap_initial_probe_coeff_zero_absurd hP hhem hspan hd0)
    · have hcone : OpenCone (P 0) (P (Fin.last n)) (P j) :=
        openCone_probe_of_head_span_opposite hspan hcneg hdpos
      have hjpos : 0 < j.val := by
        have hj0 : j.val ≠ 0 := by
          intro hj0
          exact hj_ne_zero (Fin.ext (by simpa using hj0))
        omega
      have hjlt : j.val < n := by
        have hjn : j.val ≠ n := by
          intro hjn
          exact hj_ne_last (Fin.ext (by simpa using hjn))
        omega
      let r : ℕ := j.val - 1
      have hr : r < n + 1 := by
        dsimp [r]
        omega
      have hsucc : ((⟨r, hr⟩ : Fin (n + 1)) + 1) = j := by
        apply Fin.ext
        have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, Fin.val_mk, hone,
          Nat.mod_eq_of_lt (show r + 1 < n + 1 by dsimp [r]; omega)]
        dsimp [r]
        omega
      have hY0 :
          0 ≤ sOrient (P ⟨r, hr⟩) (P j) (P 0) := by
        have h := hP.closed_convex.edge_support ⟨r, hr⟩ 0
        simpa [hsucc] using h
      have hYn :
          0 ≤ sOrient (P ⟨r, hr⟩) (P j) (P (Fin.last n)) := by
        have h := hP.closed_convex.edge_support ⟨r, hr⟩ (Fin.last n)
        simpa [hsucc] using h
      have hplane :
          sOrient (P 0) (P (Fin.last n)) (P ⟨r, hr⟩) = 0 :=
        edgeAnchor_prev_plane_of_next_openCone hcone hY0 hYn
      have hraw :
          sOrient (P ⟨r, hr⟩) (P j) (P (Fin.last n)) = 0 :=
        openCone_prevEdge_right_zero_of_plane hcone hplane
      left
      left
      refine ⟨r, n, by omega, by omega, by omega, ?_, ?_⟩
      · dsimp [r]
        omega
      · have hjidx : (⟨r + 1, by omega⟩ : Fin (n + 1)) = j := by
          apply Fin.ext
          dsimp [r]
          omega
        have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n :=
          Fin.ext (by simp)
        simpa [hjidx, hlast] using hraw
  · exact False.elim (wrap_initial_last_coeff_zero_absurd hP hnr hhem hj_ne_zero hspan hc0)
  · rcases lt_trichotomy d 0 with hdneg | hd0 | hdpos
    · have hcone : OpenCone (P 0) (P j) (P (Fin.last n)) :=
        openCone_last_of_head_span_opposite hspan hcpos hdneg
      have hprev : n - 1 < n + 1 := by omega
      have hsucc :
          ((⟨n - 1, hprev⟩ : Fin (n + 1)) + 1) = Fin.last n := by
        apply Fin.ext
        have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, Fin.val_mk, hone,
          Nat.mod_eq_of_lt (show n - 1 + 1 < n + 1 by omega)]
        simp
        omega
      have hY0 :
          0 ≤ sOrient (P ⟨n - 1, hprev⟩) (P (Fin.last n)) (P 0) := by
        have h := hP.closed_convex.edge_support ⟨n - 1, hprev⟩ 0
        simpa [hsucc] using h
      have hYj :
          0 ≤ sOrient (P ⟨n - 1, hprev⟩) (P (Fin.last n)) (P j) := by
        have h := hP.closed_convex.edge_support ⟨n - 1, hprev⟩ j
        simpa [hsucc] using h
      have hplane :
          sOrient (P 0) (P j) (P ⟨n - 1, hprev⟩) = 0 :=
        edgeAnchor_prev_plane_of_next_openCone hcone hY0 hYj
      have hraw0 :
          sOrient (P ⟨n - 1, hprev⟩) (P (Fin.last n)) (P 0) = 0 :=
        openCone_prevEdge_left_zero_of_plane hcone hplane
      let a : Fin (n + 1) := ⟨n - 1, hprev⟩
      let b : Fin (n + 1) := 0
      have hsucc_a : a + 1 = Fin.last n := by simpa [a] using hsucc
      have hne : b ≠ a := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [a, b] at hv
        omega
      have hne1 : b ≠ a + 1 := by
        rw [hsucc_a]
        intro h
        have hv := congrArg Fin.val h
        dsimp [b] at hv
        change (0 : ℕ) = n at hv
        omega
      have hadj : a.val + 1 < n + 1 := by
        dsimp [a]
        omega
      have hraw :
          sOrient (P a) (P (a + 1)) (P b) = 0 := by
        simpa [a, b, hsucc_a] using hraw0
      exact mirrorBoundaryProgress_of_raw_ordinary_zero P B hne hne1 hadj hraw
    · exact False.elim (wrap_initial_probe_coeff_zero_absurd hP hhem hspan hd0)
    · have hcone : OpenCone (P (Fin.last n)) (P j) (P 0) :=
        ⟨c, d, hcpos, hdpos, hspan⟩
      have h1 : 1 < n + 1 := by omega
      have hsucc0 : ((0 : Fin (n + 1)) + 1) = ⟨1, h1⟩ := by
        apply Fin.ext
        have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, Fin.val_zero, hone,
          Nat.mod_eq_of_lt (show 0 + 1 < n + 1 by omega)]
      have h0n :
          0 ≤ sOrient (P 0) (P ⟨1, h1⟩) (P (Fin.last n)) := by
        have h := hP.closed_convex.edge_support (0 : Fin (n + 1)) (Fin.last n)
        simpa [hsucc0] using h
      have h0j :
          0 ≤ sOrient (P 0) (P ⟨1, h1⟩) (P j) := by
        have h := hP.closed_convex.edge_support (0 : Fin (n + 1)) j
        simpa [hsucc0] using h
      have hplane :
          sOrient (P (Fin.last n)) (P j) (P ⟨1, h1⟩) = 0 :=
        edgeAnchor_next_plane_of_prev_openCone hcone h0n h0j
      have hraw :
          sOrient (P 0) (P ⟨1, h1⟩) (P (Fin.last n)) = 0 :=
        openCone_nextEdge_left_zero_of_plane hcone hplane
      left
      left
      refine ⟨0, n, by omega, by omega, by omega, by omega, ?_⟩
      have hzero : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n :=
        Fin.ext (by simp)
      simpa [hzero, hlast] using hraw



theorem weakWrapSeed_v9_of_firstStep :
    WeakVanishingWrapSeedResidueV9 := by
  intro n P B hP _hpos hnr _hB _hside _hangle a b hne hne1 hwrapBase hsupp
  have ha_val : a.val = n := weak_wrap_base_is_last hwrapBase
  have ha : a = Fin.last n := Fin.ext (by simpa using ha_val)
  have hsucc : a + 1 = (0 : Fin (n + 1)) :=
    weak_wrap_successor_is_zero hwrapBase
  have hb_ne_last : b ≠ Fin.last n := by
    intro hb
    exact hne (hb.trans ha.symm)
  have hb_ne_zero : b ≠ 0 := by
    intro hb
    exact hne1 (hb.trans hsucc.symm)
  have hzero :
      sOrient (P (Fin.last n)) (P 0) (P b) = 0 := by
    simpa [ha, hsucc] using hsupp
  exact mirrorBoundaryProgress_of_wrap_firstStep hP.two_le hP hnr
    hP.closed_convex.open_hemisphere hb_ne_last hb_ne_zero hzero















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









/-- The opened WBS arm has no nonadjacent repeats from a local fixed/tail
no-collision statement for this support-stuck branch. -/
theorem openedWBS_noNonadjacentRepeat_of_localNoCross
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (_hB : StrictConvexSphArm B)
    (_hside : SameSides A B) (_hangle : JointLe A B)
    (k : Fin (n - 1)) (_hkdef : jointAngle A k < jointAngle B k)
    (_hstuck : SupportStuckWBS A B k)
    (hnocross :
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r ≤ (openingAxis k).val → (openingAxis k).val < s →
          openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩) :
    NoNonadjacentRepeat (openedWBS A B k) := by
  intro r s hr hs hrs heq
  have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
  by_cases hsK : s ≤ (openingAxis k).val
  · have hrK : r ≤ (openingAxis k).val := by omega
    have hrw : openedWBS A B k ⟨r, hr⟩ = A ⟨r, hr⟩ := by
      unfold openedWBS
      exact openTail_fixed A (openingAxis k) (-(monitoredSupWBS A B k)) hrK
    have hsw : openedWBS A B k ⟨s, hs⟩ = A ⟨s, hs⟩ := by
      unfold openedWBS
      exact openTail_fixed A (openingAxis k) (-(monitoredSupWBS A B k)) hsK
    apply hbase r s hr hs hrs
    rwa [hrw, hsw] at heq
  · have hKs : (openingAxis k).val < s := by omega
    by_cases hrK : r ≤ (openingAxis k).val
    · exact (hnocross r s hr hs hrs hrK hKs) heq
    · have hKr : (openingAxis k).val < r := by omega
      have hrw :
          openedWBS A B k ⟨r, hr⟩ =
            rotS2 (A (openingAxis k)) (-(monitoredSupWBS A B k)) (A ⟨r, hr⟩) := by
        unfold openedWBS
        exact openTail_rot A (openingAxis k) (-(monitoredSupWBS A B k)) hKr
      have hsw :
          openedWBS A B k ⟨s, hs⟩ =
            rotS2 (A (openingAxis k)) (-(monitoredSupWBS A B k)) (A ⟨s, hs⟩) := by
        unfold openedWBS
        exact openTail_rot A (openingAxis k) (-(monitoredSupWBS A B k)) hKs
      apply hbase r s hr hs hrs
      apply rotS2_injective (A (openingAxis k)) (-(monitoredSupWBS A B k))
      rwa [← hrw, ← hsw]



/-- With a local opened-arm no-repeat proof, the raw WBS support-stuck witness
produces the v9 mirror-aware boundary progress.  The wrap edge is handled by
the FFCT85 first-step theorem. -/
theorem supportStuckWBS_boundaryProgress_of_noRepeat_firstStep
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (_hA : StrictConvexSphArm A) (_hB : StrictConvexSphArm B)
    (_hside : SameSides A B) (_hangle : JointLe A B)
    (k : Fin (n - 1)) (_hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k)
    (hPweak : WeakConvexSphArm (openedWBS A B k))
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ)) :
    MirrorBoundaryZeroProgress (openedWBS A B k) B := by
  obtain ⟨a, b, hne, hne1, hsupp0⟩ := supportStuckWBS_vanishingSupport hstuck
  have hsupp :
      sOrient (openedWBS A B k a) (openedWBS A B k (a + 1))
        (openedWBS A B k b) = 0 := by
    simpa [openedWBS] using hsupp0
  by_cases hadj : a.val + 1 < n + 1
  · rcases orientationNormalized (openedWBS A B k) hne hne1 hsupp hadj with hdir | hrev
    · obtain ⟨i, j, hij, hj, hzero⟩ := hdir
      left
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      simpa using hzero
    · obtain ⟨i, j, hij, hj, hzero⟩ := hrev
      right
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      exact mirrorArm_sOrient_zero_of_revArm_zero (openedWBS A B k)
        (by omega) (by omega) (by omega) hzero
  · have ha_val : a.val = n := weak_wrap_base_is_last hadj
    have ha : a = Fin.last n := Fin.ext (by simpa using ha_val)
    have hsucc : a + 1 = (0 : Fin (n + 1)) :=
      weak_wrap_successor_is_zero hadj
    have hb_ne_last : b ≠ Fin.last n := by
      intro hb
      exact hne (hb.trans ha.symm)
    have hb_ne_zero : b ≠ 0 := by
      intro hb
      exact hne1 (hb.trans hsucc.symm)
    have hzero :
        sOrient (openedWBS A B k (Fin.last n)) (openedWBS A B k 0)
          (openedWBS A B k b) = 0 := by
      simpa [ha, hsucc] using hsupp
    exact mirrorBoundaryProgress_of_wrap_firstStep hPweak.two_le hPweak hnr hhem
      hb_ne_last hb_ne_zero hzero


























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



/-- Strict interval wrap data for `A[a..a+m]`, for an arbitrary start `a` (not just `a ≥ 1`).
Mirrors `intervalWrapDataStrict_of_cyclicTriple` but is valid at `a = 0` too. -/
theorem wrapDataStrict_general {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ n) :
    IntervalWrapDataStrict A a m hb := by
  have hcyc : CyclicTriplePos (n := n + 1) A := cyclicTriplePos_unconditional hA.closed_convex
  obtain ⟨h, _hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
  refine { toWeak := { wrap_short := ?_, wrap_support := ?_ }, wrap_strict := ?_ }
  · refine ⟨?_, hemisphere_nonAntipodal hhem ⟨a + m, by omega⟩ ⟨a, by omega⟩⟩
    intro heq
    exact hbase a (a + m) (by omega) (by omega) (by omega) heq.symm
  · intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      have : sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + 0, by omega⟩) = 0 := by
        simp only [sOrient, det3]; ring
      rw [this]
    · by_cases hvm : v = m
      · have hav : a + v = a + m := by omega
        have hidx : (⟨a + v, by omega⟩ : Fin (n + 1)) = ⟨a + m, by omega⟩ := Fin.ext hav
        rw [hidx]
        have : sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩) = 0 := by
          simp only [sOrient, det3]; ring
        rw [this]
      · have hpos : 0 < sOrient (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩) (A ⟨a + m, by omega⟩) :=
          hcyc ⟨a, by omega⟩ ⟨a + v, by omega⟩ ⟨a + m, by omega⟩
            (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
        rw [sOrient_cyclic (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩)]
        exact le_of_lt hpos
  · intro v hv hvm hv0
    have hpos : 0 < sOrient (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩) (A ⟨a + m, by omega⟩) :=
      hcyc ⟨a, by omega⟩ ⟨a + v, by omega⟩ ⟨a + m, by omega⟩
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
    rw [sOrient_cyclic (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩)]
    exact hpos

/-- The subarm `A[a..a+m]` of a strictly convex arm is strictly convex (for `2 ≤ m`). -/
theorem strictConvex_subarm {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ n) :
    StrictConvexSphArm (intervalArm A a m hb) :=
  strictConvex_intervalArm_of_wrap hA hm hb (wrapDataStrict_general hA hm hb)



/-- General oriented tangent datum: for the convex orientation `0 ≤ sOrient a0 axis tail`, the signed
tangent support equals `‖u‖‖w‖ sin (sphAngle a0 axis tail)` (the `+` branch). -/
theorem orientedDatum_sin_general {axis a0 tail : S2}
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsupp : 0 ≤ sOrient a0 axis tail) :
    (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ)
      = ‖tangentTo axis a0‖ * ‖tangentTo axis tail‖ * Real.sin (sphAngle a0 axis tail) := by
  set u : E3 := tangentTo axis a0 with hu
  set w : E3 := tangentTo axis tail with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (axis : E3) w⟫ with hs
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  set γ : ℝ := sphAngle a0 axis tail with hγ
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact sphAngle_nonneg _ _ _
  have hγπ : γ ≤ Real.pi := by rw [hγ]; exact sphAngle_le_pi _ _ _
  have hcEq : c = N * Real.cos γ := by
    have hcos : Real.cos γ = c / N := by
      rw [hγ, sphAngle, InnerProductGeometry.cos_angle]
    rw [hcos]; field_simp
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (axis : E3)) (u := u) (w := w) axis.2
      (tangentTo_orthogonal axis a0) (tangentTo_orthogonal axis tail)
    rw [hc, hs, hN]; rw [mul_pow]; linear_combination this
  have hsinγ : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0 hγπ
  have hssq : s ^ 2 = (N * Real.sin γ) ^ 2 := by
    have hsincos : Real.sin γ ^ 2 = 1 - Real.cos γ ^ 2 := by
      have := Real.sin_sq_add_cos_sq γ; linarith
    have hsc : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [hsc, hcEq]
    linear_combination (-(N ^ 2)) * hsincos
  have hsnn : 0 ≤ s := by
    have hbridge : s = -sOrient axis a0 tail := by
      rw [hs, hu, hw, inner_tangent_cross_eq_neg_sOrient]
    have hswap : sOrient axis a0 tail = -sOrient a0 axis tail := by
      simp only [sOrient, det3]; ring
    rw [hbridge, hswap]; linarith
  have hge : 0 ≤ N * Real.sin γ := mul_nonneg (le_of_lt hNp) hsinγ
  have hsEq : s = N * Real.sin γ := by
    nlinarith [hssq, hsnn, hge, sq_nonneg (s - N * Real.sin γ)]
  rw [hs] at hsEq ⊢
  rw [hsEq, hN]

/-- General signed support of the opened (by `-θ`) triple: `N sin (sphAngle a0 axis tail + θ)`.  Port of
`support_openNeg_eq_sin` for an arbitrary convex-oriented triple. -/
theorem support_openNeg_sin_general {axis a0 tail : S2}
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsupp : 0 ≤ sOrient a0 axis tail) (θ : ℝ) :
    sOrient a0 axis (rotS2 axis (-θ) tail)
      = ‖tangentTo axis a0‖ * ‖tangentTo axis tail‖
          * Real.sin (sphAngle a0 axis tail + θ) := by
  set u : E3 := tangentTo axis a0 with hu
  set w : E3 := tangentTo axis tail with hw
  have hq' : tangentTo axis (rotS2 axis (-θ) tail) = rot (axis : E3) (-θ) w := by
    rw [hw]; exact tangentTo_axis_rotS2 axis tail (-θ)
  have hbridge : sOrient a0 axis (rotS2 axis (-θ) tail)
      = (⟪u, cross (axis : E3) (tangentTo axis (rotS2 axis (-θ) tail))⟫ : ℝ) := by
    have h := inner_tangent_cross_eq_neg_sOrient axis a0 (rotS2 axis (-θ) tail)
    have hswap : sOrient a0 axis (rotS2 axis (-θ) tail)
        = - sOrient axis a0 (rotS2 axis (-θ) tail) := by
      simp only [sOrient, det3]; ring
    rw [hswap, ← h, hu]
  rw [hbridge, hq']
  have hcomm : cross (axis : E3) (rot (axis : E3) (-θ) w)
      = rot (axis : E3) (-θ) (cross (axis : E3) w) := by
    rw [rot_cross axis.2 (-θ) (axis : E3) w, rot_axis axis.2]
  rw [hcomm]
  have horthcw : (⟪cross (axis : E3) w, (axis : E3)⟫ : ℝ) = 0 := inner_cross_left (axis : E3) w
  rw [inner_rot_tangent (axis : E3) (-θ) horthcw]
  have hsval : (⟪u, cross (axis : E3) w⟫ : ℝ)
      = ‖u‖ * ‖w‖ * Real.sin (sphAngle a0 axis tail) := by
    rw [hu, hw]; exact orientedDatum_sin_general hka hkt hsupp
  have haa : (⟪(axis : E3), w⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact tangentTo_orthogonal axis tail
  have haa1 : (⟪(axis : E3), (axis : E3)⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, axis.2]; norm_num
  have hcc : cross (axis : E3) (cross (axis : E3) w) = -w := by
    rw [cross_cross, haa, haa1]; simp
  have hcval : (⟪u, cross (axis : E3) (cross (axis : E3) w)⟫ : ℝ)
      = -(‖u‖ * ‖w‖ * Real.cos (sphAngle a0 axis tail)) := by
    rw [hcc, inner_neg_right]
    have hcosγ : (⟪u, w⟫ : ℝ) = ‖u‖ * ‖w‖ * Real.cos (sphAngle a0 axis tail) := by
      have hγeq : sphAngle a0 axis tail = InnerProductGeometry.angle u w := by
        rw [hu, hw, sphAngle]
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
      rw [← hγeq] at h; linear_combination -h
    rw [hcosγ]
  rw [hsval, hcval, Real.cos_neg, Real.sin_neg]
  rw [Real.sin_add]; ring

/-- **The angle cap from a nonnegative rotated support.**  If the original triple is strictly oriented
(`0 < sOrient a0 axis tail`) and the opened-by-`-θ` triple is weakly oriented
(`0 ≤ sOrient a0 axis (rotS2 axis (-θ) tail)`), with `0 ≤ θ ≤ π`, then `θ + sphAngle a0 axis tail ≤ π`.
Tangent-plane: the rotated support is `N sin (α + θ)` (`support_openNeg_sin_general`), so its
nonnegativity forces `sin (α + θ) ≥ 0`; with `α ∈ (0,π)` and `θ ∈ [0,π]` this gives `α + θ ≤ π`. -/
theorem angle_cap_of_rotated_support_nonneg {axis a0 tail : S2}
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hstrict : 0 < sOrient a0 axis tail)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hrot : 0 ≤ sOrient a0 axis (rotS2 axis (-θ) tail)) :
    θ + sphAngle a0 axis tail ≤ Real.pi := by
  set α := sphAngle a0 axis tail with hα
  have hunz : tangentTo axis a0 ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : tangentTo axis tail ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hNp : 0 < ‖tangentTo axis a0‖ * ‖tangentTo axis tail‖ :=
    mul_pos (norm_pos_iff.2 hunz) (norm_pos_iff.2 hwnz)
  have hsin : sOrient a0 axis (rotS2 axis (-θ) tail)
      = ‖tangentTo axis a0‖ * ‖tangentTo axis tail‖ * Real.sin (α + θ) := by
    rw [hα]; exact support_openNeg_sin_general hka hkt (le_of_lt hstrict) θ
  rw [hsin] at hrot
  have hsinnn : 0 ≤ Real.sin (α + θ) := by
    by_contra h; push_neg at h
    have := mul_neg_of_pos_of_neg hNp h
    linarith [hrot]
  have hdet : det3 (a0 : E3) (axis : E3) (tail : E3) ≠ 0 := ne_of_gt hstrict
  have hα0 : 0 < α := by rw [hα]; exact sphAngle_pos_of_det3_ne a0 axis tail hdet
  have hαπ : α < Real.pi := by rw [hα]; exact sphAngle_lt_pi_of_det3_ne a0 axis tail hdet
  by_contra hcon
  push_neg at hcon
  have h1 : 0 < α + θ - Real.pi := by linarith
  have h2 : α + θ - Real.pi < Real.pi := by linarith
  have hpos : 0 < Real.sin (α + θ - Real.pi) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  have heq : Real.sin (α + θ - Real.pi) = - Real.sin (α + θ) := by
    rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]; ring
  linarith [heq, hpos, hsinnn]



set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1800000 in
/-- **2D Plücker / sine-addition identity in the tangent plane.**
For `axis` unit and three vectors `p, x, n` with `x ⊥ axis`:
`⟪x,x⟫ ⟪p, axis×n⟫ = ⟪p, axis×x⟫ ⟪x,n⟫ + ⟪p,x⟫ ⟪x, axis×n⟫`.
(This is `sin(β+γ) = sinβ cosγ + cosβ sinγ` over constant norms.) -/
theorem plucker_sine_add {axis p x n : E3} (hxa : (⟪x, axis⟫ : ℝ) = 0) :
    (⟪x, x⟫ : ℝ) * (⟪p, cross axis n⟫ : ℝ)
      = (⟪p, cross axis x⟫ : ℝ) * (⟪x, n⟫ : ℝ)
        + (⟪p, x⟫ : ℝ) * (⟪x, cross axis n⟫ : ℝ) := by
  rw [inner_eq_coord x x, inner_eq_coord p (cross axis n), inner_eq_coord p (cross axis x),
    inner_eq_coord x n, inner_eq_coord p x, inner_eq_coord x (cross axis n)]
  simp only [cross_apply_zero, cross_apply_one, cross_apply_two]
  rw [inner_eq_coord] at hxa
  linear_combination
    (n 0 * p 1 * x 2 - n 0 * p 2 * x 1 - n 1 * p 0 * x 2 + n 1 * p 2 * x 0
      + n 2 * p 0 * x 1 - n 2 * p 1 * x 0) * hxa

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1800000 in
/-- **Planar resolution of `n` in the orthogonal basis `{x, axis×x}`** (for `x, n ⊥ axis`, `axis`
unit).  `⟪x,x⟫ • n = ⟪x,n⟫ • x + ⟪axis×x, n⟫ • (axis×x)`. -/
theorem planar_decompose {axis x n : E3} (haxis : ‖axis‖ = 1)
    (hxa : (⟪x, axis⟫ : ℝ) = 0) (hna : (⟪n, axis⟫ : ℝ) = 0) :
    (⟪x, x⟫ : ℝ) • n
      = (⟪x, n⟫ : ℝ) • x + (⟪cross axis x, n⟫ : ℝ) • cross axis x := by
  have haa : (axis 0) ^ 2 + (axis 1) ^ 2 + (axis 2) ^ 2 = 1 := by
    have := real_inner_self_eq_norm_sq axis
    rw [inner_eq_coord, haxis] at this; nlinarith [this]
  rw [inner_eq_coord] at hxa hna
  apply ext_coord
  · simp only [smul_apply, add_apply, cross_apply_zero, cross_apply_one, cross_apply_two,
      inner_eq_coord]
    linear_combination
      (-axis 0 * n 0 * x 0 - axis 0 * n 1 * x 1 - axis 0 * n 2 * x 2 + axis 1 * n 0 * x 1
        - axis 1 * n 1 * x 0 + axis 2 * n 0 * x 2 - axis 2 * n 2 * x 0) * hxa
      + (axis 0 * x 0 ^ 2 + axis 0 * x 1 ^ 2 + axis 0 * x 2 ^ 2) * hna
      + (-n 0 * x 1 ^ 2 - n 0 * x 2 ^ 2 + n 1 * x 0 * x 1 + n 2 * x 0 * x 2) * haa
  · simp only [smul_apply, add_apply, cross_apply_zero, cross_apply_one, cross_apply_two,
      inner_eq_coord]
    linear_combination
      (-axis 0 * n 0 * x 1 + axis 0 * n 1 * x 0 - axis 1 * n 0 * x 0 - axis 1 * n 1 * x 1
        - axis 1 * n 2 * x 2 + axis 2 * n 1 * x 2 - axis 2 * n 2 * x 1) * hxa
      + (axis 1 * x 0 ^ 2 + axis 1 * x 1 ^ 2 + axis 1 * x 2 ^ 2) * hna
      + (n 0 * x 0 * x 1 - n 1 * x 0 ^ 2 - n 1 * x 2 ^ 2 + n 2 * x 1 * x 2) * haa
  · simp only [smul_apply, add_apply, cross_apply_zero, cross_apply_one, cross_apply_two,
      inner_eq_coord]
    linear_combination
      (axis 0 * n 2 * x 0 + axis 1 * n 2 * x 1 - axis 2 * n 0 * x 0 - axis 2 * n 1 * x 1) * hxa
      + (-axis 0 * x 0 * x 2 - axis 1 * x 1 * x 2 + axis 2 * x 0 ^ 2 + axis 2 * x 1 ^ 2) * hna
      + (n 0 * x 0 * x 2 + n 1 * x 1 * x 2 - n 2 * x 0 ^ 2 - n 2 * x 1 ^ 2) * haa

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1800000 in
/-- **2D Plücker / cosine-addition identity in the tangent plane.**
For `axis` unit and three vectors `p, x, n` all orthogonal to `axis`:
`⟪x,x⟫ ⟪p, n⟫ = ⟪p,x⟫ ⟪x,n⟫ - ⟪p, axis×x⟫ ⟪x, axis×n⟫`.
(This is `cos(β+γ) = cosβ cosγ - sinβ sinγ` over constant norms.)  Derived from `planar_decompose`. -/
theorem plucker_cos_add {axis p x n : E3} (haxis : ‖axis‖ = 1)
    (hxa : (⟪x, axis⟫ : ℝ) = 0) (hna : (⟪n, axis⟫ : ℝ) = 0) :
    (⟪x, x⟫ : ℝ) * (⟪p, n⟫ : ℝ)
      = (⟪p, x⟫ : ℝ) * (⟪x, n⟫ : ℝ)
        - (⟪p, cross axis x⟫ : ℝ) * (⟪x, cross axis n⟫ : ℝ) := by
  have hdec := planar_decompose haxis hxa hna
  have h := congrArg (fun v => (⟪p, v⟫ : ℝ)) hdec
  simp only [inner_smul_right, inner_add_right] at h
  have hswap : (⟪cross axis x, n⟫ : ℝ) = -(⟪x, cross axis n⟫ : ℝ) := by
    rw [inner_eq_coord (cross axis x) n, inner_eq_coord x (cross axis n)]
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  rw [hswap] at h
  rw [h]; ring

/-- The signed support datum equals `sOrient a axis b`. -/
theorem datum_eq_sOrient (axis a b : S2) :
    (⟪tangentTo axis a, cross (axis : E3) (tangentTo axis b)⟫ : ℝ) = sOrient a axis b := by
  rw [inner_tangent_cross_eq_neg_sOrient]
  simp only [sOrient, det3]; ring

/-- The cosine datum: `⟪t a, t b⟫ = ‖t a‖‖t b‖ cos (sphAngle a axis b)`. -/
theorem cos_datum (axis a b : S2) :
    (⟪tangentTo axis a, tangentTo axis b⟫ : ℝ)
      = ‖tangentTo axis a‖ * ‖tangentTo axis b‖ * Real.cos (sphAngle a axis b) := by
  have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (tangentTo axis a) (tangentTo axis b)
  rw [sphAngle]; linarith [h]

/-- The signed datum in sine form, valid for the convex orientation `0 ≤ sOrient a axis b`. -/
theorem sin_datum {axis a b : S2} (hka : ShortArc axis a) (hkb : ShortArc axis b)
    (hsupp : 0 ≤ sOrient a axis b) :
    sOrient a axis b
      = ‖tangentTo axis a‖ * ‖tangentTo axis b‖ * Real.sin (sphAngle a axis b) := by
  rw [← datum_eq_sOrient]; exact orientedDatum_sin_general hka hkb hsupp

set_option maxHeartbeats 1800000 in
/-- **Angle additivity.**  If `z` lies in the convex wedge (`0 ≤ sOrient prev axis z` and
`0 ≤ sOrient z axis next`), the strictly-oriented joint angle splits:
`sphAngle prev axis z + sphAngle z axis next = sphAngle prev axis next`. -/
theorem sphAngle_add_of_wedge {prev axis next z : S2}
    (hprev : ShortArc axis prev) (hnext : ShortArc axis next) (hz : ShortArc axis z)
    (hpos : 0 < sOrient prev axis next)
    (hzw1 : 0 ≤ sOrient prev axis z) (hzw2 : 0 ≤ sOrient z axis next) :
    sphAngle prev axis z + sphAngle z axis next = sphAngle prev axis next := by
  set tp := tangentTo axis prev with htp
  set tz := tangentTo axis z with htz
  set tn := tangentTo axis next with htn
  have hpnz : tp ≠ 0 := (tangentTo_ne_zero_iff axis prev).2 hprev
  have hznz : tz ≠ 0 := (tangentTo_ne_zero_iff axis z).2 hz
  have hnnz : tn ≠ 0 := (tangentTo_ne_zero_iff axis next).2 hnext
  have hpp : (0:ℝ) < ‖tp‖ := norm_pos_iff.2 hpnz
  have hzp : (0:ℝ) < ‖tz‖ := norm_pos_iff.2 hznz
  have hnp : (0:ℝ) < ‖tn‖ := norm_pos_iff.2 hnnz
  set α := sphAngle prev axis next with hαdef
  set β := sphAngle prev axis z with hβdef
  set γ := sphAngle z axis next with hγdef
  have hα0 : 0 < α := by
    rw [hαdef]; exact sphAngle_pos_of_det3_ne prev axis next (ne_of_gt hpos)
  have hαπ : α < Real.pi := by
    rw [hαdef]; exact sphAngle_lt_pi_of_det3_ne prev axis next (ne_of_gt hpos)
  have hβ0 : 0 ≤ β := sphAngle_nonneg _ _ _
  have hβπ : β ≤ Real.pi := sphAngle_le_pi _ _ _
  have hγ0 : 0 ≤ γ := sphAngle_nonneg _ _ _
  have hγπ : γ ≤ Real.pi := sphAngle_le_pi _ _ _
  have hpa : (⟪tp, (axis:E3)⟫ : ℝ) = 0 := tangentTo_orthogonal axis prev
  have hza : (⟪tz, (axis:E3)⟫ : ℝ) = 0 := tangentTo_orthogonal axis z
  have hna : (⟪tn, (axis:E3)⟫ : ℝ) = 0 := tangentTo_orthogonal axis next
  have hSpn : sOrient prev axis next
      = ‖tp‖ * ‖tn‖ * Real.sin α := sin_datum hprev hnext (le_of_lt hpos)
  have hCpn : (⟪tp, tn⟫ : ℝ) = ‖tp‖ * ‖tn‖ * Real.cos α := cos_datum axis prev next
  have hSpz : sOrient prev axis z
      = ‖tp‖ * ‖tz‖ * Real.sin β := sin_datum hprev hz hzw1
  have hCpz : (⟪tp, tz⟫ : ℝ) = ‖tp‖ * ‖tz‖ * Real.cos β := cos_datum axis prev z
  have hSzn : sOrient z axis next
      = ‖tz‖ * ‖tn‖ * Real.sin γ := sin_datum hz hnext hzw2
  have hCzn : (⟪tz, tn⟫ : ℝ) = ‖tz‖ * ‖tn‖ * Real.cos γ := cos_datum axis z next
  have hDpn : (⟪tp, cross (axis:E3) tn⟫ : ℝ) = sOrient prev axis next := datum_eq_sOrient axis prev next
  have hDpz : (⟪tp, cross (axis:E3) tz⟫ : ℝ) = sOrient prev axis z := datum_eq_sOrient axis prev z
  have hDzn : (⟪tz, cross (axis:E3) tn⟫ : ℝ) = sOrient z axis next := datum_eq_sOrient axis z next
  have hzz : (⟪tz, tz⟫ : ℝ) = ‖tz‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  have hsine := plucker_sine_add (axis := (axis:E3)) (p := tp) (x := tz) (n := tn) hza
  have hcosine := plucker_cos_add (axis := (axis:E3)) (p := tp) (x := tz) (n := tn) axis.2 hza hna
  rw [hDpn, hDpz, hDzn, hSpn, hSpz, hSzn, hzz, hCpz, hCzn] at hsine
  rw [hDpz, hDzn, hCpn, hCpz, hCzn, hzz] at hcosine
  have hPZN : (0:ℝ) < ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ := by positivity
  have hsinα : Real.sin α = Real.sin (β + γ) := by
    rw [Real.sin_add]
    have : ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ * Real.sin α
        = ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ * (Real.sin β * Real.cos γ + Real.cos β * Real.sin γ) := by
      nlinarith [hsine]
    have h2 := mul_left_cancel₀ (ne_of_gt hPZN) this
    linarith [h2]
  have hcosα : Real.cos α = Real.cos (β + γ) := by
    rw [Real.cos_add]
    have : ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ * Real.cos α
        = ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ * (Real.cos β * Real.cos γ - Real.sin β * Real.sin γ) := by
      nlinarith [hcosine]
    have h2 := mul_left_cancel₀ (ne_of_gt hPZN) this
    linarith [h2]
  have hcosdiff : Real.cos (α - (β + γ)) = 1 := by
    rw [Real.cos_sub, hcosα, hsinα]
    have := Real.sin_sq_add_cos_sq (β + γ); nlinarith [this]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hlo : -(2 * Real.pi) < α - (β + γ) := by nlinarith [hα0, hαπ, hβ0, hγ0, hβπ, hγπ, hpi]
  have hhi : α - (β + γ) < 2 * Real.pi := by nlinarith [hα0, hαπ, hβ0, hγ0, hβπ, hγπ, hpi]
  have hzero : α - (β + γ) = 0 := (Real.cos_eq_one_iff_of_lt_of_lt hlo hhi).1 hcosdiff
  linarith [hzero]

set_option maxHeartbeats 1800000 in
/-- **Cosine of the subtended angle.**  For `x, y` on the same (nonnegative) side of `prev` at the
apex (`0 ≤ sOrient prev axis x`, `0 ≤ sOrient prev axis y`), with `prev` a short arc, the cosine of
`sphAngle x axis y` equals `cos (β_x - β_y)`, where `β_z = sphAngle prev axis z`. -/
theorem cos_sphAngle_sub {prev axis x y : S2}
    (hprev : ShortArc axis prev) (hx : ShortArc axis x) (hy : ShortArc axis y)
    (hxw1 : 0 ≤ sOrient prev axis x) (hyw1 : 0 ≤ sOrient prev axis y) :
    Real.cos (sphAngle x axis y)
      = Real.cos (sphAngle prev axis x - sphAngle prev axis y) := by
  set tp := tangentTo axis prev with htp
  set tx := tangentTo axis x with htx
  set ty := tangentTo axis y with hty
  have hpnz : tp ≠ 0 := (tangentTo_ne_zero_iff axis prev).2 hprev
  have hxnz : tx ≠ 0 := (tangentTo_ne_zero_iff axis x).2 hx
  have hynz : ty ≠ 0 := (tangentTo_ne_zero_iff axis y).2 hy
  have hpp : (0:ℝ) < ‖tp‖ := norm_pos_iff.2 hpnz
  have hxp : (0:ℝ) < ‖tx‖ := norm_pos_iff.2 hxnz
  have hyp : (0:ℝ) < ‖ty‖ := norm_pos_iff.2 hynz
  set βx := sphAngle prev axis x with hβx
  set βy := sphAngle prev axis y with hβy
  have hpa : (⟪tp, (axis:E3)⟫ : ℝ) = 0 := tangentTo_orthogonal axis prev
  have hcosine := plucker_cos_add (axis := (axis:E3)) (p := tx) (x := tp) (n := ty) axis.2 hpa
    (tangentTo_orthogonal axis y)
  have hpp2 : (⟪tp, tp⟫ : ℝ) = ‖tp‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  have hCxp : (⟪tx, tp⟫ : ℝ) = ‖tx‖ * ‖tp‖ * Real.cos βx := by
    rw [cos_datum axis x prev, hβx, sphAngle_comm prev axis x]
  have hCpy : (⟪tp, ty⟫ : ℝ) = ‖tp‖ * ‖ty‖ * Real.cos βy := by
    rw [cos_datum axis prev y, hβy]
  have hCxy : (⟪tx, ty⟫ : ℝ) = ‖tx‖ * ‖ty‖ * Real.cos (sphAngle x axis y) := cos_datum axis x y
  have hSxp : (⟪tx, cross (axis:E3) tp⟫ : ℝ) = -(‖tp‖ * ‖tx‖ * Real.sin βx) := by
    rw [datum_eq_sOrient axis x prev]
    have hswap : sOrient x axis prev = -sOrient prev axis x := by
      simp only [sOrient, det3]; ring
    rw [hswap, sin_datum hprev hx hxw1, hβx]
  have hSpy : (⟪tp, cross (axis:E3) ty⟫ : ℝ) = ‖tp‖ * ‖ty‖ * Real.sin βy := by
    rw [datum_eq_sOrient axis prev y, sin_datum hprev hy hyw1, hβy]
  rw [hpp2, hCxp, hCpy, hCxy, hSxp, hSpy] at hcosine
  rw [Real.cos_sub]
  have hP : (0:ℝ) < ‖tp‖ ^ 2 * (‖tx‖ * ‖ty‖) := by positivity
  have : ‖tp‖ ^ 2 * (‖tx‖ * ‖ty‖) * Real.cos (sphAngle x axis y)
      = ‖tp‖ ^ 2 * (‖tx‖ * ‖ty‖) * (Real.cos βx * Real.cos βy + Real.sin βx * Real.sin βy) := by
    nlinarith [hcosine]
  exact mul_left_cancel₀ (ne_of_gt hP) this

set_option maxHeartbeats 1800000 in
/-- **The apex-wedge angle cap (hard core).**  If `prev, axis, next` is a strictly-oriented joint
(`0 < sOrient prev axis next`, opening `α = sphAngle prev axis next ∈ (0,π)`), and `x, y` both lie in
the convex wedge between `prev` and `next` at the apex `axis`, then the subtended angle is at most the
opening: `sphAngle x axis y ≤ sphAngle prev axis next`. -/
theorem sphAngle_le_of_in_apex_wedge {prev axis next x y : S2}
    (hprev : ShortArc axis prev) (hnext : ShortArc axis next)
    (hx : ShortArc axis x) (hy : ShortArc axis y)
    (hpos : 0 < sOrient prev axis next)
    (hxw1 : 0 ≤ sOrient prev axis x) (hxw2 : 0 ≤ sOrient x axis next)
    (hyw1 : 0 ≤ sOrient prev axis y) (hyw2 : 0 ≤ sOrient y axis next) :
    sphAngle x axis y ≤ sphAngle prev axis next := by
  set α := sphAngle prev axis next with hαdef
  have hxadd := sphAngle_add_of_wedge hprev hnext hx hpos hxw1 hxw2
  have hyadd := sphAngle_add_of_wedge hprev hnext hy hpos hyw1 hyw2
  set βx := sphAngle prev axis x with hβx
  set βy := sphAngle prev axis y with hβy
  set γx := sphAngle x axis next with hγx
  set γy := sphAngle y axis next with hγy
  have hα0 : 0 < α := by
    rw [hαdef]; exact sphAngle_pos_of_det3_ne prev axis next (ne_of_gt hpos)
  have hαπ : α < Real.pi := by
    rw [hαdef]; exact sphAngle_lt_pi_of_det3_ne prev axis next (ne_of_gt hpos)
  have hβx0 : 0 ≤ βx := sphAngle_nonneg _ _ _
  have hβy0 : 0 ≤ βy := sphAngle_nonneg _ _ _
  have hγx0 : 0 ≤ γx := sphAngle_nonneg _ _ _
  have hγy0 : 0 ≤ γy := sphAngle_nonneg _ _ _
  have hβxα : βx ≤ α := by have := hxadd; rw [← hαdef] at this; linarith
  have hβyα : βy ≤ α := by have := hyadd; rw [← hαdef] at this; linarith
  have hcoseq : Real.cos (sphAngle x axis y) = Real.cos (βx - βy) :=
    cos_sphAngle_sub hprev hx hy hxw1 hyw1
  have hcoslb : Real.cos α ≤ Real.cos (βx - βy) := by
    by_cases hcase : βy ≤ βx
    · have h1 : 0 ≤ βx - βy := by linarith
      have h2 : βx - βy ≤ α := by linarith
      exact Real.cos_le_cos_of_nonneg_of_le_pi h1 (le_of_lt hαπ) h2
    · push_neg at hcase
      have h1 : 0 ≤ βy - βx := by linarith
      have h2 : βy - βx ≤ α := by linarith
      have hk := Real.cos_le_cos_of_nonneg_of_le_pi h1 (le_of_lt hαπ) h2
      rw [show βx - βy = -(βy - βx) from by ring, Real.cos_neg]; exact hk
  have hxyπ : sphAngle x axis y ≤ Real.pi := sphAngle_le_pi _ _ _
  have hcoslb2 : Real.cos α ≤ Real.cos (sphAngle x axis y) := by rw [hcoseq]; exact hcoslb
  by_contra hcon
  push_neg at hcon
  have hlt : Real.cos (sphAngle x axis y) < Real.cos α :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hα0) hxyπ hcon
  linarith [hcoslb2, hlt]

/-- For a strict convex arm, `A i = A j` (`i ≠ j`) is impossible. -/
theorem arm_index_ne {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {i j : Fin (n + 1)} (hij : i ≠ j) : A i ≠ A j := by
  have hcyc : ProofsInTheBook.SphericalCyclicTriple.CyclicTriplePos (n := n + 1) A :=
    ProofsInTheBook.PlanarConvexDiag.cyclicTriplePos_unconditional hA.closed_convex
  have hn2 : 2 ≤ n := hA.two_le
  intro heq
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin (n + 1), k ≠ i ∧ k ≠ j := by
    by_contra h; push_neg at h
    have hsub : (Finset.univ : Finset (Fin (n + 1))) ⊆ {i, j} := by
      intro m _; simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hm : m = i
      · exact Or.inl hm
      · exact Or.inr (h m hm)
    have hcard : (Finset.univ : Finset (Fin (n + 1))).card ≤ 2 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
    rw [Finset.card_univ, Fintype.card_fin] at hcard; omega
  have key : ∀ a b c : Fin (n + 1), a < b → b < c → A a = A b ∨ A a = A c ∨ A b = A c → False := by
    intro a b c hab hbc hrep
    have hp := hcyc a b c hab hbc
    have hz : sOrient (A a) (A b) (A c) = 0 := by
      rcases hrep with h | h | h <;> · simp only [sOrient, det3, h]; ring
    linarith [hp, hz]
  rcases lt_trichotomy i j with hij1 | hij1 | hij1
  · rcases lt_trichotomy k i with hk1 | hk1 | hk1
    · exact key k i j hk1 hij1 (Or.inr (Or.inr heq))
    · exact hki hk1
    · rcases lt_trichotomy k j with hk2 | hk2 | hk2
      · exact key i k j hk1 hk2 (Or.inr (Or.inl heq))
      · exact hkj hk2
      · exact key i j k hij1 hk2 (Or.inl heq)
  · exact hij hij1
  · rcases lt_trichotomy k j with hk1 | hk1 | hk1
    · exact key k j i hk1 hij1 (Or.inr (Or.inr heq.symm))
    · exact hkj hk1
    · rcases lt_trichotomy k i with hk2 | hk2 | hk2
      · exact key j k i hk1 hk2 (Or.inr (Or.inl heq.symm))
      · exact hki hk2
      · exact key j i k hij1 hk2 (Or.inl heq.symm)

/-- Any two distinct-index vertices of a strict convex arm form a short arc. -/
theorem arm_shortArc {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {i j : Fin (n + 1)} (hij : i ≠ j) : ShortArc (A i) (A j) := by
  obtain ⟨_hvec, _hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  exact ⟨arm_index_ne hA hij, hemisphere_nonAntipodal hhem i j⟩

/-- **Lemma A — apex tangent-cone monotonicity (strict arm).**  On a strictly convex spherical arm `A`,
for `r < K < s` the chord `A r — A s` is seen from the interior vertex `A K` under an angle no larger than
the local joint angle at `A K`: `sphAngle (A r)(A K)(A s) ≤ sphAngle (A (K-1))(A K)(A (K+1))`.  Pure
original-arm fact: `A r`, `A s` both lie in the apex wedge spanned by `A (K-1)`, `A (K+1)` (four direct
edge supports of `A`), and the unoriented angle subtended within a wedge of opening `< π` is at most the
wedge opening. -/
theorem strictConvex_apex_angle_le_joint {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {K r s : ℕ}
    (hK0 : 1 ≤ K) (hKn : K < n) (hrK : r < K) (hKs : K < s) (hsn : s < n + 1) :
    sphAngle (A ⟨r, by omega⟩) (A ⟨K, by omega⟩) (A ⟨s, hsn⟩)
      ≤ sphAngle (A ⟨K - 1, by omega⟩) (A ⟨K, by omega⟩) (A ⟨K + 1, by omega⟩) := by
  set Km : Fin (n + 1) := ⟨K-1, by omega⟩ with hKm
  set Ka : Fin (n + 1) := ⟨K, by omega⟩ with hKa
  set Kp : Fin (n + 1) := ⟨K+1, by omega⟩ with hKp
  set R : Fin (n + 1) := ⟨r, by omega⟩ with hR
  set S : Fin (n + 1) := ⟨s, hsn⟩ with hS
  have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    simp only [Fin.val_one']; rw [Nat.mod_eq_of_lt (by omega)]
  have add_one : ∀ m : ℕ, (hm : m + 1 < n + 1) →
      ((⟨m, by omega⟩ : Fin (n + 1)) + 1) = (⟨m + 1, hm⟩ : Fin (n + 1)) := by
    intro m hm; apply Fin.ext
    rw [Fin.val_add, h1v, Fin.val_mk, Nat.mod_eq_of_lt hm]
  have hpos : 0 < sOrient (A Km) (A Ka) (A Kp) := by
    have hlt0 : Km < Ka := Fin.mk_lt_mk.mpr (by omega)
    have hlt1 : Ka < Kp := Fin.mk_lt_mk.mpr (by omega)
    exact cut_diagonal_supports hA.closed_convex hlt0 hlt1
  have hneKm : Ka ≠ Km := by rw [hKa, hKm, Ne, Fin.mk.injEq]; omega
  have hneKp : Ka ≠ Kp := by rw [hKa, hKp, Ne, Fin.mk.injEq]; omega
  have hneR : Ka ≠ R := by rw [hKa, hR, Ne, Fin.mk.injEq]; omega
  have hneS : Ka ≠ S := by rw [hKa, hS, Ne, Fin.mk.injEq]; omega
  have hprev : ShortArc (A Ka) (A Km) := arm_shortArc hA hneKm
  have hnext : ShortArc (A Ka) (A Kp) := arm_shortArc hA hneKp
  have hx : ShortArc (A Ka) (A R) := arm_shortArc hA hneR
  have hy : ShortArc (A Ka) (A S) := arm_shortArc hA hneS
  have hKmKa : (Km + 1 : Fin (n + 1)) = Ka := by
    rw [hKm, add_one (K-1) (by omega), hKa, Fin.mk.injEq]; omega
  have hKaKp : (Ka + 1 : Fin (n + 1)) = Kp := by rw [hKa, add_one K (by omega)]
  have hxw1 : 0 ≤ sOrient (A Km) (A Ka) (A R) := by
    have := hA.closed_convex.edge_support Km R; rw [hKmKa] at this; exact this
  have hxw2 : 0 ≤ sOrient (A R) (A Ka) (A Kp) := by
    have h := hA.closed_convex.edge_support Ka R; rw [hKaKp] at h
    rw [sOrient_cyclic (A R) (A Ka) (A Kp)]; exact h
  have hyw1 : 0 ≤ sOrient (A Km) (A Ka) (A S) := by
    have := hA.closed_convex.edge_support Km S; rw [hKmKa] at this; exact this
  have hyw2 : 0 ≤ sOrient (A S) (A Ka) (A Kp) := by
    have h := hA.closed_convex.edge_support Ka S; rw [hKaKp] at h
    rw [sOrient_cyclic (A S) (A Ka) (A Kp)]; exact h
  exact sphAngle_le_of_in_apex_wedge hprev hnext hx hy hpos hxw1 hxw2 hyw1 hyw2

/-- **Lemma B — the adjacent opened edge support caps the joint.**  At the WBS opening supremum the opened
adjacent triple `(K-1, K, K+1)` is a genuine edge support of the opened arm
(`0 ≤ sOrient (P (K-1))(P K)(P (K+1))` with `P (K-1) = A (K-1)`, `P K = A K`,
`P (K+1) = rotS2 (A K)(-δ*)(A (K+1))`), so by `angle_cap_of_rotated_support_nonneg`
`δ* + sphAngle (A (K-1))(A K)(A (K+1)) ≤ π`. -/
theorem joint_cap_of_opened_adjacent_support {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B) (k : Fin (n - 1))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k
        + sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) ≤ Real.pi := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hk := k.isLt
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  set K : Fin (n + 1) := openingAxis k with hKdef
  set δ : ℝ := monitoredSupWBS A B k with hδdef
  have hKval : K.val = k.val + 1 := by rw [hKdef]; rfl
  -- strict consecutive support 0 < sOrient(jointPrev, A K, jointNext) (defeq to the A⟨·⟩ form)
  have hlt0 : (⟨k.val, by omega⟩ : Fin (n + 1)) < ⟨k.val + 1, by omega⟩ :=
    Fin.mk_lt_mk.mpr (by omega)
  have hlt1 : (⟨k.val + 1, by omega⟩ : Fin (n + 1)) < ⟨k.val + 2, by omega⟩ :=
    Fin.mk_lt_mk.mpr (by omega)
  have hstrict : 0 < sOrient (jointPrev A k) (A K) (jointNext A k) :=
    cut_diagonal_supports hA.closed_convex hlt0 hlt1
  -- weak convexity of opened arm; the adjacent edge support
  have hwrapArc : ShortArc (openTail A K (-δ) (Fin.last n)) (openTail A K (-δ) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openTail A K (-δ)) :=
    supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrapArc
  have hidx : (⟨k.val, by omega⟩ : Fin (n + 1)) + 1 = K := by
    rw [hKdef]; ext; simp [Fin.add_def, openingAxis]; omega
  have hwc0 := hPweak.closed_convex.edge_support ⟨k.val, by omega⟩ ⟨k.val + 2, by omega⟩
  rw [hidx] at hwc0
  have hkle : k.val ≤ K.val := by omega
  have hklt : K.val < k.val + 2 := by omega
  have hPprev : openTail A K (-δ) ⟨k.val, by omega⟩ = A ⟨k.val, by omega⟩ :=
    openTail_fixed A K (-δ) (r := ⟨k.val, by omega⟩) hkle
  have hPK : openTail A K (-δ) K = A K := openTail_fixed A K (-δ) (r := K) (le_refl K.val)
  have hPnext : openTail A K (-δ) ⟨k.val + 2, by omega⟩
      = rotS2 (A K) (-δ) (A ⟨k.val + 2, by omega⟩) :=
    openTail_rot A K (-δ) (r := ⟨k.val + 2, by omega⟩) hklt
  rw [hPprev, hPK, hPnext] at hwc0
  have hδ0 : 0 ≤ δ := (monitoredSupWBS_mem_Icc hA hka hkt hkdef).1
  have hδπ : δ ≤ Real.pi := le_of_lt (monitoredSupWBS_lt_pi hA hB hka hkt hkdef)
  exact angle_cap_of_rotated_support_nonneg hka hkt hstrict hδ0 hδπ hwc0

/-- **The subarm angle cap.**  At the WBS opening supremum, the subarm base angle `sphAngle (A r)(A K)(A s)`
(`r < K < s`) together with the opening `δ* = monitoredSupWBS` satisfies `δ* + sphAngle (A r)(A K)(A s) ≤ π`.
This is the cap `endpt_openTail_interior_mono` needs on the strict subarm.  Proof: Lemma A bounds the subarm
base angle by the local joint angle `sphAngle (A (K-1))(A K)(A (K+1))` (pure strict-arm tangent cone), and
Lemma B caps `δ* +` that joint angle by `π` (the adjacent opened *edge* support); combine by `linarith`.
This avoids the false weak planar diagonal entirely. -/
theorem openedWBS_subarm_angle_cap {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B) (k : Fin (n - 1))
    (hkdef : jointAngle A k < jointAngle B k)
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (hrK : r < (openingAxis k).val) (hKs : (openingAxis k).val < s) :
    monitoredSupWBS A B k
        + sphAngle (A ⟨r, hr⟩) (A (openingAxis k)) (A ⟨s, hs⟩) ≤ Real.pi := by
  have hk := k.isLt
  have hKval : (openingAxis k).val = k.val + 1 := rfl
  have hKn : k.val + 1 < n := by omega
  -- Lemma B: the joint cap.
  have hjoint := joint_cap_of_opened_adjacent_support hA hB k hkdef
  -- Lemma A: subarm base angle ≤ local joint angle (defeq to the jointPrev/openingAxis/jointNext form).
  have hangle :
      sphAngle (A ⟨r, hr⟩) (A (openingAxis k)) (A ⟨s, hs⟩)
        ≤ sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) :=
    strictConvex_apex_angle_le_joint hA (K := k.val + 1) (r := r) (s := s)
      (by omega) hKn hrK hKs hs
  linarith [hangle, hjoint]



/-- The genuine subarm-induction residue: with the IH `MainPlusNR` for all smaller dimensions,
a proper cross collision whose opening axis is strictly interior to the pair (`r < K < s`) and
with positive opening (`0 < δ*`) is impossible.  This is the weak-target / limit core. -/
def SubarmIHContra : Prop :=
  ∀ {n : ℕ}, (∀ m : ℕ, m < n → MainPlusNR m) →
    ∀ (A B : Fin (n + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k → SupportStuckWBS A B k →
        ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
          r + 2 ≤ s →
          r < (openingAxis k).val → (openingAxis k).val < s →
          (0 < r ∨ s < n) →
          0 < monitoredSupWBS A B k →
          openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩ → False

/-- **The subarm-induction residue is discharged (limit-free, no IH).**  A proper cross collision with
strictly interior axis (`r < K < s`) and positive opening is impossible: the strict subarm `A[r..s]`
opened at its interior axis `K-r` by `-δ*` has, by `endpt_openTail_interior_mono` (cap from
`openedWBS_subarm_angle_cap`), endpoint `≥ sDist (A r)(A s) > 0` (strict no-repeat, `r + 2 ≤ s`); but the
collision makes the opened subarm endpoints coincide (`openedWBS r = openedWBS s`), forcing endpoint `0`.
Contradiction.  Note the IH `ihdim` is not used. -/
theorem subarmIHContra_holds : SubarmIHContra := by
  intro n _ihdim A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs _hproper hδpos heq
  set K : Fin (n + 1) := openingAxis k with hKdef
  set δ : ℝ := monitoredSupWBS A B k with hδdef
  have hsn : s ≤ n := by omega
  set m : ℕ := s - r with hm
  have hm2 : 2 ≤ m := by omega
  have hbnd : r + m ≤ n := by omega
  set Aint : Fin (m + 1) → S2 := intervalArm A r m hbnd with hAint_def
  have hAint : StrictConvexSphArm Aint := strictConvex_subarm hA hm2 hbnd
  set Kint : Fin (m + 1) := ⟨K.val - r, by omega⟩ with hKint_def
  have hKint0 : 1 ≤ Kint.val := by simp only [hKint_def]; omega
  have hKintm : Kint.val < m := by simp only [hKint_def]; omega
  -- vertex identifications
  have eAint0 : Aint 0 = A ⟨r, hr⟩ := by
    simp only [hAint_def, intervalArm]
    exact congrArg A (Fin.ext (by simp))
  have eAintK : Aint Kint = A K := by
    simp only [hAint_def, intervalArm]
    exact congrArg A (Fin.ext (by simp only [hKint_def]; omega))
  have eAintLast : Aint (Fin.last m) = A ⟨s, hs⟩ := by
    simp only [hAint_def, intervalArm]
    exact congrArg A (Fin.ext (by simp only [Fin.val_last]; omega))
  -- the cap on the subarm
  have hcap : δ + sphAngle (Aint 0) (Aint Kint) (Aint (Fin.last m)) ≤ Real.pi := by
    rw [eAint0, eAintK, eAintLast]
    exact openedWBS_subarm_angle_cap hA hB k hkdef hr hs hrK hKs
  -- interior-axis endpoint monotonicity on the strict subarm
  have hmono : endpt Aint ≤ endpt (openTail Aint Kint (-δ)) :=
    endpt_openTail_interior_mono hAint hKint0 hKintm (le_of_lt hδpos) hcap
  -- the opened subarm endpoints are the colliding `openedWBS` vertices
  have hopen0 : openTail Aint Kint (-δ) 0 = openedWBS A B k ⟨r, hr⟩ := by
    rw [openTail_fixed Aint Kint (-δ) (r := 0) (Nat.zero_le _), eAint0]
    simp only [openedWBS, ← hδdef, ← hKdef]
    exact (openTail_fixed A K (-δ) (r := ⟨r, hr⟩) (le_of_lt hrK)).symm
  have hopenLast : openTail Aint Kint (-δ) (Fin.last m) = openedWBS A B k ⟨s, hs⟩ := by
    rw [openTail_rot Aint Kint (-δ) (r := Fin.last m) (by simp only [Fin.val_last]; exact hKintm),
      eAintK, eAintLast]
    simp only [openedWBS, ← hδdef, ← hKdef]
    exact (openTail_rot A K (-δ) (r := ⟨s, hs⟩) hKs).symm
  have htarget0 : endpt (openTail Aint Kint (-δ)) = 0 := by
    unfold endpt
    rw [hopen0, hopenLast, heq, sDist_eq_zero_iff]
  have hsource_pos : 0 < endpt Aint := by
    unfold endpt
    rw [eAint0, eAintLast]
    exact sDist_pos_of_ne (strictConvex_noNonadjacentRepeat hA r s hr hs (by omega))
  rw [htarget0] at hmono
  linarith [hsource_pos]



/-- WBS support-stuck endpoint dispatch with the cross-piece collision residue removed.
Collision-free branches reconstruct opened no-repeat locally (verbatim from v11); collision
branches are discharged inline (full closure / `δ = 0` / `r = K`), with the `r < K` case routed
to the subarm-induction residue `SubarmIHContra`. -/
theorem supportStuckWBS_endpoint_dispatch_at_level_nr_v12
    (hSub : SubarmIHContra)
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
    endpt (openedWBS A B k) ≤ endpt B := by
  by_cases hnocross :
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r ≤ (openingAxis k).val → (openingAxis k).val < s →
          openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩
  · obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
    have hwrapArc :
        ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
          (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
      openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
    have hPweak : WeakConvexSphArm (openedWBS A B k) := by
      unfold openedWBS
      exact supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrapArc
    have hPpos : PositiveJoints (openedWBS A B k) := by
      intro r
      unfold openedWBS
      exact (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef r).1
    have hedge := openedEdges_short_at_supWBS_of_wrap (A := A) (B := B) hA hwrapArc
    have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
    have hhem0 := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
    have hhem : ∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ) := by
      simpa [openedWBS] using hhem0
    have hside' : SameSides (openedWBS A B k) B := by
      intro r
      unfold openedWBS
      rw [openTail_preserves_sides A (openingAxis k) (-(monitoredSupWBS A B k)) r]
      exact hside r
    have hjointk : jointAngle (openedWBS A B k) k =
        openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) := by
      unfold openedWBS
      exact jointAngle_openTail_eq_openedInterior A k (-(monitoredSupWBS A B k))
    have hslack : openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) ≤ jointAngle B k :=
      openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
    have hangle' : JointLe (openedWBS A B k) B := by
      intro r
      by_cases hrk : r = k
      · rw [hrk, hjointk]
        exact hslack
      · unfold openedWBS
        rw [jointAngle_openTail_eq_of_ne A k (-(monitoredSupWBS A B k)) hrk]
        exact hangle r
    have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
      openedWBS_noNonadjacentRepeat_of_localNoCross A B hA hB hside hangle
        k hkdef hstuck hnocross
    have hprog : MirrorBoundaryZeroProgress (openedWBS A B k) B :=
      supportStuckWBS_boundaryProgress_of_noRepeat_firstStep A B hA hB hside hangle
        k hkdef hstuck hPweak hnr hhem
    exact endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
      bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
      hPweak hPpos hnr hB hside' hangle' hhem ihdim hprog
  · push Not at hnocross
    obtain ⟨r, s, hr, hs, hrs, hrK, hKs, heq⟩ := hnocross
    have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
    by_cases hfull : r = 0 ∧ s = n
    · -- full-arm closure: `endpt (openedWBS) = sDist self = 0 ≤ endpt B`.
      obtain ⟨hr0, hsn⟩ := hfull
      have e0 : (0 : Fin (n + 1)) = ⟨r, hr⟩ := Fin.ext (by simp [hr0])
      have en : (Fin.last n) = ⟨s, hs⟩ := Fin.ext (by simp [hsn])
      have hzero : endpt (openedWBS A B k) = 0 := by
        unfold endpt
        rw [e0, en, heq]
        unfold sDist sInner
        rw [S2.inner_self]
        exact Real.arccos_one
      rw [hzero]
      unfold endpt
      exact sDist_nonneg _ _
    · -- proper collision: derive `False`.
      exfalso
      have hproper : 0 < r ∨ s < n := by
        rcases Nat.eq_zero_or_pos r with hr0 | hrpos
        · refine Or.inr ?_
          rcases Nat.lt_or_ge s n with hlt | hge
          · exact hlt
          · exact absurd ⟨hr0, le_antisymm (by omega) hge⟩ hfull
        · exact Or.inl hrpos
      set δ : ℝ := monitoredSupWBS A B k with hδdef
      by_cases hδ0 : δ = 0
      · have hO : openedWBS A B k = A := by
          simp only [openedWBS, ← hδdef, hδ0, neg_zero]
          exact openTail_zero_angle A (openingAxis k)
        rw [hO] at heq
        exact hbase r s hr hs hrs heq
      · have hδpos : 0 < δ := lt_of_le_of_ne (hδdef ▸ (monitoredSupWBS_mem_Icc hA
          (shortArcs_of_strict hA k).1 (shortArcs_of_strict hA k).2 hkdef).1) (Ne.symm hδ0)
        by_cases hrKeq : r = (openingAxis k).val
        · -- `r = K`: rigid rotation about `A K`; `heq` becomes `A K = A s`.
          have hrleK : r ≤ (openingAxis k).val := le_of_eq hrKeq
          have hrw_r : openedWBS A B k ⟨r, hr⟩ = A (openingAxis k) := by
            have h1 : openedWBS A B k ⟨r, hr⟩ = A ⟨r, hr⟩ := by
              simp only [openedWBS, ← hδdef]
              exact openTail_fixed A (openingAxis k) (-δ) hrleK
            rw [h1]
            congr 1
            exact Fin.ext (by simp [hrKeq])
          have hrw_s : openedWBS A B k ⟨s, hs⟩ = rotS2 (A (openingAxis k)) (-δ) (A ⟨s, hs⟩) := by
            simp only [openedWBS, ← hδdef]
            exact openTail_rot A (openingAxis k) (-δ) hKs
          rw [hrw_r, hrw_s] at heq
          have hzero : sDist (A (openingAxis k)) (A ⟨s, hs⟩) = 0 := by
            have hiso : sDist (A (openingAxis k)) (A ⟨s, hs⟩)
                = sDist (rotS2 (A (openingAxis k)) (-δ) (A (openingAxis k)))
                    (rotS2 (A (openingAxis k)) (-δ) (A ⟨s, hs⟩)) :=
              (sDist_rotS2 (A (openingAxis k)) (-δ) (A (openingAxis k)) (A ⟨s, hs⟩)).symm
            rw [hiso, rotS2_axis_fixed, ← heq, sDist_eq_zero_iff]
          have hKs2 : A (openingAxis k) = A ⟨s, hs⟩ := sDist_eq_zero_iff.mp hzero
          have hKlt : (openingAxis k).val + 2 ≤ s := by omega
          refine hbase (openingAxis k).val s (openingAxis k).isLt hs hKlt ?_
          rw [← hKs2]
        · -- `r < K`: the genuine subarm-induction residue.
          have hrK_lt : r < (openingAxis k).val := lt_of_le_of_ne hrK hrKeq
          exact hSub ihdim A B hA hB hside hangle k hkdef hstuck
            r s hr hs hrs hrK_lt hKs hproper hδpos heq



theorem open_step_wbs_nr_v12
    (hSub : SubarmIHContra)
    {n : ℕ} (_hn : 2 ≤ n) (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' → NoNonadjacentRepeat A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B := by
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA']; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hside' : SameSides A' B := by
    intro i; rw [hA', openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  have hmono : endpt A ≤ endpt A' := glueWBS_clause_i hA hka hkt hkdef
  by_cases hstuck : SupportStuckWBS A B k
  · have hAB0 : endpt (openedWBS A B k) ≤ endpt B :=
      supportStuckWBS_endpoint_dispatch_at_level_nr_v12 hSub ihdim
        A B hA hB hside hangle k hkdef hstuck
    have hAB : endpt A' ≤ endpt B := by
      rw [hA']
      exact hAB0
    exact le_trans hmono hAB
  · have hreach : ReachWBS A B k := by
      rcases glueWBS_clause_ii hA hB hka hkt hkdef hstuck with hr | hbase
      · exact hr
      · rcases BaseStuckProgressWBS_holds n A B hA hB k hkdef hbase with hr | hvan
        · exact hr
        · exfalso
          obtain ⟨i, j, hji, hji1, heq⟩ := hvan
          exact hstuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq⟩
    have hstrict : StrictConvexSphArm A' := by
      rw [hA']; exact reachWBS_strictConvex hA hB hka hkt hkdef hstuck
    have hreach_k : jointAngle A' k = jointAngle B k := by rw [hjointk]; exact hreach
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    have hAB : endpt A' ≤ endpt B :=
      ihdef A' B (strictConvexSphArm_toWeak hstrict)
        (strictConvexSphArm_positiveJoints hstrict) (strictConvex_noNonadjacentRepeat hstrict)
        hB hside' hangle' hdrop
    exact le_trans hmono hAB

theorem szOpeningStepPlusNR_v12
    (hSub : SubarmIHContra) :
    SZOpeningStepPlusNR := by
  intro n hn ihdim A B hA hposA hnrA hB hside hangle ihdef
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · exact weakPositiveCutReadyNR_v9_holds weakWrapSeed_v9_of_firstStep
      bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
      hA hposA hnrA hB hside hangle ihdim hvanish
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_wbs_nr_v12 hSub hn ihdim hAstrict hB hside hangle ihdef k hkdef

theorem mainPlusNR_at_level_v12
    (hSub : SubarmIHContra)
    {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m) : MainPlusNR n := by
  intro A B hA hposA hnrA hB hside hangle
  let hstep := szOpeningStepPlusNR_v12 hSub
  have hrec :
      ∀ d : ℕ, ∀ A B : Fin (n + 1) → S2,
        WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
        StrictConvexSphArm B → SameSides A B → JointLe A B →
        deficitCount A B = d → endpt A ≤ endpt B := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro A B hA hposA hnrA hB hside hangle hdef
      refine hstep n hn ihdim A B hA hposA hnrA hB hside hangle ?_
      intro A' B' hA' hposA' hnrA' hB' hside' hangle' hlt
      exact IH (deficitCount A' B') (hdef ▸ hlt) A' B' hA' hposA' hnrA'
        hB' hside' hangle' rfl
  exact hrec (deficitCount A B) A B hA hposA hnrA hB hside hangle rfl

theorem mainPlusNR_all_v12
    (hSub : SubarmIHContra) :
    ∀ n : ℕ, 2 ≤ n → MainPlusNR n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn A B hA hposA hnrA hB hside hangle
    have ihdim : ∀ m : ℕ, m < n → MainPlusNR m := by
      intro m hm
      rcases Nat.lt_or_ge m 2 with h2 | h2
      · exact mainPlusNR_of_lt_two h2
      · exact IH m hm h2
    exact mainPlusNR_at_level_v12 hSub hn ihdim
      A B hA hposA hnrA hB hside hangle

/-- Chapter-13 strict-arm monotonicity, with the cross-piece collision residue replaced by the
genuine subarm-induction residue `SubarmIHContra`. -/
theorem spherical_arm_mono_final_ch13_v12
    (hSub : SubarmIHContra) :
    SphericalArmMonotone := by
  intro n hn A B hA hB hside hangle
  exact (mainPlusNR_all_v12 hSub n hn) A B
    (strictConvexSphArm_toWeak hA) (strictConvexSphArm_positiveJoints hA)
    (strictConvex_noNonadjacentRepeat hA) hB hside hangle

/-- **Chapter-13 strict-arm monotonicity, UNCONDITIONAL.**  The subarm-induction residue `SubarmIHContra`
is discharged by `subarmIHContra_holds`, so the `v12` headline becomes unconditional: Chapter 13 closed. -/
theorem spherical_arm_mono_final_ch13 : SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v12 subarmIHContra_holds









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



/-- **Strict mirrored cosine bound.**  Companion of `cos_open_le_cos_orig_neg`: a *strict* opening
`0 < θ` (within the great-semicircle range, `θ + φ₀ < π`) and a strict oriented datum
`0 < ⟪tangentTo axis a0, axis × tangentTo axis tail⟫`... actually we only need the strict-angle
output, derived below. -/
theorem cos_open_lt_cos_orig_neg (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ))
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ + sphAngle a0 axis tail < Real.pi) :
    Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) < Real.cos (sphAngle a0 axis tail) := by
  set u := tangentTo axis a0 with hu
  set w := tangentTo axis tail with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (axis : E3) w⟫ with hsdef
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  set φ₀ : ℝ := sphAngle a0 axis tail with hφ
  have hcosopen : Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail))
      = (Real.cos (-θ) * c + Real.sin (-θ) * s) / N := by
    rw [cos_openedJointAngle, norm_tangentTo_open]
  have hcosorig : Real.cos φ₀ = c / N := by
    rw [hφ, sphAngle, InnerProductGeometry.cos_angle]
  have hφ0 : 0 ≤ φ₀ := sphAngle_nonneg _ _ _
  have hφπ : φ₀ ≤ Real.pi := sphAngle_le_pi _ _ _
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (axis : E3)) (u := u) (w := w) axis.2
      (tangentTo_orthogonal axis a0) (tangentTo_orthogonal axis tail)
    rw [hc, hsdef, hN]; rw [mul_pow]; linear_combination this
  have hcEq : c = N * Real.cos φ₀ := by
    rw [hcosorig]; field_simp
  have hsinφ : 0 ≤ Real.sin φ₀ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ
  have hssq : s ^ 2 = (N * Real.sin φ₀) ^ 2 := by
    have hsincos : Real.sin φ₀ ^ 2 = 1 - Real.cos φ₀ ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ₀; linarith
    rw [mul_pow, hsincos]
    have : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [this, hcEq]; ring
  have hsEq : s = N * Real.sin φ₀ := by
    have hge : 0 ≤ N * Real.sin φ₀ := mul_nonneg (le_of_lt hNp) hsinφ
    nlinarith [hssq, hsign, hge, sq_nonneg (s - N * Real.sin φ₀)]
  have hsinusoid : Real.cos (-θ) * c + Real.sin (-θ) * s = N * Real.cos (φ₀ + θ) := by
    rw [hcEq, hsEq, Real.cos_neg, Real.sin_neg, Real.cos_add]; ring
  rw [hcosopen, hcosorig, hsinusoid]
  rw [div_lt_div_iff_of_pos_right hNp]
  have hcos : Real.cos (φ₀ + θ) < Real.cos φ₀ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hφ0 (by linarith) (by linarith)
  rw [hcEq]
  exact mul_lt_mul_of_pos_left hcos hNp

/-- **Strict mirrored base-angle increase.**  Opening the joint at `axis` by `-θ` (`0 < θ`, strictly
within range) strictly increases the base angle, given the convex oriented datum. -/
theorem openedAngle_gt_of_oriented_neg (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ))
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ + sphAngle a0 axis tail < Real.pi) :
    sphAngle a0 axis tail < sphAngle a0 axis (rotS2 axis (-θ) tail) := by
  have hcos := cos_open_lt_cos_orig_neg axis a0 tail hka hkt hsign hθ0 hθπ
  by_contra hle
  rw [not_lt] at hle
  have : Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) ≥ Real.cos (sphAngle a0 axis tail) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hle
  linarith [hcos]



/-- **Interior-axis endpoint STRICT increase.**  For a strictly convex arm `A`, interior axis `K`
(`1 ≤ K.val`, `K.val < n`), opening the tail by `-θ` with `0 < θ` strictly within the great-semicircle
range strictly increases the arm endpoint. -/
theorem endpt_openTail_interior_strict {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} (hK0 : 1 ≤ K.val) (hKn : K.val < n) {θ : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ + sphAngle (A 0) (A K) (A (Fin.last n)) < Real.pi) :
    endpt A < endpt (openTail A K (-θ)) := by
  obtain ⟨hka, hkt⟩ := shortArc_interior_base hA hK0 hKn
  have hsign : (0 : ℝ) ≤
      (⟪tangentTo (A K) (A 0), cross (A K : E3) (tangentTo (A K) (A (Fin.last n)))⟫ : ℝ) :=
    orientedSign_neg_of_support (orientedDatum_interior hA hK0 hKn)
  have hangle : sphAngle (A 0) (A K) (A (Fin.last n))
      < sphAngle (A 0) (A K) (rotS2 (A K) (-θ) (A (Fin.last n))) :=
    openedAngle_gt_of_oriented_neg (A K) (A 0) (A (Fin.last n)) hka hkt hsign hθ0 hθπ
  have hstr : sDist (A 0) (A (Fin.last n))
      < sDist (A 0) (rotS2 (A K) (-θ) (A (Fin.last n))) :=
    reach_base_endpoint_strict (A K) (A 0) (A (Fin.last n)) hka hkt hangle
  rw [endpt_openTail_interior A (-θ) hK0 hKn]
  exact hstr



/-- Continuity of `tangentTo` of two `θ`-continuous unit-vector families. -/
theorem continuousAt_tangentTo_openTail {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (p q : Fin (n + 1)) (θ₀ : ℝ) :
    ContinuousAt (fun θ : ℝ => tangentTo (openTail A K θ p) (openTail A K θ q)) θ₀ := by
  have hp := (continuous_openTail_vec A K p).continuousAt (x := θ₀)
  have hq := (continuous_openTail_vec A K q).continuousAt (x := θ₀)
  have heq : (fun θ : ℝ => tangentTo (openTail A K θ p) (openTail A K θ q))
      = (fun θ : ℝ => ((openTail A K θ q : S2) : E3)
          - (⟪((openTail A K θ q : S2) : E3), ((openTail A K θ p : S2) : E3)⟫ : ℝ)
            • ((openTail A K θ p : S2) : E3)) := by
    funext θ; rw [tangentTo_eq]; rfl
  rw [heq]
  exact hq.sub ((hq.inner hp).smul hp)

/-- The generic `openTail` strict-convexity assembler (mirrors `reach_strictConvex_at_sup`). -/
theorem strictConvex_openTail_of_constraints {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {K : Fin (n + 1)} {θ : ℝ} {h : E3} (hnorm : ‖h‖ = 1)
    (hedge : ∀ i : Fin (n + 1), ShortArc (openTail A K θ i) (openTail A K θ (i + 1)))
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K θ i) (openTail A K θ (i + 1)) (openTail A K θ j))
    (hhem : ∀ k : Fin (n + 1), 0 < (⟪h, (openTail A K θ k : E3)⟫ : ℝ)) :
    StrictConvexSphArm (openTail A K θ) := by
  refine { two_le := hA.two_le, closed_convex := ?_ }
  refine { three_le := by have := hA.two_le; omega
           edge_short := hedge
           edge_support := ?_
           strict_nonincident := hmix
           open_hemisphere := ⟨h, hnorm, hhem⟩ }
  intro i j
  by_cases hji : j = i
  · subst hji; rw [sOrient, ProofsInTheBook.SphericalDiagCut.det3_self_right]
  · by_cases hji1 : j = i + 1
    · subst hji1; rw [sOrient, ProofsInTheBook.SphericalDiagCut.det3_self_mid]
    · exact le_of_lt (hmix i j hji hji1)

/-- **Strict convexity persistence for small opening.**  There is a `θ₀ > 0` such that for all `θ`
with `|θ| < θ₀`, `openTail A K θ` is a `StrictConvexSphArm`. -/
theorem strictConvex_openTail_of_small {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (K : Fin (n + 1)) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, |θ| < θ₀ → StrictConvexSphArm (openTail A K θ) := by
  classical
  obtain ⟨h, hnorm, hhpos0⟩ := hA.closed_convex.open_hemisphere
  -- at θ = 0, openTail A K 0 = A, so every constraint is strictly satisfied.
  have h0 : openTail A K 0 = A := openTail_zero_angle A K
  -- Build the conjunction of all (finitely many) strict constraints as an eventually-true statement.
  -- edge family: 0 < ‖tangentTo (P i)(P (i+1))‖
  have hedge_ev : ∀ i : Fin (n + 1),
      ∀ᶠ θ : ℝ in nhds 0,
        0 < ‖tangentTo (openTail A K θ i) (openTail A K θ (i + 1))‖ := by
    intro i
    have hcont : ContinuousAt
        (fun θ : ℝ => ‖tangentTo (openTail A K θ i) (openTail A K θ (i + 1))‖) 0 :=
      (continuousAt_tangentTo_openTail A K i (i + 1) 0).norm
    have hpos0 : 0 < ‖tangentTo (openTail A K 0 i) (openTail A K 0 (i + 1))‖ := by
      rw [h0]
      have hsa : ShortArc (A i) (A (i + 1)) := hA.closed_convex.edge_short i
      exact norm_pos_iff.2 ((tangentTo_ne_zero_iff _ _).2 hsa)
    exact continuousAt_const.eventually_lt hcont hpos0
  -- mixed support family
  have hmix_ev : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      ∀ᶠ θ : ℝ in nhds 0,
        0 < sOrient (openTail A K θ i) (openTail A K θ (i + 1)) (openTail A K θ j) := by
    intro i j hji hji1
    have hcont : ContinuousAt
        (fun θ : ℝ => sOrient (openTail A K θ i) (openTail A K θ (i + 1)) (openTail A K θ j)) 0 :=
      (continuous_interiorSupport A K (i, i + 1, j)).continuousAt
    have hpos0 : 0 < sOrient (openTail A K 0 i) (openTail A K 0 (i + 1)) (openTail A K 0 j) := by
      rw [h0]; exact hA.closed_convex.strict_nonincident i j hji hji1
    exact continuousAt_const.eventually_lt hcont hpos0
  -- hemisphere family
  have hhem_ev : ∀ k : Fin (n + 1),
      ∀ᶠ θ : ℝ in nhds 0, 0 < (⟪h, (openTail A K θ k : E3)⟫ : ℝ) := by
    intro k
    have hcont : ContinuousAt (fun θ : ℝ => (⟪h, (openTail A K θ k : E3)⟫ : ℝ)) 0 :=
      (continuous_const.inner (continuous_openTail_vec A K k)).continuousAt
    have hpos0 : 0 < (⟪h, (openTail A K 0 k : E3)⟫ : ℝ) := by rw [h0]; exact hhpos0 k
    exact continuousAt_const.eventually_lt hcont hpos0
  -- combine: all three finite families eventually hold together.
  have hmix_all : ∀ᶠ θ : ℝ in nhds 0,
      (∀ p : Fin (n + 1) × Fin (n + 1), p.2 ≠ p.1 → p.2 ≠ p.1 + 1 →
        0 < sOrient (openTail A K θ p.1) (openTail A K θ (p.1 + 1)) (openTail A K θ p.2)) := by
    refine Filter.eventually_all.2 ?_
    intro p
    by_cases hp1 : p.2 = p.1
    · exact Filter.Eventually.of_forall (fun θ hc => absurd hp1 hc)
    · by_cases hp2 : p.2 = p.1 + 1
      · exact Filter.Eventually.of_forall (fun θ _ hc => absurd hp2 hc)
      · exact (hmix_ev p.1 p.2 hp1 hp2).mono (fun θ hθ _ _ => hθ)
  have hall : ∀ᶠ θ : ℝ in nhds 0,
      (∀ i : Fin (n + 1), 0 < ‖tangentTo (openTail A K θ i) (openTail A K θ (i + 1))‖) ∧
      (∀ p : Fin (n + 1) × Fin (n + 1), p.2 ≠ p.1 → p.2 ≠ p.1 + 1 →
        0 < sOrient (openTail A K θ p.1) (openTail A K θ (p.1 + 1)) (openTail A K θ p.2)) ∧
      (∀ k : Fin (n + 1), 0 < (⟪h, (openTail A K θ k : E3)⟫ : ℝ)) :=
    ((Filter.eventually_all.2 hedge_ev).and hmix_all).and (Filter.eventually_all.2 hhem_ev) |>.mono
      (fun θ hθ => ⟨hθ.1.1, hθ.1.2, hθ.2⟩)
  -- extract a metric ball.
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨θ₀, hθ₀pos, hθ₀⟩ := hall
  refine ⟨θ₀, hθ₀pos, ?_⟩
  intro θ hθ
  have hdist : dist θ 0 < θ₀ := by rw [Real.dist_eq, sub_zero]; exact hθ
  obtain ⟨hE, hM, hH⟩ := hθ₀ hdist
  refine strictConvex_openTail_of_constraints hA hnorm ?_ ?_ hH
  · intro i; exact (tangentTo_ne_zero_iff _ _).1 (norm_pos_iff.1 (hE i))
  · intro i j hji hji1; exact hM (i, j) hji hji1



/-- **Joint-angle continuity at `θ₀`** when the two joint tangents are nonzero there. -/
theorem continuousAt_jointAngle_openTail {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i : Fin (n - 1)) (θ₀ : ℝ)
    (hp : tangentTo (openTail A K θ₀ ⟨i.val + 1, by have := i.isLt; omega⟩)
            (openTail A K θ₀ ⟨i.val, by have := i.isLt; omega⟩) ≠ 0)
    (hq : tangentTo (openTail A K θ₀ ⟨i.val + 1, by have := i.isLt; omega⟩)
            (openTail A K θ₀ ⟨i.val + 2, by have := i.isLt; omega⟩) ≠ 0) :
    ContinuousAt (fun θ : ℝ => jointAngle (openTail A K θ) i) θ₀ := by
  set a : Fin (n + 1) := ⟨i.val, by have := i.isLt; omega⟩
  set b : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; omega⟩
  set c : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; omega⟩
  have hangle :
      ContinuousAt (fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2)
        (tangentTo (openTail A K θ₀ b) (openTail A K θ₀ a),
          tangentTo (openTail A K θ₀ b) (openTail A K θ₀ c)) :=
    InnerProductGeometry.continuousAt_angle hp hq
  have hpair :
      ContinuousAt (fun θ : ℝ =>
        ((tangentTo (openTail A K θ b) (openTail A K θ a),
          tangentTo (openTail A K θ b) (openTail A K θ c)) : E3 × E3)) θ₀ :=
    (continuousAt_tangentTo_openTail A K b a θ₀).prodMk
      (continuousAt_tangentTo_openTail A K b c θ₀)
  have hcomp :
      ContinuousAt
        ((fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2) ∘
          (fun θ : ℝ =>
            ((tangentTo (openTail A K θ b) (openTail A K θ a),
              tangentTo (openTail A K θ b) (openTail A K θ c)) : E3 × E3))) θ₀ :=
    ContinuousAt.comp
      (g := fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2)
      (f := fun θ : ℝ =>
        ((tangentTo (openTail A K θ b) (openTail A K θ a),
          tangentTo (openTail A K θ b) (openTail A K θ c)) : E3 × E3))
      hangle hpair
  have heq : (fun θ : ℝ => jointAngle (openTail A K θ) i)
      = ((fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2) ∘
          (fun θ : ℝ =>
            ((tangentTo (openTail A K θ b) (openTail A K θ a),
              tangentTo (openTail A K θ b) (openTail A K θ c)) : E3 × E3))) := by
    funext θ; rfl
  rw [heq]; exact hcomp



theorem stuckWitnessExists_holds : StuckWitnessExists := by
  intro n hn A B hA hB hside hangle _ih hwider
  -- We always take the right disjunct `endpt A < endpt B`.
  refine Or.inr ?_
  obtain ⟨i₀, hi₀⟩ := hwider
  -- the opening axis = apex of the deficient joint i₀.
  set K : Fin (n + 1 + 1) := openingAxis i₀ with hK
  obtain ⟨hK0, hKn⟩ := ProofsInTheBook.SphericalOpeningOutcome.openingAxis_interior i₀
  -- base angle is strictly below π, so there is room to open.
  have hbaseπ : sphAngle (A 0) (A K) (A (Fin.last (n + 1))) < Real.pi :=
    ProofsInTheBook.ZinanFFCT41.base_sphAngle_lt_pi hA i₀
  -- §3: strict convexity persists on |θ| < θc.
  obtain ⟨θc, hθcpos, hθc⟩ := strictConvex_openTail_of_small hA K
  -- §4: joint i₀ stays < B's joint i₀ on a neighbourhood of 0.
  have hjcont : ContinuousAt (fun θ : ℝ => jointAngle (openTail A K θ) i₀) 0 := by
    have h0 : openTail A K 0 = A := openTail_zero_angle A K
    refine continuousAt_jointAngle_openTail A K i₀ 0 ?_ ?_
    · rw [h0]
      have hsa : ShortArc (A ⟨i₀.val + 1, by have := i₀.isLt; omega⟩)
          (A ⟨i₀.val, by have := i₀.isLt; omega⟩) := by
        have := hA.closed_convex.edge_short ⟨i₀.val, by have := i₀.isLt; omega⟩
        -- edge from ⟨i₀⟩ to ⟨i₀+1⟩ is a short arc; symmetrize.
        have hsucc : (⟨i₀.val, by have := i₀.isLt; omega⟩ + 1 : Fin (n + 1 + 1))
            = ⟨i₀.val + 1, by have := i₀.isLt; omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_add, Fin.val_one]
          rw [Nat.mod_eq_of_lt (by have := i₀.isLt; omega)]
        rw [hsucc] at this; exact this.symm
      exact (tangentTo_ne_zero_iff _ _).2 hsa
    · rw [h0]
      have hsa : ShortArc (A ⟨i₀.val + 1, by have := i₀.isLt; omega⟩)
          (A ⟨i₀.val + 2, by have := i₀.isLt; omega⟩) := by
        have := hA.closed_convex.edge_short ⟨i₀.val + 1, by have := i₀.isLt; omega⟩
        have hsucc : (⟨i₀.val + 1, by have := i₀.isLt; omega⟩ + 1 : Fin (n + 1 + 1))
            = ⟨i₀.val + 2, by have := i₀.isLt; omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_add, Fin.val_one]
          rw [Nat.mod_eq_of_lt (by have := i₀.isLt; omega)]
        rw [hsucc] at this; exact this
      exact (tangentTo_ne_zero_iff _ _).2 hsa
  have hjev : ∀ᶠ θ : ℝ in nhds 0, jointAngle (openTail A K θ) i₀ < jointAngle B i₀ := by
    have hval0 : (fun θ : ℝ => jointAngle (openTail A K θ) i₀) 0 < jointAngle B i₀ := by
      simp only [openTail_zero_angle]; exact hi₀
    exact hjcont.eventually_lt continuousAt_const hval0
  rw [Metric.eventually_nhds_iff] at hjev
  obtain ⟨θj, hθjpos, hθj⟩ := hjev
  -- choose θ small enough (strictly) for: convexity, joint slack, and angle range.
  have hπgap : 0 < Real.pi - sphAngle (A 0) (A K) (A (Fin.last (n + 1))) := by linarith
  set m : ℝ := min (min θc θj) (Real.pi - sphAngle (A 0) (A K) (A (Fin.last (n + 1)))) with hm
  have hmpos : 0 < m := lt_min (lt_min hθcpos hθjpos) hπgap
  set θ : ℝ := m / 2 with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; linarith
  have hθm : θ < m := by rw [hθdef]; linarith
  have hθ_c : θ < θc := lt_of_lt_of_le hθm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθ_j : θ < θj := lt_of_lt_of_le hθm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hθ_π : θ + sphAngle (A 0) (A K) (A (Fin.last (n + 1))) < Real.pi := by
    have : θ < Real.pi - sphAngle (A 0) (A K) (A (Fin.last (n + 1))) :=
      lt_of_lt_of_le hθm (min_le_right _ _)
    linarith
  -- the opened arm at -θ.
  have habs : |(-θ)| < θc := by rw [abs_neg, abs_of_pos hθpos]; exact hθ_c
  have hAsharp : StrictConvexSphArm (openTail A K (-θ)) := hθc (-θ) habs
  -- (1) strict endpoint increase.
  have hendpt_str : endpt A < endpt (openTail A K (-θ)) :=
    endpt_openTail_interior_strict hA hK0 hKn hθpos hθ_π
  -- (2) the opened arm has the same sides as B.
  have hside' : ∀ i : Fin (n + 1), sideLen (openTail A K (-θ)) i = sideLen B i := by
    intro i; rw [openTail_preserves_sides A K (-θ) i]; exact hside i
  -- (3) the opened arm has joints ≤ B.
  have hangle' : ∀ i : Fin (n + 1 - 1), jointAngle (openTail A K (-θ)) i ≤ jointAngle B i := by
    intro i
    by_cases hii : i = i₀
    · subst hii
      have hdist : dist (-θ) 0 < θj := by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hθpos]; exact hθ_j
      exact le_of_lt (hθj hdist)
    · rw [jointAngle_openTail_eq_of_ne A i₀ (-θ) hii]; exact hangle i
  -- (4) the unconditional weak arm lemma at level n+1.
  have hweak : endpt (openTail A K (-θ)) ≤ endpt B := by
    have := spherical_arm_mono_final_ch13 (n := n + 1) (by omega)
      (openTail A K (-θ)) B hAsharp hB hside' hangle'
    simpa [endpt] using this
  exact lt_of_lt_of_le hendpt_str hweak





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



/-- **The strict arm lemma, surfaced as a clean top-level statement** (conditional on the single
residue).  Companion to the unconditional `≤` headline `spherical_arm_mono_final_ch13`. -/
theorem spherical_arm_mono_strict_of_residue (h : StuckWitnessExists)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  armMono_strict_of_stuckWitness h hn A B hA hB hside hangle hstrict



/-- **The strict spherical arm lemma — UNCONDITIONAL.**  Equal-sided strictly convex spherical arms
with nondecreasing joints and SOME joint strictly wider have a strictly longer endpoint chord.
Companion to the unconditional `≤` headline `spherical_arm_mono_final_ch13`. -/
theorem spherical_arm_mono_strict_uncond
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_of_residue ProofsInTheBook.ZinanFFCT113.stuckWitnessExists_holds
    hn A B hA hB hside hangle hstrict



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

/-- Edge signs in Cauchy's rigidity proof. -/
inductive EdgeSign where
  | plus | minus | zero
  deriving DecidableEq, Repr

open EdgeSign

/-- The nonzero signs left after Cauchy's proof discards unchanged edges. -/
inductive StrictEdgeSign where
  | plus | minus
  deriving DecidableEq, Repr

/-- Forget zero signs and keep only genuine increases/decreases. -/
def EdgeSign.toStrict : EdgeSign → Option StrictEdgeSign
  | plus => some StrictEdgeSign.plus
  | minus => some StrictEdgeSign.minus
  | zero => none



















namespace StrictTriangleSigns





end StrictTriangleSigns















/--
The concrete GEOMETRIC data for the opening direction of Cauchy's arm lemma at a vertex link while the
endpoint chord is fixed by congruent faces: two equal-sided strictly convex spherical arms whose joints
are nondecreasing (some strictly wider) yet share the same endpoint chord.  Such a configuration is
impossible — refuted by the **proven** spherical arm lemma
`ZinanFFCT112.cauchy_arm_fixed_chord_contradiction_uncond` (unconditional, clean-3).  The arm-lemma
conclusion is now DERIVED, not posited (cf. the former `arm_conclusion` field).
-/
structure CauchyArmOpeningObstruction where
  n : ℕ
  hn : 2 ≤ n
  A : Fin (n + 1) → S2
  B : Fin (n + 1) → S2
  hA : StrictConvexSphArm A
  hB : StrictConvexSphArm B
  equal_sides : ∀ i : Fin n, sideLen A i = sideLen B i
  opened : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i
  some_angle_strictly_opened : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i
  fixed_chord : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))

namespace CauchyArmOpeningObstruction



end CauchyArmOpeningObstruction

/--
The corresponding GEOMETRIC data for the closing direction: the same impossibility with the arm closing
(`B`'s joints no wider than `A`'s, some strictly narrower) at a fixed chord — refuted by the same proven
arm lemma applied with the two arms swapped.
-/
structure CauchyArmClosingObstruction where
  n : ℕ
  hn : 2 ≤ n
  A : Fin (n + 1) → S2
  B : Fin (n + 1) → S2
  hA : StrictConvexSphArm A
  hB : StrictConvexSphArm B
  equal_sides : ∀ i : Fin n, sideLen A i = sideLen B i
  closed : ∀ i : Fin (n - 1), jointAngle B i ≤ jointAngle A i
  some_angle_strictly_closed : ∃ i : Fin (n - 1), jointAngle B i < jointAngle A i
  fixed_chord : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))

namespace CauchyArmClosingObstruction



end CauchyArmClosingObstruction

/-- A low sign-change vertex link supplies one of the two fixed-chord arm
contradictions above. -/
inductive CauchyArmFixedChordObstruction where
  | opening : CauchyArmOpeningObstruction → CauchyArmFixedChordObstruction
  | closing : CauchyArmClosingObstruction → CauchyArmFixedChordObstruction

namespace CauchyArmFixedChordObstruction



end CauchyArmFixedChordObstruction















/--
Local data at a surviving vertex after zero edges have been removed.

The two obstruction fields are the exact Cauchy-arm frontier at the finite
sign layer: the geometric vertex-link argument must convert a constant strict
sign pattern and a single positive block followed by a single negative block
into fixed-chord arm-lemma contradictions.  Once those obstructions and parity
are supplied, the `≥ 4` lower bound is proved below.
-/
structure CauchyArmVertex where
  /-- Number of strict sign changes around this vertex. -/
  signChanges : ℕ
  /-- Cyclic strict plus/minus sign changes occur in pairs. -/
  signChanges_even : Even signChanges
  /-- A constant strict sign pattern yields a fixed-chord arm contradiction. -/
  zero_sign_changes_obstruction : signChanges = 0 → CauchyArmFixedChordObstruction
  /-- Exactly one positive and one negative block yields a fixed-chord arm contradiction. -/
  two_sign_changes_obstruction : signChanges = 2 → CauchyArmFixedChordObstruction

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

/-- Count cyclically-adjacent unequal pairs of `x :: xs`, where the cyclic successor
of the last element is `first`.  `firstAux first prev xs` walks the tail `xs` with
`prev` the previous element, and at the end compares the last element to `first`. -/
def flipAux (first : α) : α → List α → ℕ
  | prev, [] => if prev ≠ first then 1 else 0
  | prev, x :: xs => (if prev ≠ x then 1 else 0) + flipAux first x xs

/-- The cyclic flip count of a list: the number of cyclically adjacent unequal pairs.
For a one-element (or empty) list it is `0`. -/
def cyclicFlipCount : List α → ℕ
  | [] => 0
  | x :: xs => flipAux x x xs

/-- The cyclic skip-zero flip count of a list of `EdgeSign`s: drop the zeros, then
take the cyclic flip count of the resulting strict sequence. -/
def cyclicFlipCountSkipZeros (xs : List EdgeSign) : ℕ :=
  cyclicFlipCount (xs.filterMap EdgeSign.toStrict)

/-- (1) Zeros are dropped: by definition, the skip-zero count is the cyclic flip
count of the strict sub-sequence. -/
@[simp] theorem cyclicFlipCountSkipZeros_eq_strict (xs : List EdgeSign) :
    cyclicFlipCountSkipZeros xs = cyclicFlipCount (xs.filterMap EdgeSign.toStrict) := rfl



/-- A two-valued sign as an element of `ZMod 2`. -/
def StrictEdgeSign.valZ : StrictEdgeSign → ZMod 2
  | StrictEdgeSign.plus => 0
  | StrictEdgeSign.minus => 1













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



/-- A strict (no-zero) signing on darts that is invariant under the edge involution
`α`, i.e. a sign attached to each edge (`α`-orbit) of `M`. -/
def EdgeInvariant (M : CombMap D) (s : D → StrictEdgeSign) : Prop :=
  ∀ d, s (M.α d) = s d

/-- The set of darts whose corner is a sign **change** read from the vertex side:
the edge of `d` and the edge of `σ d` differ. -/
def vertexChangeSet (M : CombMap D) (s : D → StrictEdgeSign) : Finset D :=
  Finset.univ.filter (fun d => s d ≠ s (M.σ d))

/-- The set of darts whose corner is a sign **change** read from the face side:
the edge of `d` and the edge of `φ d` differ. -/
def faceChangeSet (M : CombMap D) (s : D → StrictEdgeSign) : Finset D :=
  Finset.univ.filter (fun d => s d ≠ s (M.φ d))





/-- The vertex flip count at a `σ`-orbit (vertex) `Q`: the number of darts at that
vertex whose corner is a sign change. -/
def vertexFlip (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.σ)) : ℕ :=
  ((vertexChangeSet M s).filter (fun d => Quotient.mk (cycleSetoid M.σ) d = Q)).card

/-- The face flip count at a `φ`-orbit (face) `Q`. -/
def faceFlip (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.φ)) : ℕ :=
  ((faceChangeSet M s).filter (fun d => Quotient.mk (cycleSetoid M.φ) d = Q)).card

































/-- The `σ`-ordered list of edge signs around the vertex represented by dart `d`. -/
def vertexSignList (M : CombMap D) (es : D → EdgeSign) (d : D) : List EdgeSign :=
  (M.σ.toList d).map es

/-- The book's per-vertex count: the cyclic sign-flip count of the edge signs around
the vertex of `d`, in `σ`-order, with zeros skipped. -/
def vertexFlipCountSkipZeros (M : CombMap D) (es : D → EdgeSign) (d : D) : ℕ :=
  cyclicFlipCountSkipZeros (vertexSignList M es d)

/-- A vertex (represented by dart `d`) is **active** if some dart in its `σ`-orbit
carries a nonzero edge sign. -/
def ActiveVertex (M : CombMap D) (es : D → EdgeSign) (d : D) : Prop :=
  ∃ x, M.σ.SameCycle d x ∧ es x ≠ EdgeSign.zero





/-- Edge involution of the tetrahedron map: the six transpositions pairing each dart
with its reverse. -/
def tetraAlpha : Equiv.Perm (Fin 12) :=
  (List.formPerm [0, 3]) * (List.formPerm [1, 6]) * (List.formPerm [2, 9]) *
    (List.formPerm [4, 7]) * (List.formPerm [5, 10]) * (List.formPerm [8, 11])

/-- Vertex rotation of the tetrahedron map: the four `3`-cycles rotating the darts
around each of the four vertices. -/
def tetraSigma : Equiv.Perm (Fin 12) :=
  (List.formPerm [0, 1, 2]) * (List.formPerm [3, 5, 4]) *
    (List.formPerm [6, 7, 8]) * (List.formPerm [9, 11, 10])

/-- The tetrahedron as a combinatorial map on `Fin 12`. -/
def tetraMap : CombMap (Fin 12) where
  α := tetraAlpha
  σ := tetraSigma
  α_invol := by decide
  α_no_fixed := by decide





noncomputable instance : DecidableEq (Quotient (cycleSetoid tetraMap.φ)) :=
  Quotient.decidableEq























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

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- Length of a face = number of darts in its `φ`-orbit. -/
def faceLen (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) : ℕ :=
  (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card













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

/-- Vertices are `σ`-orbits of darts. -/
abbrev Vertex (M : CombMap D) : Type _ :=
  Quotient (cycleSetoid M.σ)

/-- Faces are `φ`-orbits of darts. -/
abbrev Face (M : CombMap D) : Type _ :=
  Quotient (cycleSetoid M.φ)

/-- The vertex at the tail of a dart. -/
def tail (M : CombMap D) (d : D) : M.Vertex :=
  Quotient.mk (cycleSetoid M.σ) d

/-- The vertex at the head of a dart, i.e. the tail of its reverse dart. -/
def head (M : CombMap D) (d : D) : M.Vertex :=
  Quotient.mk (cycleSetoid M.σ) (M.α d)

/-- The face containing a dart. -/
def dartFace (M : CombMap D) (d : D) : M.Face :=
  Quotient.mk (cycleSetoid M.φ) d

/-- The unoriented graph edge represented by a dart. -/
def dartEdge (M : CombMap D) (d : D) : Sym2 M.Vertex :=
  s(M.tail d, M.head d)

lemma alpha_alpha (M : CombMap D) (d : D) : M.α (M.α d) = d := by
  have h := congrArg (fun f : Equiv.Perm D => f d) M.α_invol
  simpa [Equiv.Perm.coe_mul, Function.comp_apply] using h

@[simp]
lemma tail_sigma (M : CombMap D) (d : D) : M.tail (M.σ d) = M.tail d := by
  exact Quotient.sound ⟨-1, by simp⟩

@[simp]
lemma tail_phi (M : CombMap D) (d : D) : M.tail (M.φ d) = M.head d := by
  unfold tail head
  exact Quotient.sound ⟨-1, by simp [φ, Equiv.Perm.coe_mul, Function.comp_apply]⟩

@[simp]
lemma tail_alpha (M : CombMap D) (d : D) : M.tail (M.α d) = M.head d :=
  rfl





/-- Vertex adjacency induced by the map darts, before deleting loops. -/
def Adj (M : CombMap D) (u v : M.Vertex) : Prop :=
  ∃ d : D, M.dartEdge d = s(u, v)

lemma adj_symm (M : CombMap D) {u v : M.Vertex} (h : M.Adj u v) : M.Adj v u := by
  rcases h with ⟨d, hd⟩
  exact ⟨d, by simpa [Sym2.eq_swap] using hd⟩



/-- The underlying `SimpleGraph` on vertex quotients.  Its adjacency is dart
adjacency with loops removed. -/
def toSimpleGraph (M : CombMap D) : SimpleGraph M.Vertex where
  Adj u v := u ≠ v ∧ M.Adj u v
  symm := by
    intro u v h
    exact ⟨h.1.symm, M.adj_symm h.2⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩



/-- No loops and no parallel edges in the quotient graph carried by the map. -/
structure IsSimpleGraph (M : CombMap D) : Prop where
  /-- No dart has equal endpoint vertices. -/
  no_loop : ∀ d : D, M.tail d ≠ M.head d
  /-- Two darts with the same unordered endpoint pair are the same map edge. -/
  no_parallel : ∀ {d e : D}, M.dartEdge d = M.dartEdge e → M.α.SameCycle d e









lemma alpha_sameCycle_of_same_endpoints (M : CombMap D) (hM : M.IsSimpleGraph)
    {d e : D} (htail : M.tail d = M.tail e) (hhead : M.head d = M.head e) :
    M.α.SameCycle d e := by
  exact hM.no_parallel (by simp [dartEdge, htail, hhead])











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

omit [DecidableEq D] in
/-- There is always a positive iterate of `p` from a surviving point back to a
surviving point: `orderOf p` returns to the starting point. -/
lemma exists_pos_pow_notMem (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) :
    ∃ n : ℕ, 0 < n ∧ (p ^ n) x.1 ∉ S := by
  refine ⟨orderOf p, orderOf_pos p, ?_⟩
  simpa using x.2

/-- The first positive `p`-iterate of `x` outside `S`. -/
noncomputable def firstOutside (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) : ℕ :=
  Nat.find (exists_pos_pow_notMem p S x)

lemma firstOutside_spec (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    0 < firstOutside p S x ∧ (p ^ firstOutside p S x) x.1 ∉ S :=
  Nat.find_spec (exists_pos_pow_notMem p S x)

lemma firstOutside_pos (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    0 < firstOutside p S x :=
  (firstOutside_spec p S x).1

lemma firstOutside_notMem (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    (p ^ firstOutside p S x) x.1 ∉ S :=
  (firstOutside_spec p S x).2

lemma firstOutside_min (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) {m : ℕ}
    (hm : m < firstOutside p S x) :
    ¬ (0 < m ∧ (p ^ m) x.1 ∉ S) :=
  Nat.find_min (exists_pos_pow_notMem p S x) hm

/-- The underlying function of `deleteSet`: move to the first surviving forward
iterate. -/
noncomputable def deleteSetFun (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) : {d : D // d ∉ S} :=
  ⟨(p ^ firstOutside p S x) x.1, firstOutside_notMem p S x⟩

@[simp]
lemma deleteSetFun_coe (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    (deleteSetFun p S x : D) = (p ^ firstOutside p S x) x.1 :=
  rfl

lemma firstOutside_inv_deleteSetFun (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    firstOutside p⁻¹ S (deleteSetFun p S x) = firstOutside p S x := by
  classical
  let n := firstOutside p S x
  have hnpos : 0 < n := firstOutside_pos p S x
  have hnnot : (p ^ n) x.1 ∉ S := firstOutside_notMem p S x
  refine (Nat.find_eq_iff (exists_pos_pow_notMem p⁻¹ S (deleteSetFun p S x))).2 ?_
  constructor
  · constructor
    · exact hnpos
    · have hpow : ((p⁻¹) ^ n) ((deleteSetFun p S x : {d : D // d ∉ S}) : D) = x.1 := by
        simp only [deleteSetFun_coe]
        rw [inv_pow]
        change (p ^ n).symm ((p ^ n) x.1) = x.1
        exact Equiv.symm_apply_apply (p ^ n) x.1
      simpa [hpow] using x.2
  · intro m hm
    rintro ⟨hmpos, hmnot⟩
    have hmn : m < n := hm
    have hsubpos : 0 < n - m := Nat.sub_pos_of_lt hmn
    have hsub_lt : n - m < n := Nat.sub_lt hnpos hmpos
    have hforward :
        (p ^ (n - m)) x.1 =
          ((p⁻¹) ^ m) ((deleteSetFun p S x : {d : D // d ∉ S}) : D) := by
      simp only [deleteSetFun_coe]
      rw [inv_pow]
      have hle : m ≤ n := le_of_lt hmn
      have hperm : (p ^ m)⁻¹ * p ^ n = p ^ (n - m) := by
        have hpown : p ^ n = p ^ m * p ^ (n - m) := by
          have hadd : m + (n - m) = n := Nat.add_sub_of_le hle
          calc
            p ^ n = p ^ (m + (n - m)) := by rw [hadd]
            _ = p ^ m * p ^ (n - m) := by rw [pow_add]
        calc
          (p ^ m)⁻¹ * p ^ n = (p ^ m)⁻¹ * (p ^ m * p ^ (n - m)) := by
            rw [hpown]
          _ = p ^ (n - m) := by
            rw [← mul_assoc, inv_mul_cancel, one_mul]
      calc
        (p ^ (n - m)) x.1 = ((p ^ m)⁻¹ * (p ^ n)) x.1 := by
          rw [hperm]
        _ = ((p ^ m)⁻¹) ((p ^ n) x.1) := rfl
        _ = ((p⁻¹) ^ m) ((p ^ n) x.1) := by rw [inv_pow]
    have hbad : 0 < n - m ∧ (p ^ (n - m)) x.1 ∉ S := by
      exact ⟨hsubpos, by simpa [hforward] using hmnot⟩
    exact firstOutside_min p S x hsub_lt hbad

lemma deleteSetFun_inv_apply (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    deleteSetFun p⁻¹ S (deleteSetFun p S x) = x := by
  classical
  apply Subtype.ext
  rw [deleteSetFun_coe, firstOutside_inv_deleteSetFun p S x, deleteSetFun_coe]
  rw [inv_pow]
  change (p ^ firstOutside p S x).symm ((p ^ firstOutside p S x) x.1) = x.1
  exact Equiv.symm_apply_apply (p ^ firstOutside p S x) x.1

end DeleteSet

open DeleteSet

/-- Delete a finite set from the cycles of a permutation, reconnecting the
surviving points by skipping deleted points. -/
noncomputable def deleteSet (p : Equiv.Perm D) (S : Finset D) :
    Equiv.Perm {d : D // d ∉ S} where
  toFun := deleteSetFun p S
  invFun := deleteSetFun p⁻¹ S
  left_inv := deleteSetFun_inv_apply p S
  right_inv := by
    intro x
    simpa using deleteSetFun_inv_apply p⁻¹ S x



lemma sameCycle_deleteSet_imp (p : Equiv.Perm D) (S : Finset D)
    {x y : {d : D // d ∉ S}} :
    (deleteSet p S).SameCycle x y → p.SameCycle x.1 y.1 := by
  classical
  intro hxy
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.SameCycle.exists_nat_pow_eq (f := deleteSet p S) hxy
  clear hxy
  revert x
  induction m with
  | zero =>
      intro x hm
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hm
      exact (congrArg Subtype.val hm).sameCycle p
  | succ m ih =>
      intro x hm
      let z : {d : D // d ∉ S} := deleteSet p S x
      have hstep : p.SameCycle x.1 z.1 := by
        refine ⟨(firstOutside p S x : ℤ), ?_⟩
        rw [zpow_natCast]
        rfl
      have htail : ((deleteSet p S) ^ m) z = y := by
        simpa [z, pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hm
      exact hstep.trans (ih (x := z) htail)

lemma sameCycle_deleteSet_of_pow (p : Equiv.Perm D) (S : Finset D) :
    ∀ m : ℕ, ∀ x y : {d : D // d ∉ S},
      (p ^ m) x.1 = y.1 → (deleteSet p S).SameCycle x y := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro x y hxy
      by_cases hm0 : m = 0
      · subst hm0
        apply (Subtype.ext ?_).sameCycle
        simpa using hxy
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        let n := firstOutside p S x
        have hnpos : 0 < n := firstOutside_pos p S x
        have hnot_lt : ¬ m < n := by
          intro hmn
          have hbad : 0 < m ∧ (p ^ m) x.1 ∉ S := by
            exact ⟨hmpos, by simpa [hxy] using y.2⟩
          exact firstOutside_min p S x hmn hbad
        have hnm : n ≤ m := le_of_not_gt hnot_lt
        let z : {d : D // d ∉ S} := deleteSet p S x
        have hxz : z.1 = (p ^ n) x.1 := rfl
        have hstep : (deleteSet p S).SameCycle x z := by
          refine ⟨1, ?_⟩
          change deleteSet p S x = z
          rfl
        by_cases hnm_eq : n = m
        · have hzy : z = y := by
            apply Subtype.ext
            rw [hxz, hnm_eq, hxy]
          simpa [hzy] using hstep
        · have hlt : m - n < m := Nat.sub_lt hmpos hnpos
          have hpow : (p ^ (m - n)) z.1 = y.1 := by
            rw [hxz]
            rw [← mul_apply, ← pow_add]
            have hadd : m - n + n = m := Nat.sub_add_cancel hnm
            rw [hadd, hxy]
          exact hstep.trans (ih (m - n) hlt z y hpow)

lemma sameCycle_deleteSet_iff (p : Equiv.Perm D) (S : Finset D)
    (x y : {d : D // d ∉ S}) :
    (deleteSet p S).SameCycle x y ↔ p.SameCycle x.1 y.1 := by
  classical
  constructor
  · exact sameCycle_deleteSet_imp p S
  · intro h
    obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := p) h
    exact sameCycle_deleteSet_of_pow p S m x y hm

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

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Cyclic successor on a nonempty finite index type. -/
def cyclicNext {n : ℕ} (h : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ h⟩



/-- The dart set of a face, as a finite orbit set. -/
def faceOrbitFinset (M : CombMap D) (f : M.Face) : Finset D :=
  Finset.univ.filter fun d => M.dartFace d = f



/-- A normalized cyclic dart list for a selected face orbit.

The `root` chooses one representative and fixes the cyclic rotation.  The
`toFinset_eq` field says the list enumerates exactly the selected `φ`-orbit.
-/
structure NormalizedCyclicDartList (M : CombMap D) (f : M.Face)
    (root : D) (darts : List D) : Prop where
  head_eq : darts.head? = some root
  root_face : M.dartFace root = f
  nodup : darts.Nodup
  length_pos : 0 < darts.length
  toFinset_eq : darts.toFinset = faceOrbitFinset M f

/-- A boundary arc/path between two boundary vertices. -/
structure BoundaryPath (M : CombMap D) (u v : M.Vertex) where
  /-- Vertices in path order, including both endpoints. -/
  vertices : List M.Vertex
  /-- Edges in path order.  For boundary arcs these are boundary-cycle edges. -/
  edges : List (Sym2 M.Vertex)
  /-- The first listed vertex is the initial endpoint. -/
  starts_at : vertices.head? = some u
  /-- The last listed vertex is the terminal endpoint. -/
  ends_at : vertices.getLast? = some v
  /-- The arc is simple as a vertex list. -/
  simple : vertices.Nodup

namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}

/-- Interior vertices of a path: endpoints removed. -/
def internalVertices (P : BoundaryPath M u v) : List M.Vertex :=
  P.vertices.tail.dropLast

/-- A path has at least one internal vertex. -/
def HasInternalVertex (P : BoundaryPath M u v) : Prop :=
  P.internalVertices ≠ []







end BoundaryPath

/-- The two boundary arcs determined by a pair of distinct boundary vertices. -/
structure BoundaryArcSplit (M : CombMap D)
    (boundaryVertices : List M.Vertex) (boundaryEdges : List (Sym2 M.Vertex))
    (u v : M.Vertex) where
  /-- The arc from `u` to `v`. -/
  path₁ : BoundaryPath M u v
  /-- The complementary arc from `v` back to `u`. -/
  path₂ : BoundaryPath M v u
  /-- `path₁` uses only boundary vertices. -/
  path₁_boundary_vertices :
    ∀ ⦃w : M.Vertex⦄, w ∈ path₁.vertices → w ∈ boundaryVertices
  /-- `path₂` uses only boundary vertices. -/
  path₂_boundary_vertices :
    ∀ ⦃w : M.Vertex⦄, w ∈ path₂.vertices → w ∈ boundaryVertices
  /-- Together the two arcs cover the boundary vertex list. -/
  boundary_vertices_covered :
    ∀ w : M.Vertex, w ∈ boundaryVertices ↔ w ∈ path₁.vertices ∨ w ∈ path₂.vertices
  /-- The internal vertices of the two arcs are disjoint. -/
  internally_disjoint :
    ∀ ⦃w : M.Vertex⦄,
      w ∈ path₁.internalVertices → w ∈ path₂.internalVertices → False
  /-- The first arc is nontrivial when the endpoint pair is not a boundary edge.
  (One-directional: a *proper* — non-adjacent — pair forces an internal vertex.  The
  converse `HasInternalVertex → proper` is intentionally NOT required: for a *consecutive*
  pair the long complementary arc must still carry the cycle's other vertices internally,
  so demanding `↔` would make `BoundaryArcSplit`, hence `BoundaryCycle`/`NearTriangulation`,
  uninhabited whenever the cycle has a third vertex.  See `ZinanCh35VacuityObstruction`.) -/
  path₁_internal_of_proper :
    s(u, v) ∉ boundaryEdges → path₁.HasInternalVertex
  /-- The second arc is nontrivial when the endpoint pair is not a boundary edge
  (one-directional, same rationale as `path₁_internal_of_proper`). -/
  path₂_internal_of_proper :
    s(u, v) ∉ boundaryEdges → path₂.HasInternalVertex

/-- The orbit-algebraic **core** of a boundary cycle — every field except the
`arcSplit` certificate.  Split out (2026-06-15) so the universal arc-split
(`arcSplit_of_nodup`, derivable from `VertexNodup`) can be proved over the core and
installed into the full `BoundaryCycle` without the `boundaryCycleOfFace ↔ arcSplit`
self-reference.  See `HANDOFF/ch35-arcsplit-core-refactor.md`. -/
structure BoundaryCycleData (M : CombMap D) (f : M.Face) where
  /-- Chosen dart representative fixing the cyclic rotation. -/
  root : D
  /-- Normalized cyclic dart list enumerating the selected face orbit. -/
  darts : List D
  /-- Cyclic boundary vertex list. -/
  vertices : List M.Vertex
  /-- Cyclic boundary edge list. -/
  edges : List (Sym2 M.Vertex)
  /-- The dart list is normalized and exactly enumerates the selected face orbit. -/
  normalized : NormalizedCyclicDartList M f root darts
  /-- Boundary vertices are the tails of the cyclic dart list. -/
  vertices_eq : vertices = darts.map M.tail
  /-- Boundary edges are the graph edges represented by the cyclic dart list. -/
  edges_eq : edges = darts.map M.dartEdge
  /-- The cyclic order agrees with the face permutation. -/
  consecutive_phi :
    ∀ i : Fin darts.length,
      darts.get (cyclicNext normalized.length_pos i) = M.φ (darts.get i)
  /-- Consecutive boundary darts match at their common boundary vertex. -/
  consecutive_vertex :
    ∀ i : Fin darts.length,
      M.tail (darts.get (cyclicNext normalized.length_pos i)) = M.head (darts.get i)

/-- A boundary cycle for the selected face `f`: the orbit-algebraic core
(`BoundaryCycleData`) together with the arc-splitting certificate.

The dart list is a normalized cyclic enumeration of the `φ`-orbit of `f`.
The vertex and edge lists are exposed so later files can reason about the
boundary without repeatedly unfolding quotient-orbit facts.
-/
structure BoundaryCycle (M : CombMap D) (f : M.Face) extends BoundaryCycleData M f where
  /-- Arc-splitting certificate for any two distinct listed boundary vertices. -/
  arcSplit :
    ∀ ⦃u v : M.Vertex⦄,
      u ≠ v → u ∈ vertices → v ∈ vertices →
        BoundaryArcSplit M vertices edges u v

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

/-- Boundary vertices are represented by the exposed cyclic vertex list. -/
def IsBoundaryVertex (C : BoundaryCycle M f) (v : M.Vertex) : Prop :=
  v ∈ C.vertices

/-- Boundary edges are represented by the exposed cyclic edge list. -/
def IsBoundaryEdge (C : BoundaryCycle M f) (e : Sym2 M.Vertex) : Prop :=
  e ∈ C.edges



/-- The boundary vertex list is simple. -/
def VertexNodup (C : BoundaryCycle M f) : Prop :=
  C.vertices.Nodup



/-- Boundary length, measured in darts/edges. -/
def length (C : BoundaryCycle M f) : ℕ :=
  C.darts.length



























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
open EdgeSign
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
open EdgeSign



















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
open ProofsInTheBook.Chapter13 EdgeSign
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


