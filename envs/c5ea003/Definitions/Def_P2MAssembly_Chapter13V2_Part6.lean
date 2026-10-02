-- Prove2me | Definitions.Def_P2MAssembly_Chapter13V2_Part6
-- name    : P2MAssembly_Chapter13V2_Part6
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T20:50:51.309046+00:00
-- url     : https://prove2.me/theorems/fa459118-6817-4146-84fb-7c5e4657f09c
-- title:
--   Convex Euclidean realizations and derived spherical links
-- statement:
--   This part defines triangulated Euclidean realizations with vertex coordinates, triangular face representatives, nondegenerate edges and faces, supporting planes and strict separation of vertices not belonging to each face. Face-local outward orientation specifies a positive multiple of the ordered cross product. ConvexEuclideanPolyhedron additionally carries degree at least three, a connected Euler-characteristic-two map, triangular faces and graph simplicity. Derived links list neighbors in reverse vertex-rotation order. CongruentFaces means equality of corresponding dart-edge lengths. The part also defines the signed dihedral differences and the correspondence between darts and vertex-star positions. These precise geometric input conditions are retained; arbitrary polygon-faced polyhedra are not introduced.
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
import Definitions.Def_P2MAssembly_Chapter13V2_Part4
import Definitions.Def_P2MAssembly_Chapter13V2_Part5

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








attribute [instance] ChordSideReconstruction.fintypeDₛ ChordSideReconstruction.decEqDₛ

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

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace List



end List











































































/-- Reindexing a strict convex arm by a propositionally-trivial `Fin.cast` preserves it. -/
theorem strictArm_reindex {n m : ℕ} (h : n = m) (A : Fin (m + 1) → S2)
    (hA : StrictConvexSphArm A) :
    StrictConvexSphArm (fun i : Fin (n + 1) => A (Fin.cast (by rw [h]) i)) := by
  subst h
  simpa using hA



/-- The `Q`-link reindex is a strict convex arm (from the genuine `(starQ Q).vertexLink_strictArm`). -/
theorem linkQcast_strictArm (M : CombMap D) (starP starQ : M.Vertex → VertexStar)
    (hnn : ∀ Q, (starQ Q).n = (starP Q).n) (Q : M.Vertex) :
    StrictConvexSphArm (linkQcast M starP starQ hnn Q) :=
  strictArm_reindex (hnn Q).symm (starQ Q).vertexLink (starQ Q).vertexLink_strictArm

namespace ConvexPolytopeRealization

variable {M : CombMap D} (R : ConvexPolytopeRealization M)


/-- Shorthand: the `Q`-link (reindexed) at `Q`. -/
@[reducible] def linkQ (Q : M.Vertex) : Fin ((R.starP Q).n + 1) → S2 :=
  linkQcast M R.starP R.starQ R.hnn Q

/-- The `Q`-link reindex is a strict convex arm. -/
theorem linkQ_strictArm (Q : M.Vertex) : StrictConvexSphArm (R.linkQ Q) :=
  linkQcast_strictArm M R.starP R.starQ R.hnn Q



/-- A dart `d` is in the `σ`-orbit of its vertex's representative `dartRep (tail d)`. -/
theorem sameCycle_dartRep (d : D) : M.σ.SameCycle (R.dartRep (M.tail d)) d := by
  have h : Quotient.mk (cycleSetoid M.σ) (R.dartRep (M.tail d)) = Quotient.mk (cycleSetoid M.σ) d := by
    rw [show Quotient.mk (cycleSetoid M.σ) (R.dartRep (M.tail d)) = M.tail (R.dartRep (M.tail d)) from rfl,
        R.dartRep_tail]
    rfl
  exact Quotient.exact h

/-- `ActiveVertex` is constant on a `σ`-orbit. -/
theorem activeVertex_congr {d d' : D} (h : M.σ.SameCycle d d') :
    ActiveVertex M R.edgeSign d ↔ ActiveVertex M R.edgeSign d' := by
  constructor
  · rintro ⟨x, hx, hxne⟩; exact ⟨x, h.symm.trans hx, hxne⟩
  · rintro ⟨x, hx, hxne⟩; exact ⟨x, h.trans hx, hxne⟩



/-- **The crux bridge (DERIVED, not posited).**  At the representative dart of vertex `Q`, the closed-link
cyclic flip count equals the `σ`-cyclic skip-zeros count of the edge signs.  Chain:
`signChangesFull = cyclicFlips (nzSigns linkDiff)` (def) `= cyclicFlipCountSkipZeros (real signs)`
(reconciliation) `= cyclicFlipCountSkipZeros (σ-edge-sign list)` (`linkOrder`) `= vertexFlipCountSkipZeros`
(def). -/
theorem signChangesFull_eq_vertexFlip_rep (Q : M.Vertex) :
    signChangesFull (R.starP Q).vertexLink (R.linkQ Q)
      = vertexFlipCountSkipZeros M R.edgeSign (R.dartRep Q) := by
  unfold signChangesFull
  rw [cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros]
  exact (cyclicFlipCountSkipZeros_of_dihedralRotated (R.linkOrder Q)).symm

/-- **The crux bridge at an arbitrary active dart.**  By `σ`-orbit invariance of
`vertexFlipCountSkipZeros`, the bridge at the representative transfers to every dart of the vertex. -/
theorem signChangesFull_eq_vertexFlip (d : D) :
    signChangesFull (R.starP (M.tail d)).vertexLink (R.linkQ (M.tail d))
      = vertexFlipCountSkipZeros M R.edgeSign d := by
  rw [R.signChangesFull_eq_vertexFlip_rep (M.tail d)]
  exact vertexFlipCountSkipZeros_sameCycle M R.edgeSign (R.sameCycle_dartRep d)



/-- **The genuine vertex-arm datum at an active dart** (Bridge: `vertexArm`).  Built from the two real
spherical links via `cauchyArmVertexFull_of_links`: equal sides (`sides_eq`), equal closing chord
(`close_eq`), the interior strict witness (`interiorActive`), and the two-arc residual (`twoArc`).  Its
`signChanges` is the genuine FULL closed-link cyclic count `signChangesFull`. -/
noncomputable def vertexArm (d : D) (hd : ActiveVertex M R.edgeSign d) :
    Chapter13.CauchyArmVertex :=
  cauchyArmVertexFull_of_links (R.starP (M.tail d)).n (R.starP (M.tail d)).hn
    (R.starP (M.tail d)).vertexLink (R.linkQ (M.tail d))
    (R.starP (M.tail d)).vertexLink_strictArm (R.linkQ_strictArm (M.tail d))
    (R.sides_eq (M.tail d)) (R.close_eq (M.tail d))
    (R.interiorActive (M.tail d)
      ((R.activeVertex_congr (R.sameCycle_dartRep d)).mpr hd))
    (R.twoArc (M.tail d))

/-- `vertexArm`'s `signChanges` is `signChangesFull` (by construction). -/
theorem vertexArm_signChanges (d : D) (hd : ActiveVertex M R.edgeSign d) :
    (R.vertexArm d hd).signChanges
      = signChangesFull (R.starP (M.tail d)).vertexLink (R.linkQ (M.tail d)) := rfl

/-- **The crux bridge as the assembly field** (DERIVED): the arm-datum's sign-change count equals the
`σ`-cycle skip-zeros flip count at the vertex. -/
theorem vertexArm_signChanges_eq (d : D) (hd : ActiveVertex M R.edgeSign d) :
    (R.vertexArm d hd).signChanges = vertexFlipCountSkipZeros M R.edgeSign d := by
  rw [R.vertexArm_signChanges d hd, R.signChangesFull_eq_vertexFlip d]



/-- **`realization_marked`** — the faithful `CauchyMarkedTriangulatedSphere` of the realization `R`.
All four bridges are derived theorems: `edgeSign`/`edgeSign_inv` (interface), `vertexArm` (real links),
and the crux `vertexArm_signChanges_eq` (derived via `linkOrder` + reconciliation + orbit invariance). -/
def realization_marked :
    Ch13CauchyAssembly.CauchyMarkedTriangulatedSphere M where
  isSphere := R.isSphere
  triangleFaces := R.triangle
  isSimple := R.isSimple
  edgeSign := R.edgeSign
  edgeSign_inv := R.edgeSign_inv
  vertexArm := R.vertexArm
  vertexArm_signChanges_eq := R.vertexArm_signChanges_eq











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

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The ambient Euclidean space for the chapter-13 geometric witness. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Three vertices assigned to a face, in cyclic combinatorial order. -/
abbrev FaceVertices (M : CombMap D) := M.Face → Fin 3 → M.Vertex

/--
A triangulated Euclidean polyhedron carried by a combinatorial map.

The field `faceDart` chooses a dart on every face; `faceVertex` is required to
be the three tails of that face in the `φ`-order from the chosen dart.  The
supporting halfspace certificate orients every face normal outward, so all
vertices lie in the non-positive halfspace of the face plane.

The vertex-link cyclic order is deliberately not part of this b1 interface;
that is the later b3 residue.
-/
structure TriangulatedEuclideanPolyhedron (M : CombMap D) where
  /-- Vertex coordinates in `ℝ³`. -/
  pos : M.Vertex → E3
  /-- A representative dart on each face. -/
  faceDart : M.Face → D
  /-- The representative really lies on the face it represents. -/
  faceDart_face : ∀ f, M.dartFace (faceDart f) = f
  /-- The three combinatorial vertices of a face, in cyclic order. -/
  faceVertex : FaceVertices M
  /-- Face vertices are exactly the tails along one `φ`-cycle from `faceDart`. -/
  face_vertices_match : ∀ f,
    faceVertex f =
      ![M.tail (faceDart f),
        M.tail (M.φ (faceDart f)),
        M.tail (M.φ (M.φ (faceDart f)))]
  /-- Every combinatorial face is triangular. -/
  every_face_triangle : M.FaceRegular 3
  /-- Edges are realized by distinct points. -/
  edge_nondegenerate : ∀ d, pos (M.tail d) ≠ pos (M.head d)
  /-- The three points of each face are affinely independent. -/
  face_nondegenerate : ∀ f,
    AffineIndependent ℝ
      (![pos (M.tail (faceDart f)),
        pos (M.tail (M.φ (faceDart f))),
        pos (M.tail (M.φ (M.φ (faceDart f))))] : Fin 3 → E3)
  /-- A selected point on each supporting face plane. -/
  face_point : M.Face → E3
  /-- An outward normal for each face plane. -/
  outward_normal : M.Face → E3
  /-- The three face vertices lie on the chosen plane. -/
  face_plane : ∀ f i,
    inner ℝ (outward_normal f) (pos (faceVertex f i) - face_point f) = 0
  /-- Convexity as a supporting halfspace certificate for every face. -/
  face_supporting_halfspace : ∀ f v,
    inner ℝ (outward_normal f) (pos v - face_point f) ≤ 0
  /-- Strict support: only the three vertices of the face lie on its supporting plane. -/
  face_support_strict : ∀ (f : M.Face) (v : M.Vertex),
    (∀ i, v ≠ faceVertex f i) →
      inner ℝ (outward_normal f) (pos v - face_point f) < 0

/-- The Euclidean edge vector carried by an oriented dart. -/
def edgeVec {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d : D) : E3 :=
  P.pos (M.head d) - P.pos (M.tail d)

/-- The supporting face used for the reverse-`σ` vertex-link side ending at `d`. -/
def reverseFaceBetween (M : CombMap D) (d : D) : M.Face :=
  M.dartFace d

/--
The stored map rotation is faithful to the outward orientation used by the
existing Chapter 13 vertex-link convention.

The current link builder reads neighbours in reverse `σ` order.  Thus the face
of `d` is oriented by the two outgoing edge vectors
`edgeVec (σ⁻¹ d), edgeVec d`, and the outward normal is a positive multiple of
that reversed cross product.
-/
structure RotationFaithful {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) : Prop where
  outward_normal_eq_pos_smul_reverse_cross :
    ∀ d : D,
      ∃ lam : ℝ, 0 < lam ∧
        P.outward_normal (reverseFaceBetween M d) =
          lam • cross (edgeVec P (M.σ.symm d)) (edgeVec P d)

/--
Face-local outward orientation, stated directly in the cyclic order of the
triangular face containing `d`.
-/
def FaceOrientationFaithful {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) : Prop :=
  ∀ d : D,
    ∃ lam : ℝ, 0 < lam ∧
      P.outward_normal (M.dartFace d) =
        lam • cross
          (P.pos (M.tail (M.φ (M.φ d))) - P.pos (M.tail d))
          (P.pos (M.tail (M.φ d)) - P.pos (M.tail d))

 theorem faceDart_phi_ne_self {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    M.φ (P.faceDart f) ≠ P.faceDart f := by
  intro h
  let p : Fin 3 → E3 :=
    ![P.pos (M.tail (P.faceDart f)),
      P.pos (M.tail (M.φ (P.faceDart f))),
      P.pos (M.tail (M.φ (M.φ (P.faceDart f))))]
  have hinj : Function.Injective p := (P.face_nondegenerate f).injective
  have hpts : p 1 = p 0 := by
    simp [p, h]
  have h10 : (1 : Fin 3) = 0 := hinj hpts
  norm_num at h10

 theorem faceDart_phi_cube_eq_self {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    (M.φ ^ 3) (P.faceDart f) = P.faceDart f := by
  let fd := P.faceDart f
  have hφne : M.φ fd ≠ fd := by
    simpa [fd] using faceDart_phi_ne_self P f
  have hlen : M.faceLen f = 3 := by
    simpa [CombMap.faceLen] using P.every_face_triangle f
  have hcard : (M.φ.cycleOf fd).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφne]
    simpa [fd, P.faceDart_face f] using hlen
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ 3 fd
  rw [hcard, Nat.mod_self] at hpow
  simpa [fd] using hpow.symm

/-- A dart on a triangular Euclidean face is one of the three `φ`-successive
darts from the stored representative of that face. -/
theorem dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) {f : M.Face} {d : D}
    (hd : M.dartFace d = f) :
    d = P.faceDart f ∨
      d = M.φ (P.faceDart f) ∨
      d = M.φ (M.φ (P.faceDart f)) := by
  let fd := P.faceDart f
  have hφne : M.φ fd ≠ fd := by
    simpa [fd] using faceDart_phi_ne_self P f
  have hlen : M.faceLen f = 3 := by
    simpa [CombMap.faceLen] using P.every_face_triangle f
  have hcard : (M.φ.cycleOf fd).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφne]
    simpa [fd, P.faceDart_face f] using hlen
  have hsame : M.φ.SameCycle fd d := by
    have hq : M.dartFace d = M.dartFace fd := by
      rw [hd, P.faceDart_face f]
    exact (Quotient.exact hq).symm
  have hsupp : fd ∈ M.φ.support := Equiv.Perm.mem_support.mpr hφne
  obtain ⟨i, hi, hpow⟩ := hsame.exists_pow_eq_of_mem_support hsupp
  rw [hcard] at hi
  interval_cases i
  · left
    simpa [fd] using hpow.symm
  · right
    left
    simpa [fd] using hpow.symm
  · right
    right
    simpa [fd, pow_succ] using hpow.symm

/-- Every dart tail is one of the three stored vertices of its dart face. -/
theorem tail_mem_faceVertex {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    ∃ k : Fin 3, M.tail d = P.faceVertex (M.dartFace d) k := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq
      P (f := M.dartFace d) (d := d) rfl with h | h | h
  · refine ⟨0, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 0
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm
  · refine ⟨1, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 1
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm
  · refine ⟨2, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 2
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm

/-- On a triangular Euclidean face, two `φ` steps reach the head of the
previous dart in the reverse `σ` order. -/
theorem tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d) := by
  have hcube : (M.φ ^ 3) d = d := by
    rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq
        P (f := M.dartFace d) (d := d) rfl with h | h | h
    · rw [h]
      exact faceDart_phi_cube_eq_self P (M.dartFace d)
    · rw [h]
      exact congrArg M.φ (faceDart_phi_cube_eq_self P (M.dartFace d))
    · rw [h]
      exact congrArg (fun x => M.φ (M.φ x))
        (faceDart_phi_cube_eq_self P (M.dartFace d))
  have hpred : M.φ (M.φ d) = M.φ.symm d := by
    apply M.φ.injective
    rw [Equiv.apply_symm_apply]
    simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
  have hsymm : M.φ.symm d = M.α (M.σ.symm d) := by
    apply M.φ.injective
    rw [Equiv.apply_symm_apply]
    symm
    change (M.σ * M.α) (M.α (M.σ.symm d)) = d
    rw [Equiv.Perm.mul_apply, M.alpha_alpha, Equiv.apply_symm_apply]
  rw [hpred, hsymm, M.tail_alpha]

 theorem tail_sigma_symm {M : CombMap D} (d : D) :
    M.tail (M.σ.symm d) = M.tail d := by
  have h := M.tail_sigma (M.σ.symm d)
  simpa using h.symm

/-- Face-local orientation implies the reverse-`σ` rotation-faithful convention
used by the vertex-link construction. -/
theorem rotationFaithful_of_faceOrientationFaithful {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M)
    (hface : FaceOrientationFaithful P) :
    RotationFaithful P where
  outward_normal_eq_pos_smul_reverse_cross := by
    intro d
    obtain ⟨lam, hlam, hnormal⟩ := hface d
    refine ⟨lam, hlam, ?_⟩
    have hprev :
        edgeVec P (M.σ.symm d) =
          P.pos (M.tail (M.φ (M.φ d))) - P.pos (M.tail d) := by
      simp [edgeVec, tail_sigma_symm,
        ← tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P d]
    have hnext :
        edgeVec P d =
          P.pos (M.tail (M.φ d)) - P.pos (M.tail d) := by
      simp [edgeVec, M.tail_phi]
    simpa [reverseFaceBetween, hprev, hnext] using hnormal



/-- The selected face plane contains the tail of every dart on that face. -/
theorem face_plane_dart {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    inner ℝ (P.outward_normal (M.dartFace d))
      (P.pos (M.tail d) - P.face_point (M.dartFace d)) = 0 := by
  obtain ⟨k, hk⟩ := tail_mem_faceVertex P d
  rw [hk]
  exact P.face_plane (M.dartFace d) k

































































-- The regular tetrahedron satisfies the reverse-`σ` rotation-faithfulness convention.


-- The regular tetrahedron satisfies the face-local outward-orientation convention.




/-- The outward normal on the face to the left of a dart. -/
def dartNormal {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d : D) : E3 :=
  P.outward_normal (M.dartFace d)



/--
The interior dihedral angle along a dart-represented edge.

With outward normals `n_f,n_g`, this is `π - angle n_f n_g`.
-/
def dihedralAngleAtDart {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d : D) : ℝ :=
  Real.pi - InnerProductGeometry.angle (dartNormal P d) (dartNormal P (M.α d))





theorem dihedralAngleAtDart_alpha {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    dihedralAngleAtDart P (M.α d) = dihedralAngleAtDart P d := by
  unfold dihedralAngleAtDart dartNormal
  rw [M.alpha_alpha, InnerProductGeometry.angle_comm]





/-- The dihedral-difference sign carried by a dart. -/
def dihedralSignAtDart {M : CombMap D}
    (P Q : TriangulatedEuclideanPolyhedron M) (d : D) : ProofsInTheBook.Chapter13.EdgeSign :=
  ProofsInTheBook.Ch13Realization.realSignToEdgeSign
    (dihedralAngleAtDart Q d - dihedralAngleAtDart P d)

theorem dihedralSignAtDart_alpha {M : CombMap D}
    (P Q : TriangulatedEuclideanPolyhedron M) (d : D) :
    dihedralSignAtDart P Q (M.α d) = dihedralSignAtDart P Q d := by
  unfold dihedralSignAtDart
  rw [dihedralAngleAtDart_alpha P d, dihedralAngleAtDart_alpha Q d]



























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

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

 lemma prev_mod_succ_mod {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    (((k + N - 1) % N + 1) % N) = k := by
  by_cases hk0 : k = 0
  · subst hk0
    have hNm1 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (Nat.sub_lt hN Nat.zero_lt_one)
    rw [zero_add, hNm1]
    have hN' : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hN)
    rw [hN', Nat.mod_self]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hsplit : k + N - 1 = (k - 1) + N := by omega
    rw [hsplit, Nat.add_mod_right]
    have hkpred : k - 1 < N := by omega
    rw [Nat.mod_eq_of_lt hkpred]
    have hks : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
    rw [hks, Nat.mod_eq_of_lt hk]

 def finOneOfThree {N : ℕ} (hN : 3 ≤ N) : Fin N :=
  ⟨1, by omega⟩

 lemma rev_add_one_rev_val {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    ((Fin.rev (Fin.rev i + finOneOfThree hN) : Fin N) : ℕ) =
      (i.val + N - 1) % N := by
  rw [Fin.val_rev, Fin.val_add, Fin.val_rev]
  simp only [finOneOfThree, Fin.val_mk]
  by_cases hi0 : i.val = 0
  · rw [hi0]
    have hinner : (N - (0 + 1) + 1) % N = 0 := by
      have hNpos : 0 < N := by omega
      have heq : N - (0 + 1) + 1 = N := by omega
      rw [heq, Nat.mod_self]
    rw [hinner]
    have hrhs : (0 + N - 1) % N = N - 1 := by
      rw [zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hrhs]
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi0
    have hinner : (N - (i.val + 1) + 1) % N = N - i.val := by
      have heq : N - (i.val + 1) + 1 = N - i.val := by omega
      rw [heq, Nat.mod_eq_of_lt (by omega)]
    have hrhs : (i.val + N - 1) % N = i.val - 1 := by
      have heq : i.val + N - 1 = (i.val - 1) + N := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hinner, hrhs]
    omega

 lemma rev_sub_one_rev_val {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    ((Fin.rev (Fin.rev i - finOneOfThree hN) : Fin N) : ℕ) =
      (i.val + 1) % N := by
  rw [Fin.val_rev, Fin.sub_def, Fin.val_rev]
  simp only [finOneOfThree, Fin.val_mk]
  have hinner : (N - 1 + (N - (i.val + 1))) % N =
      (N - (i.val + 1) + (N - 1)) % N := by
    rw [Nat.add_comm]
  rw [hinner]
  by_cases hilast : i.val + 1 = N
  · have hi : i.val = N - 1 := by omega
    rw [hi]
    have hmod : (N - (N - 1 + 1) + (N - 1)) % N = N - 1 := by
      have heq : N - (N - 1 + 1) + (N - 1) = N - 1 := by omega
      rw [heq, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    rw [show (N - 1 + 1) % N = 0 by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]]
    omega
  · have hi1lt : i.val + 1 < N := by omega
    have hmod1 : (N - (i.val + 1) + (N - 1)) % N = N - (i.val + 2) := by
      have hsum : N - (i.val + 1) + (N - 1) = (N - (i.val + 2)) + N := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod1]
    have htarget : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hi1lt
    rw [htarget]
    omega



/-- The incident darts at a vertex, rooted at `Quotient.out v` and ordered by `σ`. -/
def incidentDarts (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : List D :=
  M.σ.toList (Quotient.out v)

/-- The combinatorial degree read from the `σ`-cycle list. -/
def vDeg (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : ℕ :=
  (incidentDarts P v).length

/-- The `i`-th incident dart in the `σ`-cycle. -/
def incidentDart (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (i : Fin (vDeg P v)) : D :=
  (incidentDarts P v).get i

/-- Every dart read from the incident list has tail `v`. -/
theorem incidentDart_tail (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (i : Fin (vDeg P v)) :
    M.tail (incidentDart P v i) = v := by
  unfold incidentDart
  have hmem : (incidentDarts P v).get i ∈ incidentDarts P v :=
    List.get_mem _ _
  unfold incidentDarts at hmem ⊢
  have hsame : M.σ.SameCycle (Quotient.out v) ((M.σ.toList (Quotient.out v)).get i) :=
    (Equiv.Perm.mem_toList_iff.mp hmem).1
  calc
    M.tail ((M.σ.toList (Quotient.out v)).get i) = M.tail (Quotient.out v) :=
      Quotient.sound hsame.symm
    _ = v := Quotient.out_eq v

/-- The `VertexStar.n` associated to a vertex of degree `vDeg`: there are `n + 1` neighbours. -/
def starN (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : ℕ :=
  vDeg P v - 1

/-- A `VertexStar` index converted to the corresponding degree-list index. -/
def starIndexToDeg (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : Fin (vDeg P v) :=
  ⟨i.1, by
    have hi := i.2
    unfold starN at hi
    omega⟩

/-- The `i`-th incident dart, indexed in the eventual `VertexStar` convention. -/
def incidentDartOfStarIndex (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : D :=
  incidentDart P v (starIndexToDeg P v hdeg i)

theorem incidentDartOfStarIndex_tail (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    M.tail (incidentDartOfStarIndex P v hdeg i) = v := by
  unfold incidentDartOfStarIndex
  exact incidentDart_tail P v (starIndexToDeg P v hdeg i)

theorem starN_add_one_eq_vDeg (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) :
    starN P v + 1 = vDeg P v := by
  unfold starN
  omega

def incidentIndexOfDart (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (d : D) (hd : d ∈ incidentDarts P v) : Fin (vDeg P v) :=
  ⟨(incidentDarts P v).idxOf d, by
    unfold vDeg
    exact List.idxOf_lt_length_iff.mpr hd⟩

theorem incidentDart_incidentIndexOfDart
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (d : D) (hd : d ∈ incidentDarts P v) :
    incidentDart P v (incidentIndexOfDart P v d hd) = d := by
  unfold incidentDart incidentIndexOfDart
  exact List.idxOf_get (List.idxOf_lt_length_iff.mpr hd)

def reverseStarIndexOfDart (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (d : D) (hd : d ∈ incidentDarts P v) :
    Fin (starN P v + 1) :=
  Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm
    (incidentIndexOfDart P v d hd))

theorem incidentDartOfStarIndex_reverseStarIndexOfDart
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (d : D) (hd : d ∈ incidentDarts P v) :
    incidentDartOfStarIndex P v hdeg
      (Fin.rev (reverseStarIndexOfDart P v hdeg d hd)) = d := by
  unfold reverseStarIndexOfDart incidentDartOfStarIndex starIndexToDeg
  simpa [Fin.rev_rev, Fin.cast_trans, Fin.cast_eq_self] using
    incidentDart_incidentIndexOfDart P v d hd

/-- The cyclic step `1` in the eventual vertex-star index type. -/
def starOne (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) : Fin (starN P v + 1) :=
  ⟨1, by
    unfold starN
    omega⟩

theorem incidentDartOfStarIndex_reverseStarIndexOfDart_add_one
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (d : D) (hd : d ∈ incidentDarts P v) :
    incidentDartOfStarIndex P v hdeg
      (Fin.rev (reverseStarIndexOfDart P v hdeg d hd + starOne P v hdeg)) = M.σ.symm d := by
  set root : D := Quotient.out v
  set L : List D := incidentDarts P v
  set N : ℕ := vDeg P v
  set k : ℕ := L.idxOf d
  have hL : L = M.σ.toList root := by
    simp [L, incidentDarts, root]
  have hN : N = L.length := by
    simp [N, vDeg, L]
  have hNpos : 0 < N := by
    have := hdeg
    omega
  have hklt : k < N := by
    rw [hN]
    exact List.idxOf_lt_length_iff.mpr (by simpa [L] using hd)
  have hroot_support : root ∈ M.σ.support := by
    have hmem : d ∈ M.σ.toList root := by simpa [hL] using (by simpa [L] using hd)
    exact (Equiv.Perm.mem_toList_iff.mp hmem).2
  have hcard : (M.σ.cycleOf root).support.card = N := by
    rw [← Equiv.Perm.length_toList M.σ root, ← hL, hN]
  have hd_pow : d = (M.σ ^ k) root := by
    have hkltL : k < L.length := by rwa [← hN]
    have hget_idx : L.get ⟨k, hkltL⟩ = d := by
      simpa [k] using List.idxOf_get hkltL
    have hget_pow :
        L.get ⟨k, hkltL⟩ = (M.σ ^ k) root := by
      simpa [hL] using Equiv.Perm.getElem_toList M.σ root k (by simpa [hL] using hkltL)
    exact hget_idx.symm.trans hget_pow
  apply M.σ.injective
  rw [Equiv.apply_symm_apply]
  unfold incidentDartOfStarIndex incidentDart starIndexToDeg reverseStarIndexOfDart
  set j : Fin N := incidentIndexOfDart P v d hd
  have hjval : j.val = k := by
    simp [j, incidentIndexOfDart, k, L]
  have hN3 : 3 ≤ N := hdeg
  have hval :
      ((starIndexToDeg P v hdeg
        (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
          + starOne P v hdeg))) : ℕ) = (k + N - 1) % N := by
    unfold starIndexToDeg starOne
    have hrev :
        (((Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
          + ⟨1, by unfold starN; omega⟩)) :
            Fin (starN P v + 1)) : ℕ)
          =
        (((Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j).val + (starN P v + 1) - 1)
          % (starN P v + 1)) :=
      rev_add_one_rev_val (by unfold starN; omega)
        (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
    rw [hrev]
    simp [hjval, starN_add_one_eq_vDeg P v hdeg, N]
  have hget :
      (incidentDarts P v).get
        (starIndexToDeg P v hdeg
          (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
            + starOne P v hdeg))) =
        (M.σ ^ ((k + N - 1) % N)) root := by
    have hget0 := Equiv.Perm.getElem_toList M.σ root
      ((starIndexToDeg P v hdeg
        (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
          + starOne P v hdeg))) : ℕ)
      (by
        have hlt := (starIndexToDeg P v hdeg
          (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
            + starOne P v hdeg))).2
        have hlenTo : (M.σ.toList root).length = vDeg P v := by
          rw [← hL]
          simp [vDeg, L]
        simpa [hlenTo] using hlt)
    simpa [hL, hval] using hget0
  change M.σ ((incidentDarts P v).get
    (starIndexToDeg P v hdeg
      (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
        + starOne P v hdeg)))) = d
  rw [hget]
  change ((M.σ * (M.σ ^ ((k + N - 1) % N))) root) = d
  rw [← pow_succ']
  have hmod : (((k + N - 1) % N + 1) % (M.σ.cycleOf root).support.card) = k := by
    rw [hcard]
    exact prev_mod_succ_mod hNpos hklt
  calc
    (M.σ ^ (((k + N - 1) % N) + 1)) root
        = (M.σ ^ ((((k + N - 1) % N) + 1) % (M.σ.cycleOf root).support.card)) root := by
            rw [Equiv.Perm.pow_mod_card_support_cycleOf_self_apply]
    _ = (M.σ ^ k) root := by rw [hmod]
    _ = d := hd_pow.symm

theorem incidentDartOfStarIndex_reverseStarIndexOfDart_sub_one
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (d : D) (hd : d ∈ incidentDarts P v) :
    incidentDartOfStarIndex P v hdeg
      (Fin.rev (reverseStarIndexOfDart P v hdeg d hd - starOne P v hdeg)) = M.σ d := by
  set root : D := Quotient.out v
  set L : List D := incidentDarts P v
  set N : ℕ := vDeg P v
  set k : ℕ := L.idxOf d
  have hL : L = M.σ.toList root := by
    simp [L, incidentDarts, root]
  have hN : N = L.length := by
    simp [N, vDeg, L]
  have hklt : k < N := by
    rw [hN]
    exact List.idxOf_lt_length_iff.mpr (by simpa [L] using hd)
  have hcard : (M.σ.cycleOf root).support.card = N := by
    rw [← Equiv.Perm.length_toList M.σ root, ← hL, hN]
  have hd_pow : d = (M.σ ^ k) root := by
    have hkltL : k < L.length := by rwa [← hN]
    have hget_idx : L.get ⟨k, hkltL⟩ = d := by
      simpa [k] using List.idxOf_get hkltL
    have hget_pow :
        L.get ⟨k, hkltL⟩ = (M.σ ^ k) root := by
      simpa [hL] using Equiv.Perm.getElem_toList M.σ root k (by simpa [hL] using hkltL)
    exact hget_idx.symm.trans hget_pow
  unfold incidentDartOfStarIndex incidentDart starIndexToDeg reverseStarIndexOfDart
  set j : Fin N := incidentIndexOfDart P v d hd
  have hjval : j.val = k := by
    simp [j, incidentIndexOfDart, k, L]
  have hval :
      ((starIndexToDeg P v hdeg
        (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
          - starOne P v hdeg))) : ℕ) = (k + 1) % N := by
    unfold starIndexToDeg starOne
    have hrev :
        (((Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
          - ⟨1, by unfold starN; omega⟩)) :
            Fin (starN P v + 1)) : ℕ)
          =
        (((Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j).val + 1)
          % (starN P v + 1)) :=
      rev_sub_one_rev_val (by unfold starN; omega)
        (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
    rw [hrev]
    simp [hjval, starN_add_one_eq_vDeg P v hdeg, N]
  have hget :
      (incidentDarts P v).get
        (starIndexToDeg P v hdeg
          (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
            - starOne P v hdeg))) =
        (M.σ ^ ((k + 1) % N)) root := by
    have hget0 := Equiv.Perm.getElem_toList M.σ root
      ((starIndexToDeg P v hdeg
        (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
          - starOne P v hdeg))) : ℕ)
      (by
        have hlt := (starIndexToDeg P v hdeg
          (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
            - starOne P v hdeg))).2
        have hlenTo : (M.σ.toList root).length = vDeg P v := by
          rw [← hL]
          simp [vDeg, L]
        simpa [hlenTo] using hlt)
    simpa [hL, hval] using hget0
  change (incidentDarts P v).get
    (starIndexToDeg P v hdeg
      (Fin.rev (Fin.rev (Fin.cast (starN_add_one_eq_vDeg P v hdeg).symm j)
        - starOne P v hdeg))) = M.σ d
  rw [hget]
  calc
    (M.σ ^ ((k + 1) % N)) root
        = (M.σ ^ ((k + 1) % (M.σ.cycleOf root).support.card)) root := by rw [hcard]
    _ = (M.σ ^ (k + 1)) root := by
          rw [Equiv.Perm.pow_mod_card_support_cycleOf_self_apply]
    _ = M.σ d := by
          rw [hd_pow]
          rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]





theorem starN_ge_two (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) : 2 ≤ starN P v := by
  unfold starN
  omega



theorem incidentDartOfStarIndex_injective
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) :
    Function.Injective (incidentDartOfStarIndex P v hdeg) := by
  intro i j hij
  have hnodup : (incidentDarts P v).Nodup := by
    unfold incidentDarts
    exact Equiv.Perm.nodup_toList M.σ (Quotient.out v)
  unfold incidentDartOfStarIndex incidentDart at hij
  have hidx :=
    (List.Nodup.getElem_inj_iff hnodup).mp hij
  exact Fin.ext hidx

theorem dart_eq_of_same_tail_head_of_isSimpleGraph
    (hsimple : M.IsSimpleGraph) {d e : D}
    (htail : M.tail d = M.tail e) (hhead : M.head d = M.head e) :
    d = e := by
  have hsc : M.α.SameCycle d e :=
    M.alpha_sameCycle_of_same_endpoints hsimple htail hhead
  rcases (M.alpha_sameCycle_iff d e).mp hsc with heq | halpha
  · exact heq.symm
  · exfalso
    apply hsimple.no_loop d
    have hloop : M.tail d = M.head d := by
      calc
        M.tail d = M.tail e := htail
        _ = M.tail (M.α d) := by rw [halpha]
        _ = M.head d := M.tail_alpha d
    exact hloop

/-- The dart read by the Euclidean bridge's reverse-`σ` link order. -/
def reverseLinkDart (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : D :=
  incidentDartOfStarIndex P v hdeg (Fin.rev i)

/-- The neighbour read by the Euclidean bridge's reverse-`σ` link order. -/
def reverseLinkNbr (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : M.Vertex :=
  M.head (reverseLinkDart P v hdeg i)

theorem reverseLinkDart_tail (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    M.tail (reverseLinkDart P v hdeg i) = v := by
  exact incidentDartOfStarIndex_tail P v hdeg (Fin.rev i)

theorem reverseLinkDart_mem_incident (P : TriangulatedEuclideanPolyhedron M)
    (v : M.Vertex) (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    reverseLinkDart P v hdeg i ∈ incidentDarts P v := by
  unfold reverseLinkDart incidentDartOfStarIndex incidentDart
  exact List.get_mem _ _

theorem reverseLinkNbr_apex_ne (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    P.pos (reverseLinkNbr P v hdeg i) ≠ P.pos v := by
  intro h
  exact P.edge_nondegenerate (reverseLinkDart P v hdeg i) (by
    rw [reverseLinkDart_tail P v hdeg i]
    exact h.symm)

theorem reverseLinkDart_injective (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) :
    Function.Injective (reverseLinkDart P v hdeg) := by
  intro i j h
  have hidx := incidentDartOfStarIndex_injective P v hdeg h
  exact Fin.rev_injective hidx

theorem reverseLinkDart_add_one (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    reverseLinkDart P v hdeg (i + 1) = M.σ.symm (reverseLinkDart P v hdeg i) := by
  let d := reverseLinkDart P v hdeg i
  have hdmem : d ∈ incidentDarts P v := by
    simpa [d] using reverseLinkDart_mem_incident P v hdeg i
  have hidx : reverseStarIndexOfDart P v hdeg d hdmem = i := by
    have hbase :=
      incidentDartOfStarIndex_reverseStarIndexOfDart P v hdeg d hdmem
    have hsame :
        incidentDartOfStarIndex P v hdeg
            (Fin.rev (reverseStarIndexOfDart P v hdeg d hdmem)) =
          incidentDartOfStarIndex P v hdeg (Fin.rev i) := by
      simpa [d, reverseLinkDart] using hbase
    have hrev := incidentDartOfStarIndex_injective P v hdeg hsame
    exact Fin.rev_injective hrev
  have hstep :=
    incidentDartOfStarIndex_reverseStarIndexOfDart_add_one P v hdeg d hdmem
  have hidx_add :
      reverseStarIndexOfDart P v hdeg d hdmem + starOne P v hdeg = i + 1 := by
    rw [hidx]
    apply Fin.ext
    simp [Fin.add_def, starOne]
  rw [hidx_add] at hstep
  simpa [reverseLinkDart, d] using hstep

theorem reverseLinkNbr_add_one (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    reverseLinkNbr P v hdeg (i + 1) =
      M.head (M.σ.symm (reverseLinkDart P v hdeg i)) := by
  unfold reverseLinkNbr
  rw [reverseLinkDart_add_one P v hdeg i]

theorem reverseLinkNbr_eq_apex_false_of_simple
    (P : TriangulatedEuclideanPolyhedron M) (hsimple : M.IsSimpleGraph)
    (v : M.Vertex) (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    reverseLinkNbr P v hdeg i ≠ v := by
  intro h
  exact hsimple.no_loop (reverseLinkDart P v hdeg i)
    ((reverseLinkDart_tail P v hdeg i).trans h.symm)

theorem reverseLinkNbr_injective_of_simple
    (P : TriangulatedEuclideanPolyhedron M) (hsimple : M.IsSimpleGraph)
    (v : M.Vertex) (hdeg : 3 ≤ vDeg P v) :
    Function.Injective (reverseLinkNbr P v hdeg) := by
  intro i j hhead
  have hdart : reverseLinkDart P v hdeg i = reverseLinkDart P v hdeg j :=
    dart_eq_of_same_tail_head_of_isSimpleGraph hsimple
      ((reverseLinkDart_tail P v hdeg i).trans (reverseLinkDart_tail P v hdeg j).symm)
      hhead
  exact reverseLinkDart_injective P v hdeg hdart

theorem reverseLink_nonincident_of_simple
    (P : TriangulatedEuclideanPolyhedron M) (hsimple : M.IsSimpleGraph)
    (v : M.Vertex) (hdeg : 3 ≤ vDeg P v) :
    ∀ i j : Fin (starN P v + 1), j ≠ i → j ≠ i + 1 →
      ¬(reverseLinkNbr P v hdeg j = v ∨
        reverseLinkNbr P v hdeg j = reverseLinkNbr P v hdeg i ∨
        reverseLinkNbr P v hdeg j = reverseLinkNbr P v hdeg (i + 1)) := by
  intro i j hji hjnext hbad
  rcases hbad with hapex | heq | hnext
  · exact reverseLinkNbr_eq_apex_false_of_simple P hsimple v hdeg j hapex
  · exact hji (reverseLinkNbr_injective_of_simple P hsimple v hdeg heq)
  · exact hjnext (reverseLinkNbr_injective_of_simple P hsimple v hdeg hnext)



theorem exists_fin_not_incident_edge {n : ℕ} (hn : 2 ≤ n) (i : Fin (n + 1)) :
    ∃ j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin (n + 1))) ⊆ {i, i + 1} := by
    intro j _
    by_cases hji : j = i
    · simp [hji]
    · have hjnext := hcon j hji
      simp [hjnext]
  have hle := Finset.card_le_card hsub
  have hcard : ({i, i + 1} : Finset (Fin (n + 1))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hle2 : n + 1 ≤ 2 := le_trans hle hcard
  omega



/-- Local scalar triple product, in the same coordinate convention as `SphericalKernel.det3`. -/
def det3 (u v w : E3) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1)
    - u 1 * (v 0 * w 2 - v 2 * w 0)
    + u 2 * (v 0 * w 1 - v 1 * w 0)

theorem det3_eq_spherical (u v w : E3) :
    det3 u v w = ProofsInTheBook.SphericalKernel.det3 u v w := rfl

theorem det3_eq_inner_cross (u v z : E3) :
    det3 u v z = (⟪cross u v, z⟫ : ℝ) := by
  rw [det3_eq_spherical]
  calc
    ProofsInTheBook.SphericalKernel.det3 u v z = (⟪u, cross v z⟫ : ℝ) := by
      rw [inner_cross_eq_det3]
    _ = (⟪z, cross u v⟫ : ℝ) := inner_cross_cyclic u v z
    _ = (⟪cross u v, z⟫ : ℝ) := (real_inner_comm z (cross u v)).symm





 theorem faceDart_phi_ne_self_link
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    M.φ (P.faceDart f) ≠ P.faceDart f := by
  intro h
  let p : Fin 3 → E3 :=
    ![P.pos (M.tail (P.faceDart f)),
      P.pos (M.tail (M.φ (P.faceDart f))),
      P.pos (M.tail (M.φ (M.φ (P.faceDart f))))]
  have hinj : Function.Injective p := (P.face_nondegenerate f).injective
  have hpts : p 1 = p 0 := by
    simp [p, h]
  have h10 : (1 : Fin 3) = 0 := hinj hpts
  norm_num at h10

 theorem faceDart_phi_cube_eq_self
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    (M.φ ^ 3) (P.faceDart f) = P.faceDart f := by
  let fd := P.faceDart f
  have hφne : M.φ fd ≠ fd := by
    simpa [fd] using faceDart_phi_ne_self_link P f
  have hlen : M.faceLen f = 3 := by
    simpa [CombMap.faceLen] using P.every_face_triangle f
  have hcard : (M.φ.cycleOf fd).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφne]
    simpa [fd, P.faceDart_face f] using hlen
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ 3 fd
  rw [hcard, Nat.mod_self] at hpow
  simpa [fd] using hpow.symm

theorem phi_cube_eq_self_of_triangular_euclidean
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    (M.φ ^ 3) d = d := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq
      P (f := M.dartFace d) (d := d) rfl with h | h | h
  · rw [h]
    exact faceDart_phi_cube_eq_self P (M.dartFace d)
  · rw [h]
    exact congrArg M.φ (faceDart_phi_cube_eq_self P (M.dartFace d))
  · rw [h]
    exact congrArg (fun x => M.φ (M.φ x))
      (faceDart_phi_cube_eq_self P (M.dartFace d))

theorem tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d) := by
  have hcube := phi_cube_eq_self_of_triangular_euclidean P d
  have hpred : M.φ (M.φ d) = M.φ.symm d := by
    apply M.φ.injective
    rw [Equiv.apply_symm_apply]
    simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
  have hsymm : M.φ.symm d = M.α (M.σ.symm d) := by
    apply M.φ.injective
    rw [Equiv.apply_symm_apply]
    symm
    change (M.σ * M.α) (M.α (M.σ.symm d)) = d
    rw [Equiv.Perm.mul_apply, M.alpha_alpha, Equiv.apply_symm_apply]
  rw [hpred, hsymm, M.tail_alpha]

/-- The stored face vertices are the three tails of any dart on the same
triangular face, up to cyclic rotation. -/
theorem faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
    (P : TriangulatedEuclideanPolyhedron M) {f : M.Face} {e : D}
    (he : M.dartFace e = f) (k : Fin 3) :
    P.faceVertex f k = M.tail e ∨
      P.faceVertex f k = M.head e ∨
      P.faceVertex f k = M.tail (M.φ (M.φ e)) := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq P (f := f) (d := e) he with
    h | h | h
  · subst h
    fin_cases k
    · left
      have hv := congrFun (P.face_vertices_match f) 0
      simpa using hv
    · right; left
      have hv := congrFun (P.face_vertices_match f) 1
      simpa [M.tail_phi] using hv
    · right; right
      have hv := congrFun (P.face_vertices_match f) 2
      simpa using hv
  · subst h
    fin_cases k
    · right; right
      have hv := congrFun (P.face_vertices_match f) 0
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (P.faceDart f) =
          M.tail (M.φ (M.φ (M.φ (P.faceDart f)))) := by
        rw [hcube']
      exact hv.trans htail
    · left
      have hv := congrFun (P.face_vertices_match f) 1
      simpa [M.tail_phi] using hv
    · right; left
      have hv := congrFun (P.face_vertices_match f) 2
      simpa [M.tail_phi] using hv
  · subst h
    fin_cases k
    · right; left
      have hv := congrFun (P.face_vertices_match f) 0
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (P.faceDart f) =
          M.head (M.φ (M.φ (P.faceDart f))) := by
        rw [← M.tail_phi (M.φ (M.φ (P.faceDart f))), hcube']
      exact hv.trans htail
    · right; right
      have hv := congrFun (P.face_vertices_match f) 1
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (M.φ (P.faceDart f)) =
          M.tail (M.φ (M.φ (M.φ (M.φ (P.faceDart f))))) := by
        rw [hcube']
      exact hv.trans htail
    · left
      have hv := congrFun (P.face_vertices_match f) 2
      simpa using hv



theorem reverseFaceBetween_support_edgeVec_lt
    (P : TriangulatedEuclideanPolyhedron M) (d e : D)
    (he_tail : M.tail e = M.tail d)
    (hoff : ∀ i, M.head e ≠ P.faceVertex (reverseFaceBetween M d) i) :
    inner ℝ (P.outward_normal (reverseFaceBetween M d)) (edgeVec P e) < 0 := by
  have htail_plane :
      inner ℝ (P.outward_normal (M.dartFace d))
        (P.pos (M.tail d) - P.face_point (M.dartFace d)) = 0 :=
    face_plane_dart P d
  have hstrict := P.face_support_strict (M.dartFace d) (M.head e) (by
    simpa [reverseFaceBetween] using hoff)
  have hrewrite :
      inner ℝ (P.outward_normal (M.dartFace d))
        (P.pos (M.head e) - P.pos (M.tail e))
        =
      inner ℝ (P.outward_normal (M.dartFace d))
        (P.pos (M.head e) - P.face_point (M.dartFace d))
        -
      inner ℝ (P.outward_normal (M.dartFace d))
        (P.pos (M.tail d) - P.face_point (M.dartFace d)) := by
    rw [he_tail]
    calc
      inner ℝ (P.outward_normal (M.dartFace d))
          (P.pos (M.head e) - P.pos (M.tail d))
          =
        inner ℝ (P.outward_normal (M.dartFace d))
          ((P.pos (M.head e) - P.face_point (M.dartFace d))
            - (P.pos (M.tail d) - P.face_point (M.dartFace d))) := by
            congr 1
            module
      _ =
        inner ℝ (P.outward_normal (M.dartFace d))
          (P.pos (M.head e) - P.face_point (M.dartFace d))
          -
        inner ℝ (P.outward_normal (M.dartFace d))
          (P.pos (M.tail d) - P.face_point (M.dartFace d)) := by
            rw [inner_sub_right]
  simpa [reverseFaceBetween, edgeVec, hrewrite, htail_plane] using hstrict



/--
Strict face support plus reverse-`σ` rotation faithfulness gives strict
determinant positivity once the tested vertex is off the supporting triangle.
-/
theorem link_side_strict_of_rotationFaithful
    (P : TriangulatedEuclideanPolyhedron M) (hfaith : RotationFaithful P)
    (d e : D) (he_tail : M.tail e = M.tail d)
    (hoff : ∀ i, M.head e ≠ P.faceVertex (reverseFaceBetween M d) i) :
    0 < det3 (edgeVec P d) (edgeVec P (M.σ.symm d)) (edgeVec P e) := by
  obtain ⟨lam, hlam, hnormal⟩ :=
    hfaith.outward_normal_eq_pos_smul_reverse_cross d
  have hs := reverseFaceBetween_support_edgeVec_lt P d e he_tail hoff
  rw [hnormal, real_inner_smul_left] at hs
  have hcross :
      inner ℝ (cross (edgeVec P (M.σ.symm d)) (edgeVec P d)) (edgeVec P e) < 0 := by
    nlinarith
  rw [det3_eq_inner_cross, cross_antisymm, inner_neg_left]
  nlinarith

theorem face_support_from_dart_tail
    (P : TriangulatedEuclideanPolyhedron M) (d : D) (w : M.Vertex) :
    inner ℝ (P.outward_normal (M.dartFace d)) (P.pos w - P.pos (M.tail d)) ≤ 0 := by
  have htail_plane := face_plane_dart P d
  have hsupport := P.face_supporting_halfspace (M.dartFace d) w
  have hrewrite :
      inner ℝ (P.outward_normal (M.dartFace d)) (P.pos w - P.pos (M.tail d)) =
        inner ℝ (P.outward_normal (M.dartFace d)) (P.pos w - P.face_point (M.dartFace d)) -
          inner ℝ (P.outward_normal (M.dartFace d))
            (P.pos (M.tail d) - P.face_point (M.dartFace d)) := by
    calc
      inner ℝ (P.outward_normal (M.dartFace d)) (P.pos w - P.pos (M.tail d))
          = inner ℝ (P.outward_normal (M.dartFace d))
              ((P.pos w - P.face_point (M.dartFace d)) -
                (P.pos (M.tail d) - P.face_point (M.dartFace d))) := by
                congr 1
                module
      _ = inner ℝ (P.outward_normal (M.dartFace d)) (P.pos w - P.face_point (M.dartFace d)) -
            inner ℝ (P.outward_normal (M.dartFace d))
              (P.pos (M.tail d) - P.face_point (M.dartFace d)) := by
            rw [inner_sub_right]
  rw [hrewrite, htail_plane, sub_zero]
  exact hsupport

theorem face_plane_head_sub_tail
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    inner ℝ (P.outward_normal (M.dartFace d))
      (P.pos (M.head d) - P.pos (M.tail d)) = 0 := by
  have htail := face_plane_dart P d
  have hhead0 := face_plane_dart P (M.φ d)
  have hhead :
      inner ℝ (P.outward_normal (M.dartFace d))
        (P.pos (M.head d) - P.face_point (M.dartFace d)) = 0 := by
    simpa [M.tail_phi] using hhead0
  calc
    inner ℝ (P.outward_normal (M.dartFace d))
        (P.pos (M.head d) - P.pos (M.tail d))
        = inner ℝ (P.outward_normal (M.dartFace d))
            ((P.pos (M.head d) - P.face_point (M.dartFace d)) -
              (P.pos (M.tail d) - P.face_point (M.dartFace d))) := by
              congr 1
              module
    _ = inner ℝ (P.outward_normal (M.dartFace d))
          (P.pos (M.head d) - P.face_point (M.dartFace d)) -
        inner ℝ (P.outward_normal (M.dartFace d))
          (P.pos (M.tail d) - P.face_point (M.dartFace d)) := by
          rw [inner_sub_right]
    _ = 0 := by rw [hhead, htail, sub_self]

theorem face_plane_head_sigma_symm_sub_tail
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    inner ℝ (P.outward_normal (M.dartFace d))
      (P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d)) = 0 := by
  have htail := face_plane_dart P d
  have hhead0 := face_plane_dart P (M.φ (M.φ d))
  have htail_phi2 := tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P d
  have hhead :
      inner ℝ (P.outward_normal (M.dartFace d))
        (P.pos (M.head (M.σ.symm d)) - P.face_point (M.dartFace d)) = 0 := by
    simpa [htail_phi2] using hhead0
  calc
    inner ℝ (P.outward_normal (M.dartFace d))
        (P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d))
        = inner ℝ (P.outward_normal (M.dartFace d))
            ((P.pos (M.head (M.σ.symm d)) - P.face_point (M.dartFace d)) -
              (P.pos (M.tail d) - P.face_point (M.dartFace d))) := by
              congr 1
              module
    _ = inner ℝ (P.outward_normal (M.dartFace d))
          (P.pos (M.head (M.σ.symm d)) - P.face_point (M.dartFace d)) -
        inner ℝ (P.outward_normal (M.dartFace d))
          (P.pos (M.tail d) - P.face_point (M.dartFace d)) := by
          rw [inner_sub_right]
    _ = 0 := by rw [hhead, htail, sub_self]

/--
An oriented supporting triangle through `v,a,b`.

This is the non-circular local geometry: the determinant functional of the
oriented triangle is identified with a supporting face normal, with a positive
scale and exact equality set.
-/
structure OrientedTriangleSupport (P : TriangulatedEuclideanPolyhedron M)
    (v a b : M.Vertex) where
  normal : E3
  normal_unit : ‖normal‖ = 1
  c : ℝ
  c_pos : 0 < c
  det_eq :
    ∀ z : E3,
      det3 (P.pos a - P.pos v) (P.pos b - P.pos v) z = -c * inner ℝ normal z
  support : ∀ w : M.Vertex, inner ℝ normal (P.pos w - P.pos v) ≤ 0
  eq_iff :
    ∀ w : M.Vertex,
      inner ℝ normal (P.pos w - P.pos v) = 0 ↔ (w = v ∨ w = a ∨ w = b)

noncomputable def orientedTriangleSupport_of_rotationFaithful
    (P : TriangulatedEuclideanPolyhedron M) (hfaith : RotationFaithful P)
    (d e : D) (he_tail : M.tail e = M.tail d)
    (hoff : ∀ i, M.head e ≠ P.faceVertex (M.dartFace d) i) :
    OrientedTriangleSupport P (M.tail d) (M.head d) (M.head (M.σ.symm d)) := by
  classical
  let N : E3 := P.outward_normal (M.dartFace d)
  let rot := hfaith.outward_normal_eq_pos_smul_reverse_cross d
  let lam : ℝ := Classical.choose rot
  have hlam : 0 < lam := (Classical.choose_spec rot).1
  have hnormal :
      P.outward_normal (reverseFaceBetween M d) =
        lam • cross (edgeVec P (M.σ.symm d)) (edgeVec P d) :=
    (Classical.choose_spec rot).2
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hdetpos :
      0 < det3 (edgeVec P d) (edgeVec P (M.σ.symm d)) (edgeVec P e) :=
    link_side_strict_of_rotationFaithful P hfaith d e he_tail (by
      simpa [reverseFaceBetween] using hoff)
  have hNne : N ≠ 0 := by
    intro hNzero
    have hprev0 : cross (edgeVec P (M.σ.symm d)) (edgeVec P d) = 0 := by
      have hsmul : lam • cross (edgeVec P (M.σ.symm d)) (edgeVec P d) = 0 := by
        rw [← hnormal]
        exact hNzero
      rcases smul_eq_zero.mp hsmul with hlam0 | hcross0
      · exact False.elim (hlam_ne hlam0)
      · exact hcross0
    have hcross0 : cross (edgeVec P d) (edgeVec P (M.σ.symm d)) = 0 := by
      rw [cross_antisymm, hprev0, neg_zero]
    have hdet0 : det3 (edgeVec P d) (edgeVec P (M.σ.symm d)) (edgeVec P e) = 0 := by
      rw [det3_eq_inner_cross, hcross0, inner_zero_left]
    nlinarith
  have hnorm_pos : 0 < ‖N‖ := norm_pos_iff.mpr hNne
  have hnorm_ne : ‖N‖ ≠ 0 := ne_of_gt hnorm_pos
  refine
    { normal := (‖N‖)⁻¹ • N
      normal_unit := ?_
      c := ‖N‖ * lam⁻¹
      c_pos := ?_
      det_eq := ?_
      support := ?_
      eq_iff := ?_ }
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg N))]
    exact inv_mul_cancel₀ hnorm_ne
  · exact mul_pos hnorm_pos (inv_pos.mpr hlam)
  · intro z
    rw [det3_eq_inner_cross]
    have hprev :
        cross (edgeVec P (M.σ.symm d)) (edgeVec P d) = lam⁻¹ • N := by
      have hN :
          N = lam • cross (edgeVec P (M.σ.symm d)) (edgeVec P d) := by
        simpa [N, reverseFaceBetween] using hnormal
      rw [hN]
      rw [smul_smul]
      rw [inv_mul_cancel₀ hlam_ne, one_smul]
    have hcross :
        cross (edgeVec P d) (edgeVec P (M.σ.symm d)) = -(lam⁻¹) • N := by
      rw [cross_antisymm, hprev, neg_smul]
    have htail_symm : M.tail (M.σ.symm d) = M.tail d := by
      rw [← M.tail_sigma (M.σ.symm d), Equiv.apply_symm_apply]
    have hcross' :
        cross (P.pos (M.head d) - P.pos (M.tail d))
            (P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d)) =
          -(lam⁻¹) • N := by
      simpa [edgeVec, htail_symm] using hcross
    rw [hcross', real_inner_smul_left, real_inner_smul_left]
    field_simp [hlam_ne, hnorm_ne]
  · intro w
    have hs := face_support_from_dart_tail P d w
    rw [real_inner_smul_left]
    have hnonneg : 0 ≤ (‖N‖)⁻¹ := inv_nonneg.mpr (norm_nonneg N)
    nlinarith
  · intro w
    constructor
    · intro hz
      have hNzero :
          inner ℝ N (P.pos w - P.pos (M.tail d)) = 0 := by
        rw [real_inner_smul_left] at hz
        exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (inv_pos.mpr hnorm_pos))
      by_cases hgoal :
          w = M.tail d ∨ w = M.head d ∨ w = M.head (M.σ.symm d)
      · exact hgoal
      · exfalso
        push_neg at hgoal
        have hnotFace : ∀ k, w ≠ P.faceVertex (M.dartFace d) k := by
          intro k hw
          have hcases :=
            faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq P (e := d) rfl k
          rw [← hw] at hcases
          rcases hcases with htail | hhead | hphi2
          · exact hgoal.1 htail
          · exact hgoal.2.1 hhead
          · have htail_phi2 := tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P d
            exact hgoal.2.2 (hphi2.trans htail_phi2)
        have hstrict0 := P.face_support_strict (M.dartFace d) w hnotFace
        have htail_plane := face_plane_dart P d
        have hstrict :
            inner ℝ N (P.pos w - P.pos (M.tail d)) < 0 := by
          have hrewrite :
              inner ℝ N (P.pos w - P.pos (M.tail d)) =
                inner ℝ N (P.pos w - P.face_point (M.dartFace d)) -
                  inner ℝ N (P.pos (M.tail d) - P.face_point (M.dartFace d)) := by
            calc
              inner ℝ N (P.pos w - P.pos (M.tail d))
                  = inner ℝ N
                      ((P.pos w - P.face_point (M.dartFace d)) -
                        (P.pos (M.tail d) - P.face_point (M.dartFace d))) := by
                        congr 1
                        module
              _ = inner ℝ N (P.pos w - P.face_point (M.dartFace d)) -
                    inner ℝ N (P.pos (M.tail d) - P.face_point (M.dartFace d)) := by
                    rw [inner_sub_right]
          rw [hrewrite, htail_plane, sub_zero]
          exact hstrict0
        nlinarith
    · rintro (rfl | rfl | rfl)
      · simp
      · rw [real_inner_smul_left, face_plane_head_sub_tail P d, mul_zero]
      · rw [real_inner_smul_left, face_plane_head_sigma_symm_sub_tail P d, mul_zero]

/--
Local vertex-link geometry in the outward-normal orientation, i.e. the reverse
of the map's `σ` order at the vertex.  The determinant and hemisphere fields of
`VertexStar` are derived from the oriented triangle supports below.
-/
structure VertexLinkGeometry (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) where
  n : ℕ
  hn : 2 ≤ n
  nbr : Fin (n + 1) → M.Vertex
  nbr_is_sigma :
    ∃ hdeg : 3 ≤ vDeg P v, ∃ e : n = starN P v,
      ∀ i : Fin (n + 1),
        nbr i =
          M.head (incidentDartOfStarIndex P v hdeg
            (Fin.rev (Fin.cast (by rw [← e]) i)))
  oriented : ∀ i : Fin (n + 1), OrientedTriangleSupport P v (nbr i) (nbr (i + 1))
  nbr_apex_ne : ∀ i : Fin (n + 1), P.pos (nbr i) ≠ P.pos v
  nonincident :
    ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      ¬(nbr j = v ∨ nbr j = nbr i ∨ nbr j = nbr (i + 1))

noncomputable def vertexLinkGeometryOfEuclidean
    (P : TriangulatedEuclideanPolyhedron M)
    (hfaith : RotationFaithful P) (hsimple : M.IsSimpleGraph)
    (v : M.Vertex) (hdeg : 3 ≤ vDeg P v) :
    VertexLinkGeometry P v := by
  classical
  refine
    { n := starN P v
      hn := starN_ge_two P v hdeg
      nbr := reverseLinkNbr P v hdeg
      nbr_is_sigma := ?_
      oriented := ?_
      nbr_apex_ne := reverseLinkNbr_apex_ne P v hdeg
      nonincident := reverseLink_nonincident_of_simple P hsimple v hdeg }
  · refine ⟨hdeg, rfl, ?_⟩
    intro i
    rfl
  · intro i
    let hex := exists_fin_not_incident_edge (starN_ge_two P v hdeg) i
    let j : Fin (starN P v + 1) := Classical.choose hex
    have hji : j ≠ i := (Classical.choose_spec hex).1
    have hjnext : j ≠ i + 1 := (Classical.choose_spec hex).2
    let d := reverseLinkDart P v hdeg i
    let e := reverseLinkDart P v hdeg j
    have he_tail : M.tail e = M.tail d := by
      simp [d, e, reverseLinkDart_tail P v hdeg j, reverseLinkDart_tail P v hdeg i]
    have hnonincident :=
      reverseLink_nonincident_of_simple P hsimple v hdeg i j hji hjnext
    have hoff : ∀ k, M.head e ≠ P.faceVertex (M.dartFace d) k := by
      intro k hk
      have hcases :=
        faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq P (e := d) rfl k
      apply hnonincident
      rcases hcases with htail | hhead | hphi2
      · left
        change M.head e = v
        calc
          M.head e = P.faceVertex (M.dartFace d) k := hk
          _ = M.tail d := htail
          _ = v := by simpa [d] using reverseLinkDart_tail P v hdeg i
      · right; left
        change M.head e = M.head d
        rw [hk, hhead]
      · right; right
        change M.head e = reverseLinkNbr P v hdeg (i + 1)
        calc
          M.head e = P.faceVertex (M.dartFace d) k := hk
          _ = M.tail (M.φ (M.φ d)) := hphi2
          _ = M.head (M.σ.symm d) :=
              tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P d
          _ = reverseLinkNbr P v hdeg (i + 1) := by
              simpa [d] using (reverseLinkNbr_add_one P v hdeg i).symm
    have hsupp := orientedTriangleSupport_of_rotationFaithful P hfaith d e he_tail hoff
    simpa [d, reverseLinkNbr, reverseLinkDart_tail P v hdeg i,
      reverseLinkDart_add_one P v hdeg i] using hsupp

namespace VertexLinkGeometry

variable {P : TriangulatedEuclideanPolyhedron M} {v : M.Vertex}
variable (LG : VertexLinkGeometry P v)

/-- Sum of oriented supporting normals around the vertex. -/
def normalSum : E3 :=
  ∑ i : Fin (LG.n + 1), (LG.oriented i).normal

theorem exists_nonincident (j : Fin (LG.n + 1)) :
    ∃ i : Fin (LG.n + 1), j ≠ i ∧ j ≠ i + 1 := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin (LG.n + 1))) ⊆ {j, j - 1} := by
    intro i _
    rcases eq_or_ne j i with hji | hji
    · simp [hji]
    · have hnext := hcon i hji
      have him1 : i = j - 1 := by
        rw [eq_sub_iff_add_eq]
        exact hnext.symm
      simp [him1]
  have hle := Finset.card_le_card hsub
  have hcard : ({j, j - 1} : Finset (Fin (LG.n + 1))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hle2 : LG.n + 1 ≤ 2 := le_trans hle hcard
  have hn : 2 ≤ LG.n := LG.hn
  omega

theorem normal_inner_nbr_lt (j : Fin (LG.n + 1)) :
    inner ℝ LG.normalSum (P.pos (LG.nbr j) - P.pos v) < 0 := by
  rw [normalSum, sum_inner]
  have hle :
      ∀ i ∈ (Finset.univ : Finset (Fin (LG.n + 1))),
        inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) ≤ 0 := by
    intro i _
    exact (LG.oriented i).support (LG.nbr j)
  have hlt :
      ∃ i ∈ (Finset.univ : Finset (Fin (LG.n + 1))),
        inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) < 0 := by
    obtain ⟨i, hji, hjnext⟩ := LG.exists_nonincident j
    refine ⟨i, by simp, ?_⟩
    have hle_i := (LG.oriented i).support (LG.nbr j)
    have hne :
        inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) ≠ 0 := by
      intro hz
      exact LG.nonincident i j hji hjnext (((LG.oriented i).eq_iff (LG.nbr j)).1 hz)
    exact lt_of_le_of_ne hle_i hne
  have hsum := Finset.sum_lt_sum hle hlt
  simpa using hsum

theorem normalSum_ne_zero : LG.normalSum ≠ 0 := by
  intro hzero
  have hlt := LG.normal_inner_nbr_lt (0 : Fin (LG.n + 1))
  rw [hzero] at hlt
  simp at hlt

theorem open_hemi :
    ∃ h : E3, ‖h‖ = 1 ∧
      ∀ i : Fin (LG.n + 1), 0 < inner ℝ h (P.pos (LG.nbr i) - P.pos v) := by
  let N := LG.normalSum
  have hN : N ≠ 0 := LG.normalSum_ne_zero
  refine ⟨-(‖N‖)⁻¹ • N, ?_, ?_⟩
  · rw [norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg N))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hN)
  · intro i
    have hlt : inner ℝ N (P.pos (LG.nbr i) - P.pos v) < 0 := LG.normal_inner_nbr_lt i
    rw [real_inner_smul_left]
    have hpos : 0 < (‖N‖)⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hN)
    nlinarith [mul_pos hpos (neg_pos.mpr hlt)]

theorem turn_support (i j : Fin (LG.n + 1)) :
    0 ≤ ProofsInTheBook.SphericalKernel.det3
      (P.pos (LG.nbr i) - P.pos v)
      (P.pos (LG.nbr (i + 1)) - P.pos v)
      (P.pos (LG.nbr j) - P.pos v) := by
  have hdet := (LG.oriented i).det_eq (P.pos (LG.nbr j) - P.pos v)
  rw [det3_eq_spherical] at hdet
  rw [hdet]
  have hs := (LG.oriented i).support (LG.nbr j)
  nlinarith [(LG.oriented i).c_pos, hs]

theorem turn_strict (i j : Fin (LG.n + 1)) (hji : j ≠ i) (hjnext : j ≠ i + 1) :
    0 < ProofsInTheBook.SphericalKernel.det3
      (P.pos (LG.nbr i) - P.pos v)
      (P.pos (LG.nbr (i + 1)) - P.pos v)
      (P.pos (LG.nbr j) - P.pos v) := by
  have hdet := (LG.oriented i).det_eq (P.pos (LG.nbr j) - P.pos v)
  rw [det3_eq_spherical] at hdet
  rw [hdet]
  have hs_le := (LG.oriented i).support (LG.nbr j)
  have hs_ne :
      inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) ≠ 0 := by
    intro hz
    exact LG.nonincident i j hji hjnext (((LG.oriented i).eq_iff (LG.nbr j)).1 hz)
  have hs_lt : inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) < 0 :=
    lt_of_le_of_ne hs_le hs_ne
  nlinarith [(LG.oriented i).c_pos, hs_lt]

/-- Assemble the `VertexStar` from honest local vertex-link geometry. -/
def toVertexStar : VertexStar where
  n := LG.n
  hn := LG.hn
  o := P.pos v
  p := fun i => P.pos (LG.nbr i)
  apex_ne := LG.nbr_apex_ne
  open_hemi := LG.open_hemi
  turn_support := LG.turn_support
  turn_strict := LG.turn_strict

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

/-- Compatibility abbreviation for assembly lemmas that already carry a `VertexLinkGeometry`. -/
 abbrev vertexStarOfEuclidean
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) : VertexStar :=
  LG.toVertexStar

/-- Projection of `u` to the tangent plane at a unit vector `v`. -/
def tangentToVec (v u : E3) : E3 :=
  u - (inner ℝ u v) • v

lemma eq_smul_axis_of_cross_zero_unit {k v : E3} (hk : ‖k‖ = 1) (h : cross k v = 0) :
    v = (⟪v, k⟫ : ℝ) • k := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hk]
    norm_num
  set t : E3 := v - (⟪v, k⟫ : ℝ) • k with ht
  have htk : (⟪t, k⟫ : ℝ) = 0 := by
    rw [ht, inner_sub_left, real_inner_smul_left, hkk, mul_one, sub_self]
  have hct : cross k t = 0 := by
    rw [ht, show v - (⟪v, k⟫ : ℝ) • k = v + (-(⟪v, k⟫ : ℝ)) • k by module,
      cross_add_right, cross_smul_right, cross_self, smul_zero, add_zero, h]
  have hkt : (⟪k, t⟫ : ℝ) = 0 := by
    rw [real_inner_comm]
    exact htk
  have hnorm : ‖t‖ ^ 2 = 0 := by
    have hl := norm_sq_cross k t
    rw [hct, norm_zero] at hl
    rw [hk, hkt] at hl
    nlinarith [hl]
  have : t = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
    exact norm_eq_zero.mp this
  rw [ht] at this
  linear_combination (norm := module) this

lemma cross_ne_zero_of_linearIndependent_pair {u v : E3}
    (hli : LinearIndependent ℝ ![u, v]) :
    cross u v ≠ 0 := by
  intro hcross
  have hu : u ≠ 0 := by
    intro hu0
    exact hli.ne_zero 0 (by simpa using hu0)
  have hnormu : ‖u‖ ≠ 0 := by
    simpa [norm_eq_zero] using hu
  set k : E3 := ‖u‖⁻¹ • u with hkdef
  have hk : ‖k‖ = 1 := by
    rw [hkdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnormu]
  have hkv : cross k v = 0 := by
    rw [hkdef, cross_smul_left, hcross, smul_zero]
  have hvk : v = (⟪v, k⟫ : ℝ) • k :=
    eq_smul_axis_of_cross_zero_unit hk hkv
  have hvu : v = ((⟪v, k⟫ : ℝ) * ‖u‖⁻¹) • u := by
    calc
      v = (⟪v, k⟫ : ℝ) • k := hvk
      _ = ((⟪v, k⟫ : ℝ) * ‖u‖⁻¹) • u := by
        rw [hkdef, smul_smul]
  have hcontra := ((LinearIndependent.pair_iff' (K := ℝ) (x := u) (y := v) hu).mp hli)
      (((⟪v, k⟫ : ℝ) * ‖u‖⁻¹))
  exact hcontra hvu.symm

lemma perp_two_imp_parallel_cross {u v n : E3}
    (hnu : (⟪n, u⟫ : ℝ) = 0) (hnv : (⟪n, v⟫ : ℝ) = 0)
    (hli : LinearIndependent ℝ ![u, v]) :
    ∃ s : ℝ, n = s • cross u v := by
  set X : E3 := cross u v with hXdef
  have hX : X ≠ 0 := by
    rw [hXdef]
    exact cross_ne_zero_of_linearIndependent_pair hli
  let s : ℝ := (⟪n, X⟫ : ℝ) / ‖X‖ ^ 2
  refine ⟨s, ?_⟩
  apply ProofsInTheBook.SphericalCongruence.eq_of_inner_frame_eq hX
  · have hux : (⟪u, cross u v⟫ : ℝ) = 0 := by
      rw [real_inner_comm]
      exact inner_cross_left u v
    rw [real_inner_smul_right, hXdef, hux, mul_zero]
    rw [real_inner_comm]
    exact hnu
  · have hvx : (⟪v, cross u v⟫ : ℝ) = 0 := by
      rw [real_inner_comm]
      exact inner_cross_right u v
    rw [real_inner_smul_right, hXdef, hvx, mul_zero]
    rw [real_inner_comm]
    exact hnv
  · have hcrossne : cross u v ≠ 0 := by
      rwa [← hXdef]
    rw [real_inner_smul_right, hXdef]
    change (⟪cross u v, n⟫ : ℝ) =
      s * (⟪cross u v, cross u v⟫ : ℝ)
    rw [show (⟪cross u v, n⟫ : ℝ) = ⟪n, cross u v⟫ by rw [real_inner_comm],
      real_inner_self_eq_norm_sq]
    unfold s
    have hnorm : ‖cross u v‖ ^ 2 ≠ 0 := by
      positivity
    field_simp [hnorm]
    ring





lemma inner_sub_of_plane_eq {normal point x y : E3}
    (hx : inner ℝ normal (x - point) = 0)
    (hy : inner ℝ normal (y - point) = 0) :
    inner ℝ normal (x - y) = 0 := by
  calc
    inner ℝ normal (x - y)
        = inner ℝ normal ((x - point) - (y - point)) := by
            congr 1
            module
    _ = inner ℝ normal (x - point) - inner ℝ normal (y - point) := by
            rw [inner_sub_right]
    _ = 0 := by rw [hx, hy, sub_self]

 theorem faceDart_phi_ne_self
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    M.φ (P.faceDart f) ≠ P.faceDart f := by
  intro h
  let p : Fin 3 → E3 :=
    ![P.pos (M.tail (P.faceDart f)),
      P.pos (M.tail (M.φ (P.faceDart f))),
      P.pos (M.tail (M.φ (M.φ (P.faceDart f))))]
  have hinj : Function.Injective p := (P.face_nondegenerate f).injective
  have hpts : p 1 = p 0 := by
    simp [p, h]
  have h10 : (1 : Fin 3) = 0 := hinj hpts
  norm_num at h10

/-- A dart on a triangular face is one of the three `φ`-successive darts from the
stored representative of that face. -/
theorem dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) {f : M.Face} {d : D}
    (hd : M.dartFace d = f) :
    d = P.faceDart f ∨
      d = M.φ (P.faceDart f) ∨
      d = M.φ (M.φ (P.faceDart f)) := by
  let fd := P.faceDart f
  have hφne : M.φ fd ≠ fd := by
    simpa [fd] using faceDart_phi_ne_self P f
  have hlen : M.faceLen f = 3 := by
    simpa [CombMap.faceLen] using P.every_face_triangle f
  have hcard : (M.φ.cycleOf fd).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφne]
    simpa [fd, P.faceDart_face f] using hlen
  have hsame : M.φ.SameCycle fd d := by
    have hq : M.dartFace d = M.dartFace fd := by
      rw [hd, P.faceDart_face f]
    exact (Quotient.exact hq).symm
  have hsupp : fd ∈ M.φ.support := Equiv.Perm.mem_support.mpr hφne
  obtain ⟨i, hi, hpow⟩ := hsame.exists_pow_eq_of_mem_support hsupp
  rw [hcard] at hi
  interval_cases i
  · left
    simpa [fd] using hpow.symm
  · right
    left
    simpa [fd] using hpow.symm
  · right
    right
    simpa [fd, pow_succ] using hpow.symm

/-- Every dart tail is one of the three stored vertices of its dart face. -/
theorem tail_mem_faceVertex
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    ∃ k : Fin 3, M.tail d = P.faceVertex (M.dartFace d) k := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq P (f := M.dartFace d) (d := d) rfl with
    h | h | h
  · refine ⟨0, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 0
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm
  · refine ⟨1, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 1
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm
  · refine ⟨2, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 2
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm

/-- The selected face plane contains the tail of every dart on that face, not only
the stored representative's three tails. -/
theorem face_plane_dart
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    inner ℝ (P.outward_normal (M.dartFace d))
      (P.pos (M.tail d) - P.face_point (M.dartFace d)) = 0 := by
  obtain ⟨k, hk⟩ := tail_mem_faceVertex P d
  rw [hk]
  exact P.face_plane (M.dartFace d) k

 theorem faceDart_phi_cube_eq_self
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    (M.φ ^ 3) (P.faceDart f) = P.faceDart f := by
  let fd := P.faceDart f
  have hφne : M.φ fd ≠ fd := by
    simpa [fd] using faceDart_phi_ne_self P f
  have hlen : M.faceLen f = 3 := by
    simpa [CombMap.faceLen] using P.every_face_triangle f
  have hcard : (M.φ.cycleOf fd).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφne]
    simpa [fd, P.faceDart_face f] using hlen
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ 3 fd
  rw [hcard, Nat.mod_self] at hpow
  simpa [fd] using hpow.symm

theorem phi_cube_eq_self_of_triangular_euclidean
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    (M.φ ^ 3) d = d := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq P (f := M.dartFace d) (d := d) rfl with
    h | h | h
  · rw [h]
    exact faceDart_phi_cube_eq_self P (M.dartFace d)
  · rw [h]
    exact congrArg M.φ (faceDart_phi_cube_eq_self P (M.dartFace d))
  · rw [h]
    exact congrArg (fun x => M.φ (M.φ x))
      (faceDart_phi_cube_eq_self P (M.dartFace d))

theorem tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d) := by
  have hcube := phi_cube_eq_self_of_triangular_euclidean P d
  have hpred : M.φ (M.φ d) = M.φ.symm d := by
    apply M.φ.injective
    rw [Equiv.apply_symm_apply]
    simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
  have hsymm : M.φ.symm d = M.α (M.σ.symm d) := by
    apply M.φ.injective
    rw [Equiv.apply_symm_apply]
    symm
    change (M.σ * M.α) (M.α (M.σ.symm d)) = d
    rw [Equiv.Perm.mul_apply, M.alpha_alpha, Equiv.apply_symm_apply]
  rw [hpred, hsymm, M.tail_alpha]

/-- The stored face vertices are the three tails of any dart on the same
triangular face, up to cyclic rotation. -/
theorem faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) {f : M.Face} {e : D}
    (he : M.dartFace e = f) (k : Fin 3) :
    P.faceVertex f k = M.tail e ∨
      P.faceVertex f k = M.head e ∨
      P.faceVertex f k = M.tail (M.φ (M.φ e)) := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq P (f := f) (d := e) he with
    h | h | h
  · subst h
    fin_cases k
    · left
      have hv := congrFun (P.face_vertices_match f) 0
      simpa using hv
    · right; left
      have hv := congrFun (P.face_vertices_match f) 1
      simpa [M.tail_phi] using hv
    · right; right
      have hv := congrFun (P.face_vertices_match f) 2
      simpa using hv
  · subst h
    fin_cases k
    · right; right
      have hv := congrFun (P.face_vertices_match f) 0
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (P.faceDart f) =
          M.tail (M.φ (M.φ (M.φ (P.faceDart f)))) := by
        rw [hcube']
      exact hv.trans htail
    · left
      have hv := congrFun (P.face_vertices_match f) 1
      simpa [M.tail_phi] using hv
    · right; left
      have hv := congrFun (P.face_vertices_match f) 2
      simpa [M.tail_phi] using hv
  · subst h
    fin_cases k
    · right; left
      have hv := congrFun (P.face_vertices_match f) 0
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (P.faceDart f) =
          M.head (M.φ (M.φ (P.faceDart f))) := by
        rw [← M.tail_phi (M.φ (M.φ (P.faceDart f))), hcube']
      exact hv.trans htail
    · right; right
      have hv := congrFun (P.face_vertices_match f) 1
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (M.φ (P.faceDart f)) =
          M.tail (M.φ (M.φ (M.φ (M.φ (P.faceDart f))))) := by
        rw [hcube']
      exact hv.trans htail
    · left
      have hv := congrFun (P.face_vertices_match f) 2
      simpa using hv

lemma linearIndependent_pair_of_cross_ne_zero {u v : E3}
    (hcross : cross u v ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  by_cases hu : u = 0
  · exfalso
    apply hcross
    rw [hu]
    have hzero := cross_smul_left (0 : ℝ) v v
    simpa using hzero
  rw [LinearIndependent.pair_iff' hu]
  intro a hv
  apply hcross
  rw [← hv, cross_smul_right, cross_self, smul_zero]







theorem normal_eq_pos_smul_neg_cross_of_support {n u v w : E3}
    (hnu : (⟪n, u⟫ : ℝ) = 0) (hnv : (⟪n, v⟫ : ℝ) = 0)
    (hli : LinearIndependent ℝ ![u, v])
    (hopp : (⟪n, w⟫ : ℝ) < 0)
    (hdet : 0 < (⟪cross u v, w⟫ : ℝ)) :
    ∃ lam : ℝ, 0 < lam ∧ n = lam • (-(cross u v)) := by
  obtain ⟨s, hs⟩ := perp_two_imp_parallel_cross hnu hnv hli
  have hsneg : s < 0 := by
    have hdot : (⟪n, w⟫ : ℝ) = s * ⟪cross u v, w⟫ := by
      rw [hs, real_inner_smul_left]
    nlinarith
  refine ⟨-s, by linarith, ?_⟩
  rw [hs]
  module

theorem face_normal_eq_pos_smul_neg_cross_of_coplanar_edges
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face)
    (v a b w : M.Vertex)
    (hv : inner ℝ (P.outward_normal f) (P.pos v - P.face_point f) = 0)
    (ha : inner ℝ (P.outward_normal f) (P.pos a - P.face_point f) = 0)
    (hb : inner ℝ (P.outward_normal f) (P.pos b - P.face_point f) = 0)
    (hli : LinearIndependent ℝ ![P.pos a - P.pos v, P.pos b - P.pos v])
    (hw : ∀ i, w ≠ P.faceVertex f i)
    (hdet : 0 < inner ℝ (cross (P.pos a - P.pos v) (P.pos b - P.pos v))
      (P.pos w - P.pos v)) :
    ∃ lam : ℝ, 0 < lam ∧
      P.outward_normal f = lam • (-(cross (P.pos a - P.pos v) (P.pos b - P.pos v))) := by
  have hstrict0 := P.face_support_strict f w hw
  have hstrict : inner ℝ (P.outward_normal f) (P.pos w - P.pos v) < 0 := by
    have hrewrite :
        inner ℝ (P.outward_normal f) (P.pos w - P.pos v) =
          inner ℝ (P.outward_normal f) (P.pos w - P.face_point f) -
            inner ℝ (P.outward_normal f) (P.pos v - P.face_point f) := by
      calc
        inner ℝ (P.outward_normal f) (P.pos w - P.pos v)
            = inner ℝ (P.outward_normal f)
                ((P.pos w - P.face_point f) - (P.pos v - P.face_point f)) := by
                congr 1
                module
        _ = inner ℝ (P.outward_normal f) (P.pos w - P.face_point f) -
              inner ℝ (P.outward_normal f) (P.pos v - P.face_point f) := by
                rw [inner_sub_right]
    rw [hrewrite, hv, sub_zero]
    exact hstrict0
  have hperp1 : inner ℝ (P.outward_normal f) (P.pos a - P.pos v) = 0 :=
    inner_sub_of_plane_eq ha hv
  have hperp2 : inner ℝ (P.outward_normal f) (P.pos b - P.pos v) = 0 :=
    inner_sub_of_plane_eq hb hv
  exact normal_eq_pos_smul_neg_cross_of_support hperp1 hperp2 hli hstrict hdet

/-- The outward normal of `dartFace e` is the negative cross product of the two
face edges emanating from `tail e`, up to a positive scalar, once a strict
off-face vertex supplies the sign. -/
theorem face_normal_eq_pos_smul_neg_cross_of_dart_edges
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (e : D) (w : M.Vertex)
    (hw : ∀ i, w ≠ P.faceVertex (M.dartFace e) i)
    (hdet : 0 < inner ℝ
      (cross
        (P.pos (M.head e) - P.pos (M.tail e))
        (P.pos (M.tail (M.φ (M.φ e))) - P.pos (M.tail e)))
      (P.pos w - P.pos (M.tail e))) :
    ∃ lam : ℝ, 0 < lam ∧
      P.outward_normal (M.dartFace e) =
        lam • (-
          cross
            (P.pos (M.head e) - P.pos (M.tail e))
            (P.pos (M.tail (M.φ (M.φ e))) - P.pos (M.tail e))) := by
  have hv : inner ℝ (P.outward_normal (M.dartFace e))
      (P.pos (M.tail e) - P.face_point (M.dartFace e)) = 0 :=
    face_plane_dart P e
  have ha : inner ℝ (P.outward_normal (M.dartFace e))
      (P.pos (M.head e) - P.face_point (M.dartFace e)) = 0 := by
    have h := face_plane_dart P (M.φ e)
    simpa [M.tail_phi] using h
  have hb : inner ℝ (P.outward_normal (M.dartFace e))
      (P.pos (M.tail (M.φ (M.φ e))) - P.face_point (M.dartFace e)) = 0 := by
    have h := face_plane_dart P (M.φ (M.φ e))
    simpa using h
  have hcrossne :
      cross
        (P.pos (M.head e) - P.pos (M.tail e))
        (P.pos (M.tail (M.φ (M.φ e))) - P.pos (M.tail e)) ≠ 0 := by
    intro hzero
    rw [hzero] at hdet
    simp at hdet
  have hli : LinearIndependent ℝ
      ![P.pos (M.head e) - P.pos (M.tail e),
        P.pos (M.tail (M.φ (M.φ e))) - P.pos (M.tail e)] :=
    linearIndependent_pair_of_cross_ne_zero hcrossne
  exact face_normal_eq_pos_smul_neg_cross_of_coplanar_edges
    (P := P) (f := M.dartFace e)
    (v := M.tail e) (a := M.head e)
    (b := M.tail (M.φ (M.φ e))) (w := w)
    hv ha hb hli hw hdet

 lemma fin_sub_one_add_one {n : ℕ} [NeZero n] (i : Fin n) :
    i - 1 + 1 = i := by
  rw [sub_add_cancel]

 lemma vertexLinkGeometry_exists_noninc_face
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    {P : TriangulatedEuclideanPolyhedron M} {v : M.Vertex}
    (LG : VertexLinkGeometry P v) (i : Fin (LG.n + 1)) :
    ∃ j : Fin (LG.n + 1), j ≠ i ∧ j ≠ i + 1 := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin (LG.n + 1))) ⊆ {i, i + 1} := by
    intro j _
    rcases eq_or_ne j i with hji | hji
    · simp [hji]
    · have := hcon j hji
      simp [this]
  have hle := Finset.card_le_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hle2 : ({i, i + 1} : Finset (Fin (LG.n + 1))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have := LG.hn
  omega

 lemma normal_neg_raw_cross_to_edgeDir_cross
    (S : VertexStar) (i j : Fin (S.n + 1)) {normal : E3}
    {lam : ℝ} (hlam : 0 < lam)
    (hraw : normal = lam • (-(cross (S.rawDir i) (S.rawDir j)))) :
    ∃ lam' : ℝ, 0 < lam' ∧
      normal = lam' • (-(cross (S.edgeDir i : E3) (S.edgeDir j : E3))) := by
  let c : ℝ := ‖S.rawDir i‖⁻¹ * ‖S.rawDir j‖⁻¹
  have hcpos : 0 < c := mul_pos (S.inv_norm_pos i) (S.inv_norm_pos j)
  have hcross :
      cross (S.edgeDir i : E3) (S.edgeDir j : E3) =
        c • cross (S.rawDir i) (S.rawDir j) := by
    rw [S.edgeDir_coe i, S.edgeDir_coe j, cross_smul_left, cross_smul_right]
    simp [c, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  refine ⟨lam / c, div_pos hlam hcpos, ?_⟩
  rw [hraw, hcross]
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcoef : lam / c * c = lam := by
    field_simp [hcne]
  have hcoef_neg : lam / c * -c = -lam := by
    nlinarith
  conv_lhs => rw [smul_neg, ← neg_smul]
  conv_rhs => rw [← neg_smul, smul_smul]
  rw [hcoef_neg]



lemma inner_tangent_tangent_unit {a b c : E3} (hb : ‖b‖ = 1) :
    inner ℝ (tangentToVec b a) (tangentToVec b c)
      = inner ℝ a c - inner ℝ a b * inner ℝ b c := by
  unfold tangentToVec
  have hb_inner : inner ℝ b b = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hb]
    norm_num
  simp [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hb_inner, real_inner_comm]
  rw [hb]
  ring_nf

lemma inner_cross_cross_unit {a b c : E3} (hb : ‖b‖ = 1) :
    inner ℝ (cross a b) (cross b c)
      = inner ℝ a b * inner ℝ b c - inner ℝ a c := by
  have hb_inner : inner ℝ b b = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hb]
    norm_num
  rw [inner_cross_cross, hb_inner]
  ring

lemma inner_tangent_eq_neg_inner_cross {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    inner ℝ (tangentToVec b a) (tangentToVec b c)
      = - inner ℝ (cross a b) (cross b c) := by
  rw [inner_tangent_tangent_unit hb, inner_cross_cross_unit hb]
  ring

lemma norm_tangent_sq_unit {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖tangentToVec b a‖ ^ 2 = 1 - (inner ℝ a b) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_tangent_tangent_unit (a := a) (b := b) (c := a) hb]
  have ha_inner : inner ℝ a a = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, ha]
    norm_num
  rw [ha_inner]
  rw [real_inner_comm b a]
  ring

lemma norm_cross_sq_unit {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖cross a b‖ ^ 2 = 1 - (inner ℝ a b) ^ 2 := by
  rw [norm_sq_cross, ha, hb]
  ring

lemma norm_tangent_eq_norm_cross_left {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖tangentToVec b a‖ = ‖cross a b‖ := by
  have hsq : ‖tangentToVec b a‖ ^ 2 = ‖cross a b‖ ^ 2 := by
    rw [norm_tangent_sq_unit ha hb, norm_cross_sq_unit ha hb]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have h1 : 0 ≤ ‖tangentToVec b a‖ := norm_nonneg _
    have h2 : 0 ≤ ‖cross a b‖ := norm_nonneg _
    linarith

lemma norm_tangent_eq_norm_cross_right {b c : E3} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖tangentToVec b c‖ = ‖cross b c‖ := by
  have hsq : ‖tangentToVec b c‖ ^ 2 = ‖cross b c‖ ^ 2 := by
    rw [norm_tangent_sq_unit hc hb, norm_cross_sq_unit hb hc]
    rw [real_inner_comm c b]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have h1 : 0 ≤ ‖tangentToVec b c‖ := norm_nonneg _
    have h2 : 0 ≤ ‖cross b c‖ := norm_nonneg _
    linarith

lemma cos_tangent_eq_neg_cos_cross {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0) (htc : tangentToVec b c ≠ 0)
    (hX : cross a b ≠ 0) (hY : cross b c ≠ 0) :
    Real.cos (InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c))
      =
    - Real.cos (InnerProductGeometry.angle (cross a b) (cross b c)) := by
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle,
    inner_tangent_eq_neg_inner_cross ha hb hc,
    norm_tangent_eq_norm_cross_left ha hb,
    norm_tangent_eq_norm_cross_right hb hc]
  field_simp [norm_pos_iff.mpr hX, norm_pos_iff.mpr hY]

lemma tangent_angle_eq_pi_sub_cross_angle {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0) (htc : tangentToVec b c ≠ 0)
    (hX : cross a b ≠ 0) (hY : cross b c ≠ 0) :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      =
    Real.pi - InnerProductGeometry.angle (cross a b) (cross b c) := by
  apply Real.injOn_cos.eq_iff
    (s := Set.Icc (0 : ℝ) Real.pi)
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    ⟨by linarith [InnerProductGeometry.angle_le_pi (cross a b) (cross b c)],
      by linarith [InnerProductGeometry.angle_nonneg (cross a b) (cross b c)]⟩ |>.1
  rw [cos_tangent_eq_neg_cos_cross ha hb hc hta htc hX hY]
  rw [Real.cos_pi_sub]

lemma angle_normals_eq_cross {a b c n_f n_g : E3}
    (horient :
      ∃ l m : ℝ,
        0 < l ∧ 0 < m ∧
          ((n_f = l • cross a b ∧ n_g = m • cross b c) ∨
           (n_f = l • (-(cross a b)) ∧ n_g = m • (-(cross b c))))) :
    InnerProductGeometry.angle n_f n_g
      =
    InnerProductGeometry.angle (cross a b) (cross b c) := by
  rcases horient with ⟨l, m, hl, hm, hcase⟩
  rcases hcase with ⟨hf, hg⟩ | ⟨hf, hg⟩
  · rw [hf, hg]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hl]
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hm]
  · rw [hf, hg]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hl]
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hm]
    rw [InnerProductGeometry.angle_neg_neg]

theorem sphAngle_eq_pi_sub_normal_angle {a b c n_f n_g : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0) (htc : tangentToVec b c ≠ 0)
    (hX : cross a b ≠ 0) (hY : cross b c ≠ 0)
    (horient :
      ∃ l m : ℝ,
        0 < l ∧ 0 < m ∧
          ((n_f = l • cross a b ∧ n_g = m • cross b c) ∨
           (n_f = l • (-(cross a b)) ∧ n_g = m • (-(cross b c))))) :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      =
    Real.pi - InnerProductGeometry.angle n_f n_g := by
  calc
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
        = Real.pi - InnerProductGeometry.angle (cross a b) (cross b c) :=
            tangent_angle_eq_pi_sub_cross_angle ha hb hc hta htc hX hY
    _ = Real.pi - InnerProductGeometry.angle n_f n_g := by
      rw [angle_normals_eq_cross horient]

lemma tangentTo_eq_tangentToVec (p q : S2) :
    tangentTo p q = tangentToVec (p : E3) (q : E3) := by
  rw [tangentTo_eq]
  rfl



theorem linkAngle_vertexLink_eq_pi_sub_normal_angle
    (S : VertexStar) (i : Fin (S.n + 1)) {n_f n_g : E3}
    (hta :
      tangentToVec (S.edgeDir i : E3) (S.edgeDir (i - 1) : E3) ≠ 0)
    (htc :
      tangentToVec (S.edgeDir i : E3) (S.edgeDir (i + 1) : E3) ≠ 0)
    (hX : cross (S.edgeDir (i - 1) : E3) (S.edgeDir i : E3) ≠ 0)
    (hY : cross (S.edgeDir i : E3) (S.edgeDir (i + 1) : E3) ≠ 0)
    (horient :
      ∃ l m : ℝ,
        0 < l ∧ 0 < m ∧
          ((n_f = l • cross (S.edgeDir (i - 1) : E3) (S.edgeDir i : E3) ∧
              n_g = m • cross (S.edgeDir i : E3) (S.edgeDir (i + 1) : E3)) ∨
           (n_f = l • (-(cross (S.edgeDir (i - 1) : E3) (S.edgeDir i : E3))) ∧
              n_g = m • (-(cross (S.edgeDir i : E3) (S.edgeDir (i + 1) : E3)))))) :
    linkAngle S.vertexLink i = Real.pi - InnerProductGeometry.angle n_f n_g := by
  rw [linkAngle]
  simp only [VertexStar.vertexLink_apply]
  rw [sphAngle]
  show InnerProductGeometry.angle
      (tangentTo (S.edgeDir i) (S.edgeDir (i - 1)))
      (tangentTo (S.edgeDir i) (S.edgeDir (i + 1)))
        = Real.pi - InnerProductGeometry.angle n_f n_g
  rw [tangentTo_eq_tangentToVec, tangentTo_eq_tangentToVec]
  exact sphAngle_eq_pi_sub_normal_angle
    (a := (S.edgeDir (i - 1) : E3))
    (b := (S.edgeDir i : E3))
    (c := (S.edgeDir (i + 1) : E3))
    (n_f := n_f) (n_g := n_g)
    (S.edgeDir (i - 1)).2 (S.edgeDir i).2 (S.edgeDir (i + 1)).2
    hta htc hX hY horient

theorem dihedralAngleAtDart_eq_linkAngle_of_neighbors
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D)
    (LG : VertexLinkGeometry P (M.tail d)) (J : Fin (LG.n + 1))
    (hprev : LG.nbr (J - 1) = M.head (M.σ d))
    (hcenter : LG.nbr J = M.head d)
    (hnext : LG.nbr (J + 1) = M.head (M.σ.symm d)) :
    dihedralAngleAtDart P d =
      linkAngle (vertexStarOfEuclidean P (M.tail d) LG).vertexLink J := by
  let S : VertexStar := vertexStarOfEuclidean P (M.tail d) LG
  let cJ : Fin (S.n + 1) := (show Fin (S.n + 1) from J)
  change dihedralAngleAtDart P d = linkAngle S.vertexLink cJ
  have hJprev_next : (J - 1) + 1 = J := fin_sub_one_add_one J
  have hcJprev_next : (cJ - 1) + 1 = cJ := fin_sub_one_add_one cJ
  obtain ⟨wF, hwF_ne0, hwF_ne1⟩ := vertexLinkGeometry_exists_noninc_face LG (J - 1)
  obtain ⟨wG, hwG_ne0, hwG_ne1⟩ := vertexLinkGeometry_exists_noninc_face LG J
  have hface_sigma : M.dartFace (M.σ d) = M.dartFace (M.α d) := by
    have hσφ : M.σ d = M.φ (M.α d) := by
      change M.σ d = (M.σ * M.α) (M.α d)
      rw [Equiv.Perm.mul_apply, M.alpha_alpha]
    rw [hσφ, M.dartFace_phi]
  have htail_sigma : M.tail (M.σ d) = M.tail d := M.tail_sigma d
  have htail_phi2_sigma :
      M.tail (M.φ (M.φ (M.σ d))) = M.head d := by
    rw [tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P (M.σ d),
      Equiv.symm_apply_apply]
  have hhead_phi_sigma : M.head (M.φ (M.σ d)) = M.head d := by
    simpa [M.tail_phi] using htail_phi2_sigma
  have htail_phi2_d :
      M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d) :=
    tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P d
  have hhead_phi_d : M.head (M.φ d) = M.head (M.σ.symm d) := by
    simpa [M.tail_phi] using htail_phi2_d
  have hdetF : 0 < inner ℝ
      (cross
        (P.pos (M.head (M.σ d)) - P.pos (M.tail d))
        (P.pos (M.head d) - P.pos (M.tail d)))
      (P.pos (LG.nbr wF) - P.pos (M.tail d)) := by
    have h := LG.turn_strict (J - 1) wF hwF_ne0 hwF_ne1
    rw [← det3_eq_spherical, det3_eq_inner_cross] at h
    simpa [hprev, hcenter, hJprev_next] using h
  have hwF_face : ∀ k, LG.nbr wF ≠ P.faceVertex (M.dartFace (M.σ d)) k := by
    intro k heq
    have hcases := faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
      (P := P) (e := M.σ d) (f := M.dartFace (M.σ d)) rfl k
    rw [← heq, htail_sigma, htail_phi2_sigma] at hcases
    have hnon := LG.nonincident (J - 1) wF hwF_ne0 hwF_ne1
    have hnon' :
        ¬LG.nbr wF = M.tail d ∧
          ¬LG.nbr wF = M.head (M.σ d) ∧ ¬LG.nbr wF = M.head d := by
      simpa [hprev, hJprev_next, hcenter] using hnon
    rcases hcases with htail | hsig | hhead
    · exact hnon'.1 htail
    · exact hnon'.2.1 hsig
    · exact hnon'.2.2 hhead
  obtain ⟨lamF, hlamF, hnormalFraw⟩ :=
    face_normal_eq_pos_smul_neg_cross_of_dart_edges P (M.σ d) (LG.nbr wF)
      hwF_face (by simpa [htail_sigma, htail_phi2_sigma] using hdetF)
  have hrawF_left :
      S.rawDir (cJ - 1) =
        P.pos (M.head (M.σ d)) - P.pos (M.tail d) := by
    unfold S cJ vertexStarOfEuclidean VertexLinkGeometry.toVertexStar VertexStar.rawDir
    change P.pos (LG.nbr (J - 1)) - P.pos (M.tail d) =
      P.pos (M.head (M.σ d)) - P.pos (M.tail d)
    rw [hprev]
  have hrawF_right :
      S.rawDir cJ =
        P.pos (M.head d) - P.pos (M.tail d) := by
    unfold S cJ vertexStarOfEuclidean VertexLinkGeometry.toVertexStar VertexStar.rawDir
    change P.pos (LG.nbr J) - P.pos (M.tail d) =
      P.pos (M.head d) - P.pos (M.tail d)
    rw [hcenter]
  have hnormalFraw' :
      dartNormal P (M.α d) =
        lamF • (-(cross
          (S.rawDir (cJ - 1))
          (S.rawDir cJ))) := by
    rw [hrawF_left, hrawF_right]
    unfold dartNormal
    rw [← hface_sigma]
    simpa [htail_sigma, hhead_phi_sigma, smul_neg] using hnormalFraw
  obtain ⟨lamF', hlamF', hnormalF⟩ :=
    normal_neg_raw_cross_to_edgeDir_cross S
      (cJ - 1) cJ hlamF hnormalFraw'
  have hdetG : 0 < inner ℝ
      (cross
        (P.pos (M.head d) - P.pos (M.tail d))
        (P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d)))
      (P.pos (LG.nbr wG) - P.pos (M.tail d)) := by
    have h := LG.turn_strict J wG hwG_ne0 hwG_ne1
    rw [← det3_eq_spherical, det3_eq_inner_cross] at h
    simpa [hcenter, hnext] using h
  have hwG_face : ∀ k, LG.nbr wG ≠ P.faceVertex (M.dartFace d) k := by
    intro k heq
    have hcases := faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
      (P := P) (e := d) (f := M.dartFace d) rfl k
    rw [← heq, htail_phi2_d] at hcases
    have hnon := LG.nonincident J wG hwG_ne0 hwG_ne1
    have hnon' :
        ¬LG.nbr wG = M.tail d ∧
          ¬LG.nbr wG = M.head d ∧ ¬LG.nbr wG = M.head (M.σ.symm d) := by
      simpa [hcenter, hnext] using hnon
    rcases hcases with htail | hhead | hnext'
    · exact hnon'.1 htail
    · exact hnon'.2.1 hhead
    · exact hnon'.2.2 hnext'
  obtain ⟨lamG, hlamG, hnormalGraw⟩ :=
    face_normal_eq_pos_smul_neg_cross_of_dart_edges P d (LG.nbr wG)
      hwG_face (by simpa [htail_phi2_d] using hdetG)
  have hrawG_right :
      S.rawDir (cJ + 1) =
        P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d) := by
    unfold S cJ vertexStarOfEuclidean VertexLinkGeometry.toVertexStar VertexStar.rawDir
    change P.pos (LG.nbr (J + 1)) - P.pos (M.tail d) =
      P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d)
    rw [hnext]
  have hnormalGraw' :
      dartNormal P d =
        lamG • (-(cross
          (S.rawDir cJ)
          (S.rawDir (cJ + 1)))) := by
    rw [hrawF_right, hrawG_right]
    unfold dartNormal
    simpa [hhead_phi_d, smul_neg] using hnormalGraw
  obtain ⟨lamG', hlamG', hnormalG⟩ :=
    normal_neg_raw_cross_to_edgeDir_cross S
      cJ (cJ + 1) hlamG hnormalGraw'
  have hta :
      tangentToVec (S.edgeDir cJ : E3)
          (S.edgeDir (cJ - 1) : E3) ≠ 0 := by
    intro hzero
    have ht : tangentTo (S.edgeDir cJ)
        (S.edgeDir (cJ - 1)) = 0 := by
      simpa [tangentTo_eq_tangentToVec] using hzero
    have hnot := (tangentTo_eq_zero_iff
      (S.edgeDir cJ)
      (S.edgeDir (cJ - 1))).mp ht
    have hsa : ShortArc (S.edgeDir cJ)
        (S.edgeDir (cJ - 1)) := by
      have h0 := S.edgeDir_shortArc (cJ - 1)
      simpa [hcJprev_next] using h0.symm
    exact hnot hsa
  have htc :
      tangentToVec (S.edgeDir cJ : E3)
          (S.edgeDir (cJ + 1) : E3) ≠ 0 := by
    intro hzero
    have ht : tangentTo (S.edgeDir cJ)
        (S.edgeDir (cJ + 1)) = 0 := by
      simpa [tangentTo_eq_tangentToVec] using hzero
    have hnot := (tangentTo_eq_zero_iff
      (S.edgeDir cJ)
      (S.edgeDir (cJ + 1))).mp ht
    exact hnot (S.edgeDir_shortArc cJ)
  have hX :
      cross (S.edgeDir (cJ - 1) : E3)
        (S.edgeDir cJ : E3) ≠ 0 := by
    have hsa := S.edgeDir_shortArc (cJ - 1)
    exact ProofsInTheBook.SphericalCongruence.cross_ne_zero_of_shortArc
      (by simpa [hcJprev_next] using hsa)
  have hY :
      cross (S.edgeDir cJ : E3)
        (S.edgeDir (cJ + 1) : E3) ≠ 0 :=
    ProofsInTheBook.SphericalCongruence.cross_ne_zero_of_shortArc
      (S.edgeDir_shortArc cJ)
  have hlink := linkAngle_vertexLink_eq_pi_sub_normal_angle
    (S := S) (i := cJ)
    (n_f := dartNormal P (M.α d)) (n_g := dartNormal P d)
    hta htc hX hY
    ⟨lamF', lamG', hlamF', hlamG', Or.inr ⟨hnormalF, hnormalG⟩⟩
  unfold dihedralAngleAtDart
  rw [hlink, InnerProductGeometry.angle_comm]

theorem dihedralAngleAtDart_eq_linkAngle
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D)
    (LG : VertexLinkGeometry P (M.tail d)) (J : Fin (LG.n + 1))
    (hprev : LG.nbr (J - 1) = M.head (M.σ d))
    (hcenter : LG.nbr J = M.head d)
    (hnext : LG.nbr (J + 1) = M.head (M.σ.symm d)) :
    dihedralAngleAtDart P d =
      linkAngle (vertexStarOfEuclidean P (M.tail d) LG).vertexLink J :=
  dihedralAngleAtDart_eq_linkAngle_of_neighbors P d LG J hprev hcenter hnext




















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

/-- **Equal face angles ⟹ equal link side lengths.**  Two vertex stars `S`, `T` with the same edge
count and matching corresponding face angles at the apex have, by Bridge A, equal link side lengths.
This is the `equal_sides` input of the Cauchy arm obstruction, derived (not posited). -/
theorem sideLen_vertexLink_eq_of_faceAngle_eq
    (S T : VertexStar) (hnT : T.n = S.n)
    (hface : ∀ i : Fin S.n,
      EuclideanGeometry.angle (S.p i.castSucc) S.o (S.p i.succ)
        = EuclideanGeometry.angle (T.p (i.cast hnT.symm).castSucc) T.o (T.p (i.cast hnT.symm).succ)) :
    ∀ i : Fin S.n,
      sideLen S.vertexLink i = sideLen T.vertexLink (i.cast hnT.symm) := by
  intro i
  rw [S.sideLen_vertexLink, T.sideLen_vertexLink, hface i]

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



/-- **Cyclic rotation preserves interior joints.**  The `i`-th joint of `rotPoly A k` is the
spherical angle at the parent triple starting at `⟨i.val⟩ + k`. -/
theorem rotPoly_jointAngle {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (i : Fin (n - 1)) :
    jointAngle (rotPoly A k) i
      = sphAngle (A (⟨i.val, by have := i.isLt; omega⟩ + k))
          (A (⟨i.val + 1, by have := i.isLt; omega⟩ + k))
          (A (⟨i.val + 2, by have := i.isLt; omega⟩ + k)) := by
  unfold jointAngle rotPoly
  rfl



/-- The wrap parameter `M = (n+1) - s + t` for cut indices `t < s ≤ n`.  The wrapped arc has `M + 1`
vertices `A s, …, A n, A 0, …, A t`. -/
def wrapLen (n s t : ℕ) : ℕ := (n + 1) - s + t

/-- For `t < s ≤ n`, the wrap parameter satisfies `0 < M ≤ n`, so `subArc (rotPoly A s) 0 M` is a
valid contiguous sub-arc of the rotated polygon. -/
theorem wrapLen_lt_le {n s t : ℕ} (hts : t < s) (hsn : s ≤ n) :
    0 < wrapLen n s t ∧ wrapLen n s t ≤ n := by
  unfold wrapLen; omega



/-- The wrapped contiguous sub-arc `A s, A (s+1), …, A n, A 0, …, A t` (`t < s ≤ n`), realized as the
non-wrapping range `[0 .. M]` of the rotated polygon `rotPoly A s` (`M = (n+1) - s + t`). -/
def subArcWrap {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n) :
    Fin (wrapLen n s t + 1) → S2 :=
  subArc (rotPoly A ⟨s, by omega⟩) 0 (wrapLen n s t)
    (wrapLen_lt_le hts hsn).1 (wrapLen_lt_le hts hsn).2



/-- `subArcWrap A t s i = A (⟨i.val⟩ + s)` (cyclic `Fin (n+1)` addition). -/
theorem subArcWrap_apply {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t + 1)) :
    subArcWrap A t s hts hsn i
      = A (⟨i.val, by have := i.isLt; unfold wrapLen at this; omega⟩ + ⟨s, by omega⟩) := by
  unfold subArcWrap
  rw [subArc_apply]
  show rotPoly A ⟨s, by omega⟩ ⟨0 + i.val, by have := i.isLt; unfold wrapLen at this; omega⟩ = _
  unfold rotPoly
  congr 2
  apply Fin.ext
  exact Nat.zero_add i.val



/-- The starting vertex of the wrapped sub-arc is `A s`. -/
@[simp] theorem subArcWrap_zero {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s)
    (hsn : s ≤ n) :
    subArcWrap A t s hts hsn 0 = A ⟨s, by omega⟩ := by
  rw [subArcWrap_apply]
  congr 1
  apply Fin.ext
  show ((0 : Fin (wrapLen n s t + 1)).val + s) % (n + 1) = s
  simp only [Fin.val_zero, Nat.zero_add, Nat.mod_eq_of_lt (show s < n + 1 by omega)]

/-- The final vertex of the wrapped sub-arc is `A t`. -/
@[simp] theorem subArcWrap_last {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s)
    (hsn : s ≤ n) :
    subArcWrap A t s hts hsn (Fin.last (wrapLen n s t)) = A ⟨t, by omega⟩ := by
  rw [subArcWrap_apply]
  congr 1
  apply Fin.ext
  show ((Fin.last (wrapLen n s t)).val + s) % (n + 1) = t
  rw [Fin.val_last]
  unfold wrapLen
  -- ((n+1) - s + t + s) % (n+1) = (n + 1 + t) % (n+1) = t
  rw [show (n + 1) - s + t + s = (n + 1) + t by omega, Nat.add_comm (n + 1) t,
    Nat.add_mod_right, Nat.mod_eq_of_lt (show t < n + 1 by omega)]



/-- **The wrapped sub-arc is a strictly convex arm.**  For `t < s ≤ n` with `2 ≤ M = (n+1) - s + t`,
the wrapping range `A s, …, A n, A 0, …, A t` of a strictly convex spherical arm `A` is again a
`StrictConvexSphArm`, closing diagonal `A s → A t`. -/
theorem subArcWrap_strictConvexArm {n : ℕ} (A : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (hm : 2 ≤ wrapLen n s t) :
    StrictConvexSphArm (subArcWrap A t s hts hsn) := by
  unfold subArcWrap
  exact subArc_strictConvexArm (rotPoly A ⟨s, by omega⟩)
    (rotPoly_strictConvexArm hA ⟨s, by omega⟩) 0 (wrapLen n s t)
    (wrapLen_lt_le hts hsn).1 (wrapLen_lt_le hts hsn).2 (by simpa using hm)



/-- **Interior wrapped sides = rotated parent sides.**  The `i`-th side of `subArcWrap A t s` is the
side `sideLen (rotPoly A s) ⟨i.val⟩` of the rotated polygon, i.e. the cyclic edge
`A (⟨i.val⟩ + s) → A (⟨i.val⟩ + s + 1)`. -/
theorem subArcWrap_sideLen {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t)) :
    sideLen (subArcWrap A t s hts hsn) i
      = sideLen (rotPoly A ⟨s, by omega⟩)
          ⟨i.val, by have := i.isLt; unfold wrapLen at this; omega⟩ := by
  unfold subArcWrap
  rw [subArc_sideLen]
  congr 1
  apply Fin.ext
  show 0 + i.val = i.val
  exact Nat.zero_add i.val

/-- **Interior wrapped joints = rotated parent joints.**  The `i`-th joint of `subArcWrap A t s` is
the joint `jointAngle (rotPoly A s) ⟨i.val⟩` of the rotated polygon. -/
theorem subArcWrap_jointAngle {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t - 1)) :
    jointAngle (subArcWrap A t s hts hsn) i
      = jointAngle (rotPoly A ⟨s, by omega⟩)
          ⟨i.val, by have := i.isLt; unfold wrapLen at this; omega⟩ := by
  unfold subArcWrap
  rw [subArc_jointAngle]
  congr 1
  apply Fin.ext
  show 0 + i.val = i.val
  exact Nat.zero_add i.val

/-- **The wrapped arm endpoint chord is the diagonal `A t → A s`.**  `sDist (subArcWrap … 0)
(subArcWrap … (Fin.last M)) = sDist (A t) (A s)`. -/
theorem subArcWrap_endpt {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n) :
    sDist (subArcWrap A t s hts hsn 0)
        (subArcWrap A t s hts hsn (Fin.last (wrapLen n s t)))
      = sDist (A ⟨t, by omega⟩) (A ⟨s, by omega⟩) := by
  rw [subArcWrap_zero, subArcWrap_last, sDist_comm]



open ProofsInTheBook.Ch13ArmVertex in
/-- **`TwoArcSplitData` from a cyclic cut at `t < s`.**  Given the link pair `(A, B)` with equal
sides and equal closing chord, two cut indices `t < s ≤ n` with both arcs non-degenerate
(`2 ≤ s - t`, `2 ≤ wrapLen n s t`), and the per-arc joint monotonicity of the `signChanges = 2`
pattern, assemble the genuine `TwoArcSplitData A B`.  Feeding it to `TwoArcSplitData.contradiction`
yields `False`. -/
noncomputable def twoArcSplitData_of_indices {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (hm1 : 2 ≤ s - t) (hm2 : 2 ≤ wrapLen n s t)
    -- the non-wrap arc opens (`A ≤ B` joints), strictly somewhere; the wrap arc closes (`B ≤ A`).
    (hmono1 : ∀ i : Fin (s - t - 1),
        jointAngle (subArc A t s hts hsn) i ≤ jointAngle (subArc B t s hts hsn) i)
    (hstrict1 : ∃ i : Fin (s - t - 1),
        jointAngle (subArc A t s hts hsn) i < jointAngle (subArc B t s hts hsn) i)
    (hmono2 : ∀ i : Fin (wrapLen n s t - 1),
        jointAngle (subArcWrap B t s hts hsn) i ≤ jointAngle (subArcWrap A t s hts hsn) i) :
    ProofsInTheBook.Ch13ArmVertex.TwoArcSplitData A B where
  m₁ := s - t
  m₂ := wrapLen n s t
  hm₁ := hm1
  hm₂ := hm2
  Arc1 := subArc A t s hts hsn
  Brc1 := subArc B t s hts hsn
  Arc2 := subArcWrap A t s hts hsn
  Brc2 := subArcWrap B t s hts hsn
  harc1A := subArc_strictConvexArm A hA t s hts hsn hm1
  harc1B := subArc_strictConvexArm B hB t s hts hsn hm1
  harc2A := subArcWrap_strictConvexArm A hA t s hts hsn hm2
  harc2B := subArcWrap_strictConvexArm B hB t s hts hsn hm2
  hsides1 := by
    intro i
    rw [subArc_sideLen, subArc_sideLen]
    exact hsides ⟨t + i.val, by have := i.isLt; omega⟩
  hsides2 := by
    intro i
    rw [subArcWrap_sideLen, subArcWrap_sideLen]
    exact rotPoly_sideLen_eq hn A B hsides hclose ⟨s, by omega⟩ ⟨i.val, by
      have := i.isLt; unfold wrapLen at this; omega⟩
  hshareA := by
    rw [subArc_endpt, subArcWrap_endpt, sDist_comm (A ⟨t, by omega⟩) (A ⟨s, by omega⟩)]
  hshareB := by
    rw [subArc_endpt, subArcWrap_endpt, sDist_comm (B ⟨t, by omega⟩) (B ⟨s, by omega⟩)]
  hmono1 := hmono1
  hstrict1 := hstrict1
  hmono2 := hmono2







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

/-- Rotate the cyclic neighbor order of a vertex star. -/
noncomputable abbrev rotate (S : VertexStar) (k : Fin (S.n + 1)) : VertexStar where
  n := S.n
  hn := S.hn
  o := S.o
  p := fun i => S.p (i + k)
  apex_ne := fun i => S.apex_ne (i + k)
  open_hemi := by
    rcases S.open_hemi with ⟨h, hnorm, hpos⟩
    exact ⟨h, hnorm, fun i => hpos (i + k)⟩
  turn_support := by
    intro i j
    have hnext : (i + 1 : Fin (S.n + 1)) + k = (i + k) + 1 := by
      rw [add_right_comm]
    simpa [hnext] using S.turn_support (i + k) (j + k)
  turn_strict := by
    intro i j hji hji1
    have hnext : (i + 1 : Fin (S.n + 1)) + k = (i + k) + 1 := by
      rw [add_right_comm]
    have hne0 : j + k ≠ i + k := by
      intro h
      exact hji (add_right_cancel h)
    have hne1 : j + k ≠ (i + k) + 1 := by
      intro h
      apply hji1
      apply add_right_cancel (b := k)
      rw [hnext]
      exact h
    simpa [hnext] using S.turn_strict (i + k) (j + k) hne0 hne1

theorem vertexLink_rotate (S : VertexStar) (k : Fin (S.n + 1)) :
    (S.rotate k).vertexLink = rotPoly S.vertexLink k := by
  funext i
  rfl

end VertexStar

end ProofsInTheBook.Ch13VertexStar

namespace ProofsInTheBook.Ch13Cauchy3D

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/-- Compatibility abbreviation for this assembly layer: it already carries the local link geometry. -/
 abbrev vertexStarOfEuclidean
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) : VertexStar :=
  LG.toVertexStar

/--
A convex Euclidean polyhedron is a triangulated Euclidean realization together
with the face-local outward orientation and simple-graph hypotheses from which
the local vertex-link geometry is derived.

The `isSimple` field is included because the downstream Cauchy realization
interface requires a simple triangulated sphere.
-/
structure ConvexEuclideanPolyhedron (M : CombMap D)
    extends TriangulatedEuclideanPolyhedron M where
  degree_ge_three :
    ∀ (v : M.Vertex), 3 ≤ vDeg toTriangulatedEuclideanPolyhedron v
  face_orientation_faithful :
    FaceOrientationFaithful toTriangulatedEuclideanPolyhedron
  sphere : M.IsSphereMap
  triangle : M.FaceRegular 3
  isSimple : M.IsSimpleGraph

namespace ConvexEuclideanPolyhedron

/-- The underlying triangulated Euclidean realization. -/
abbrev toTri (P : ConvexEuclideanPolyhedron M) : TriangulatedEuclideanPolyhedron M :=
  P.toTriangulatedEuclideanPolyhedron

/-- The derived reverse-`σ` rotation faithfulness used by the link builder. -/
theorem faithful (P : ConvexEuclideanPolyhedron M) :
    RotationFaithful P.toTri :=
  rotationFaithful_of_faceOrientationFaithful P.toTri P.face_orientation_faithful

/-- The derived local vertex-link geometry at a vertex. -/
def linkGeom (P : ConvexEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P.toTri v) : VertexLinkGeometry P.toTri v :=
  vertexLinkGeometryOfEuclidean P.toTri P.faithful P.isSimple v hdeg

/-- The derived vertex-link geometry with the stored degree lower bound supplied. -/
def linkGeomAt (P : ConvexEuclideanPolyhedron M) (v : M.Vertex) :
    VertexLinkGeometry P.toTri v :=
  P.linkGeom v (P.degree_ge_three v)



end ConvexEuclideanPolyhedron



/-- Edge-length congruence for two Euclidean realizations on the same combinatorial map. -/
def CongruentFaces (P Q : TriangulatedEuclideanPolyhedron M) : Prop :=
  ∀ d : D,
    ‖P.pos (M.head d) - P.pos (M.tail d)‖ =
      ‖Q.pos (M.head d) - Q.pos (M.tail d)‖

theorem euclidean_angle_eq_of_three_dist_eq
    {a b c a' b' c' : Ch13Euclidean.E3}
    (hab : dist b a = dist b' a')
    (hac : dist c a = dist c' a')
    (hbc : dist b c = dist b' c')
    (hba : b ≠ a) (hca : c ≠ a) :
    EuclideanGeometry.angle b a c = EuclideanGeometry.angle b' a' c' := by
  have hcos₁ := EuclideanGeometry.law_cos b a c
  have hcos₂ := EuclideanGeometry.law_cos b' a' c'
  rw [← hab, ← hac, ← hbc] at hcos₂
  have hprod : 2 * dist b a * dist c a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (dist_ne_zero.mpr hba))
      (dist_ne_zero.mpr hca)
  have hcos :
      Real.cos (EuclideanGeometry.angle b a c) =
        Real.cos (EuclideanGeometry.angle b' a' c') := by
    have hmul :
        (2 * dist b a * dist c a) * Real.cos (EuclideanGeometry.angle b a c) =
          (2 * dist b a * dist c a) * Real.cos (EuclideanGeometry.angle b' a' c') := by
      nlinarith
    exact mul_left_cancel₀ hprod hmul
  exact Real.injOn_cos
    ⟨EuclideanGeometry.angle_nonneg b a c, EuclideanGeometry.angle_le_pi b a c⟩
    ⟨EuclideanGeometry.angle_nonneg b' a' c', EuclideanGeometry.angle_le_pi b' a' c'⟩
    hcos

theorem congruentFaces_face_angle_at_dart
    (P Q : TriangulatedEuclideanPolyhedron M) (hcong : CongruentFaces P Q) (d : D) :
    EuclideanGeometry.angle
        (P.pos (M.head d)) (P.pos (M.tail d)) (P.pos (M.head (M.σ.symm d)))
      =
    EuclideanGeometry.angle
        (Q.pos (M.head d)) (Q.pos (M.tail d)) (Q.pos (M.head (M.σ.symm d))) := by
  have htail_symm : M.tail (M.σ.symm d) = M.tail d := by
    have h := M.tail_sigma (M.σ.symm d)
    simpa using h.symm
  have htail_phi2 :
      M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d) :=
    Ch13SphAngle.tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P d
  have hhead_phi :
      M.head (M.φ d) = M.head (M.σ.symm d) := by
    simpa [M.tail_phi] using htail_phi2
  have hab :
      dist (P.pos (M.head d)) (P.pos (M.tail d)) =
        dist (Q.pos (M.head d)) (Q.pos (M.tail d)) := by
    simpa [dist_eq_norm] using hcong d
  have hac :
      dist (P.pos (M.head (M.σ.symm d))) (P.pos (M.tail d)) =
        dist (Q.pos (M.head (M.σ.symm d))) (Q.pos (M.tail d)) := by
    have h := hcong (M.σ.symm d)
    simpa [dist_eq_norm, htail_symm] using h
  have hbc :
      dist (P.pos (M.head d)) (P.pos (M.head (M.σ.symm d))) =
        dist (Q.pos (M.head d)) (Q.pos (M.head (M.σ.symm d))) := by
    have h := hcong (M.φ d)
    simpa [dist_eq_norm, M.tail_phi, hhead_phi, norm_sub_rev] using h
  have hba : P.pos (M.head d) ≠ P.pos (M.tail d) := by
    exact (P.edge_nondegenerate d).symm
  have hca : P.pos (M.head (M.σ.symm d)) ≠ P.pos (M.tail d) := by
    have hnd := P.edge_nondegenerate (M.σ.symm d)
    simpa [htail_symm] using hnd.symm
  exact euclidean_angle_eq_of_three_dist_eq hab hac hbc hba hca

/-- The Euclidean dart sign used by the Cauchy marked sphere. -/
def euclideanEdgeSign (P Q : TriangulatedEuclideanPolyhedron M) : D → EdgeSign :=
  dihedralSignAtDart P Q

theorem euclideanEdgeSign_alpha
    (P Q : TriangulatedEuclideanPolyhedron M) (d : D) :
    euclideanEdgeSign P Q (M.α d) = euclideanEdgeSign P Q d := by
  unfold euclideanEdgeSign
  exact dihedralSignAtDart_alpha P Q d

/-- A canonical representative dart for a vertex. -/
def vertexDartRep (v : M.Vertex) : D :=
  Quotient.out v

theorem vertexDartRep_tail (v : M.Vertex) :
    M.tail (vertexDartRep (M := M) v) = v :=
  Quotient.out_eq v

/-- Reading a finite list through `Fin.rev` gives its reverse. -/
theorem ofFn_get_rev {α : Type*} (L : List α) :
    List.ofFn (fun i : Fin L.length => L.get (Fin.rev i)) = L.reverse := by
  apply (List.ext_get_iff).2
  constructor
  · simp
  · intro n hn₁ hn₂
    simp only [List.length_ofFn, List.length_reverse] at hn₁ hn₂
    rw [List.get_ofFn]
    rw [List.get_reverse' L ⟨n, by simpa using hn₂⟩ (by omega)]
    simp [Fin.rev]
    have hidx : L.length - (n + 1) = L.length - 1 - n := by omega
    simp [hidx]

theorem ofFn_cast {α : Type*} {n m : ℕ} (e : n = m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast e i)) = List.ofFn f := by
  subst e
  rfl

/-- The dart in the actual Euclidean vertex-star order, i.e. the reverse of the
combinatorial `σ` order used by `incidentDartOfStarIndex`. -/
def starDart (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : D :=
  incidentDartOfStarIndex P v hdeg (Fin.rev i)

theorem starDart_tail (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    M.tail (starDart P v hdeg i) = v := by
  unfold starDart
  exact incidentDartOfStarIndex_tail P v hdeg (Fin.rev i)

theorem starDart_eq_of_index
    (P Q : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdegP : 3 ≤ vDeg P v) (hdegQ : 3 ≤ vDeg Q v)
    {i : Fin (starN P v + 1)} {j : Fin (starN Q v + 1)}
    (hij : HEq i j) :
    starDart P v hdegP i = starDart Q v hdegQ j := by
  cases hij
  simp [starDart, incidentDartOfStarIndex, incidentDart, starIndexToDeg,
    incidentDarts, vDeg, starN]









































































































































namespace ListCyclicOrder



















end ListCyclicOrder

















































































































namespace RotTwoBlockCert




























end RotTwoBlockCert








































































































































end ProofsInTheBook.Ch13Cauchy3D

end
end


