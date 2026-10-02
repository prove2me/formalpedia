-- Prove2me | Definitions.Def_P2MAssembly_Chapter13V2_Part2
-- name    : P2MAssembly_Chapter13V2_Part2
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T20:33:29.701406+00:00
-- url     : https://prove2.me/theorems/9d387c8a-52f2-42e0-baa3-bedb32e16a9c
-- title:
--   Spherical opening parameters and support constraints
-- statement:
--   This part continues the spherical-arm argument with interior-joint opening axes, neighboring points and opened angles. It defines support functions for nonincident vertex–edge pairs, positivity of joints, absence of nonadjacent repeated vertices, equator index sets and base-cap support functions. Retained congruence, continuity and comparison results concern these explicitly conditioned spherical configurations; no general polyhedron realization or global rigidity statement is introduced here.
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





















/-- **`SameSides` restricts to the ear.**  If the parents `A`, `B` agree on every side, their ears
`A[a..a+m]`, `B[a..a+m]` agree on every side. -/
theorem intervalArm_sameSides {N : ℕ} {A B : Fin (N + 1) → S2} {a m : ℕ} (hb : a + m ≤ N)
    (hside : ∀ i : Fin N, sideLen A i = sideLen B i) :
    SameSides (intervalArm A a m hb) (intervalArm B a m hb) := by
  intro i
  rw [intervalArm_sideLen A a m hb i, intervalArm_sideLen B a m hb i]
  exact hside ⟨a + i.val, by have := i.isLt; omega⟩

/-- **`JointLe` restricts to the ear.**  If `A`'s interior joints are `≤` `B`'s, the ears' interior
joints inherit the inequality. -/
theorem intervalArm_jointLe {N : ℕ} {A B : Fin (N + 1) → S2} {a m : ℕ} (hb : a + m ≤ N)
    (hangle : ∀ i : Fin (N - 1), jointAngle A i ≤ jointAngle B i) :
    JointLe (intervalArm A a m hb) (intervalArm B a m hb) := by
  intro i
  rw [intervalArm_jointAngle A a m hb i, intervalArm_jointAngle B a m hb i]
  exact hangle ⟨a + i.val, by have := i.isLt; omega⟩







/-- **The cut diagonal inequality (design §4).**  From `A`'s folded-flat betweenness equation at the
vanishing support `(A (i+1), A i, A j)`, the ear comparison `sDist (A (i+1))(A j) ≤ sDist (B (i+1))(B
j)`, and the equal first side `sDist (B (i+1))(B i) = sDist (A (i+1))(A i)`, the diagonal inequality
`sDist (A i)(A j) ≤ sDist (B i)(B j)` follows (spherical reverse triangle inequality on `B`'s bent
corner). -/
theorem cut_diag_le
    {Ai Aip1 Aj Bi Bip1 Bj : S2}
    (hflat : sDist Aip1 Aj = sDist Aip1 Ai + sDist Ai Aj)
    (hear : sDist Aip1 Aj ≤ sDist Bip1 Bj)
    (hside : sDist Bip1 Bi = sDist Aip1 Ai) :
    sDist Ai Aj ≤ sDist Bi Bj :=
  diag_le_of_flat_ear hflat hear hside

















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



/-- The Rodrigues rotation on `S²` fixes its axis: `rotS2 k δ k = k`. -/
theorem rotS2_axis_fixed (k : S2) (δ : ℝ) : rotS2 k δ k = k := by
  apply S2.ext; rw [rotS2_coe, rot_axis k.2]

/-- **The spherical angle is invariant under the Rodrigues rotation isometry** (`jointAngle_eq_of_rot`
of the handoff):  `sphAngle (R u)(R v)(R w) = sphAngle u v w` for `R = rotS2 k δ`.  This is the
substrate's `sphAngle_rotS2`. -/
theorem jointAngle_eq_of_rot (k : S2) (δ : ℝ) (u v w : S2) :
    sphAngle (rotS2 k δ u) (rotS2 k δ v) (rotS2 k δ w) = sphAngle u v w :=
  sphAngle_rotS2 k δ u v w



/-- **The axis joint is preserved** (the corrected `r = K` case, `HANDOFF/CH13_OPEN_FIX.md`).  For the
joint `r` whose first vertex is the axis (`r.val = K.val`), `openTail A K δ` preserves the joint angle:
the triple `(A K, A (K+1), A (K+2))` is the image of itself under the single isometry `rotS2 (A K) δ`
(the axis `A K` rewritten as its own rotated image), and the spherical angle is rotation-invariant. -/
theorem jointAngle_openTail_eq_at_axis {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n - 1)} (hr : r.val = K.val) :
    jointAngle (openTail A K δ) r = jointAngle A r := by
  have hrlt := r.isLt
  -- the axis vertex `A K` is exactly the first vertex `A ⟨r.val,_⟩` of joint r.
  have hKeq : K = (⟨r.val, by omega⟩ : Fin (n + 1)) := Fin.ext hr.symm
  -- the three vertices of joint r are A K (axis), A (K+1), A (K+2); first fixed, others rotated.
  have hv0 : openTail A K δ ⟨r.val, by omega⟩ = A ⟨r.val, by omega⟩ :=
    openTail_fixed A K δ (show r.val ≤ K.val by omega)
  have hv1 : openTail A K δ ⟨r.val + 1, by omega⟩ = rotS2 (A K) δ (A ⟨r.val + 1, by omega⟩) :=
    openTail_rot A K δ (show K.val < r.val + 1 by omega)
  have hv2 : openTail A K δ ⟨r.val + 2, by omega⟩ = rotS2 (A K) δ (A ⟨r.val + 2, by omega⟩) :=
    openTail_rot A K δ (show K.val < r.val + 2 by omega)
  -- A K = A ⟨r.val,_⟩ since r.val = K.val ; rewrite the fixed first vertex as its own rotated image.
  have hAK : A K = A (⟨r.val, by omega⟩ : Fin (n + 1)) := congrArg A hKeq
  have hfix : openTail A K δ ⟨r.val, by omega⟩ = rotS2 (A K) δ (A ⟨r.val, by omega⟩) := by
    rw [hv0, ← hAK, rotS2_axis_fixed]
  simp only [jointAngle, hfix, hv1, hv2]
  exact jointAngle_eq_of_rot (A K) δ _ _ _



/-- **`openTail` (axis vertex `K`) preserves every joint except the opened one.**  The opened joint is
`r` with `r.val + 1 = K.val` (apex `A K`); every other joint `r` (`r.val + 1 ≠ K.val`) is preserved:
the cases `r+2 ≤ K`, `r = K`, `K < r` cover them (the off-axis cases plus the axis joint of §2).  The
single excluded value `r.val + 1 = K.val` is exactly the opened joint. -/
theorem jointAngle_openTail_eq_of_ne_opened {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n - 1)} (hr : r.val + 1 ≠ K.val) :
    jointAngle (openTail A K δ) r = jointAngle A r := by
  have hrlt := r.isLt
  rcases lt_trichotomy (r.val) (K.val) with hlt | heq | hgt
  · -- r < K, and r+1 ≠ K, so r+2 ≤ K : all-fixed branch.
    exact openTail_preserves_joint_offaxis A K δ (Or.inl (by omega))
  · -- r = K : axis joint, §2.
    exact jointAngle_openTail_eq_at_axis A K δ heq
  · -- K < r : all-rotated branch.
    exact openTail_preserves_joint_offaxis A K δ (Or.inr hgt)



/-- The opening axis for the deficient joint `k : Fin (n-1)`: the apex vertex `A ⟨k+1⟩`. -/
def openingAxis {n : ℕ} (k : Fin (n - 1)) : Fin (n + 1) :=
  ⟨k.val + 1, by have := k.isLt; omega⟩

/-- **Every joint other than `k` is preserved by opening at the apex of `k`.**  Specialising §3 to the
axis `K = openingAxis k`: for any joint `r ≠ k`, `jointAngle (openTail A (openingAxis k) δ) r =
jointAngle A r`.  (The single disturbed joint `r.val + 1 = K.val` is `r = k`.) -/
theorem jointAngle_openTail_eq_of_ne {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    {r : Fin (n - 1)} (hr : r ≠ k) :
    jointAngle (openTail A (openingAxis k) δ) r = jointAngle A r := by
  apply jointAngle_openTail_eq_of_ne_opened
  -- r.val + 1 ≠ (openingAxis k).val = k.val + 1, i.e. r.val ≠ k.val, i.e. r ≠ k.
  simp only [openingAxis]
  intro hcontra
  exact hr (Fin.ext (by omega))

/-- **The deficit set after a REACH opening is `(deficitSet A B).erase k`.**  In the REACH case the
opened joint `k` reaches `B`'s value (no longer deficient), and every other joint is preserved (§3), so
the deficient joints of the opened arm are exactly those of `A` other than `k`. -/
theorem deficitSet_openTail_reach {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    (hreach : jointAngle (openTail A (openingAxis k) δ) k = jointAngle B k) :
    deficitSet (openTail A (openingAxis k) δ) B = (deficitSet A B).erase k := by
  ext r
  rw [Finset.mem_erase, mem_deficitSet]
  by_cases hrk : r = k
  · subst hrk
    -- at k: opened joint equals B's joint, so not deficient; and the `r ≠ k` side is false.
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_lt, hreach, le_refl]
  · rw [jointAngle_openTail_eq_of_ne A k δ hrk]
    rw [mem_deficitSet]
    exact ⟨fun h => ⟨hrk, h⟩, fun h => h.2⟩

/-- **The deficit count strictly decreases in the REACH branch.**  From the deficit-set erase identity
and the fact that `k` *was* deficient (`k ∈ deficitSet A B`), the cardinality drops by one. -/
theorem deficitCount_openTail_reach_lt {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    (hkdef : jointAngle A k < jointAngle B k)
    (hreach : jointAngle (openTail A (openingAxis k) δ) k = jointAngle B k) :
    deficitCount (openTail A (openingAxis k) δ) B < deficitCount A B := by
  have hk : k ∈ deficitSet A B := (mem_deficitSet).2 hkdef
  rw [deficitCount, deficitCount, deficitSet_openTail_reach A B k δ hreach]
  exact Finset.card_erase_lt_of_mem hk



/-- **Distinct open-hemisphere vertices form a short arc.**  If `p ≠ q` and both lie in the open
hemisphere `{x : 0 < ⟪h, x⟫}` (with `‖h‖ = 1`), then `ShortArc p q`: they are non-antipodal because
`p = -q` would force `⟪h, p⟫ = -⟪h, q⟫`, impossible for two positive values. -/
theorem shortArc_of_hemisphere {p q : S2} {h : E3} (hp : 0 < (⟪h, (p : E3)⟫ : ℝ))
    (hq : 0 < (⟪h, (q : E3)⟫ : ℝ)) (hne : p ≠ q) :
    ShortArc p q := by
  refine ⟨hne, ?_⟩
  intro hanti
  -- p = -q  ⟹  ⟪h, p⟫ = -⟪h, q⟫ < 0, contradicting hp.
  have : (⟪h, (p : E3)⟫ : ℝ) = -(⟪h, (q : E3)⟫ : ℝ) := by
    rw [hanti, inner_neg_right]
  linarith

/-- **The base sides at an interior axis are short arcs.**  For a strictly convex arm `A` and an
interior vertex index `K` (`1 ≤ K.val`, `K.val < n`), the chords `A K → A 0` and `A K → A (last)` are
short arcs, derived from the open-hemisphere positivity and the distinctness witnessed by the forward
diagonal support `0 < sOrient (A 0)(A K)(A last)`. -/
theorem shortArc_interior_base {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} (hK0 : 1 ≤ K.val) (hKn : K.val < n) :
    ShortArc (A K) (A 0) ∧ ShortArc (A K) (A (Fin.last n)) := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hP := hA.closed_convex
  -- the forward diagonal `A 0 → A K` strictly supports `A last` (vertex beyond it).
  have h0K : (0 : Fin (n + 1)) < K := by rw [Fin.lt_def, Fin.val_zero]; omega
  have hKl : K < Fin.last n := by rw [Fin.lt_def, Fin.val_last]; omega
  have hdiag : 0 < sOrient (A 0) (A K) (A (Fin.last n)) := cut_diagonal_supports hP h0K hKl
  -- cyclic rotations give distinctness of (A K, A 0) and (A K, A last).
  have hcyc := sOrient_cyclic (A 0) (A K) (A (Fin.last n))
  -- sOrient (A 0)(A K)(A last) = sOrient (A K)(A last)(A 0) = sOrient (A last)(A 0)(A K)
  have hpos1 : 0 < sOrient (A K) (A (Fin.last n)) (A 0) := by rw [← hcyc.1]; exact hdiag
  have hpos2 : 0 < sOrient (A (Fin.last n)) (A 0) (A K) := by rw [← hcyc.2]; exact hdiag
  have hKne0 : A K ≠ A 0 := ne_of_sOrient_pos_ac hpos1
  have hKnel : A K ≠ A (Fin.last n) := by
    -- from hpos2: sOrient (A last)(A 0)(A K) > 0 ⟹ A last ≠ A K (first ≠ third).
    exact (ne_of_sOrient_pos_ac hpos2).symm
  -- hemisphere positivity at all three vertices.
  obtain ⟨h, hhn, hhpos⟩ := hP.open_hemisphere
  exact ⟨shortArc_of_hemisphere (hhpos K) (hhpos 0) hKne0,
         shortArc_of_hemisphere (hhpos K) (hhpos (Fin.last n)) hKnel⟩

/-- **The convex oriented datum at an interior axis.**  For a strictly convex arm and interior axis
index `K`, the forward diagonal support gives `0 ≤ sOrient (A 0)(A K)(A (last))` — the convex opening
direction the mirrored keystone consumes. -/
theorem orientedDatum_interior {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} (hK0 : 1 ≤ K.val) (hKn : K.val < n) :
    0 ≤ sOrient (A 0) (A K) (A (Fin.last n)) := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have h0K : (0 : Fin (n + 1)) < K := by rw [Fin.lt_def, Fin.val_zero]; omega
  have hKl : K < Fin.last n := by rw [Fin.lt_def, Fin.val_last]; omega
  exact le_of_lt (cut_diagonal_supports hA.closed_convex h0K hKl)

/-- The endpoint of the opened arm at an interior axis: `A 0` fixed, `A (last)` rotated. -/
theorem endpt_openTail_interior {n : ℕ} (A : Fin (n + 1) → S2) {K : Fin (n + 1)} (θ : ℝ)
    (_hK0 : 1 ≤ K.val) (hKn : K.val < n) :
    endpt (openTail A K θ) = sDist (A 0) (rotS2 (A K) θ (A (Fin.last n))) := by
  unfold endpt
  rw [openTail_zero, openTail_rot A K θ (show K.val < (Fin.last n).val by rw [Fin.val_last]; omega)]

/-- **Interior-axis endpoint monotonicity (the corrected design §5 endpoint bound).**  For a strictly
convex arm `A` and an interior axis index `K` (`1 ≤ K.val`, `K.val < n`), opening the tail by `-θ`
(`0 ≤ θ`, within the great-semicircle range at the base triangle) does not decrease the arm endpoint:
`endpt A ≤ endpt (openTail A K (-θ))`.  This is the substrate's `reach_endpoint_mono_arm` re-proved at
an interior axis, via the axis-generic base-triangle engine. -/
theorem endpt_openTail_interior_mono {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} (hK0 : 1 ≤ K.val) (hKn : K.val < n) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθπ : θ + sphAngle (A 0) (A K) (A (Fin.last n)) ≤ Real.pi) :
    endpt A ≤ endpt (openTail A K (-θ)) := by
  obtain ⟨hka, hkt⟩ := shortArc_interior_base hA hK0 hKn
  have hsign : (0 : ℝ) ≤ (⟪tangentTo (A K) (A 0), cross (A K : E3) (tangentTo (A K) (A (Fin.last n)))⟫ : ℝ) :=
    orientedSign_neg_of_support (orientedDatum_interior hA hK0 hKn)
  have hangle : sphAngle (A 0) (A K) (A (Fin.last n))
      ≤ sphAngle (A 0) (A K) (rotS2 (A K) (-θ) (A (Fin.last n))) :=
    openedAngle_ge_of_oriented_neg (A K) (A 0) (A (Fin.last n)) hka hkt hsign hθ0 hθπ
  have hmono : sDist (A 0) (A (Fin.last n))
      ≤ sDist (A 0) (rotS2 (A K) (-θ) (A (Fin.last n))) :=
    reach_base_endpoint_mono (A K) (A 0) (A (Fin.last n)) hka hkt hangle
  -- endpt A = sDist (A 0)(A last); endpt (openTail ..) = sDist (A 0)(rotS2 (A K) (-θ)(A last)).
  rw [endpt_openTail_interior A (-θ) hK0 hKn]
  show sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (rotS2 (A K) (-θ) (A (Fin.last n)))
  exact hmono





















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



/-- The incoming neighbour `A k'` of the deficient joint `k` (vertex index `k`). -/
def jointPrev {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) : S2 :=
  A ⟨k.val, by have := k.isLt; omega⟩

/-- The outgoing neighbour `A ⟨k+2⟩` of the deficient joint `k` (vertex index `k+2`, in the rotated
tail). -/
def jointNext {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) : S2 :=
  A ⟨k.val + 2, by have := k.isLt; omega⟩

/-- The opened interior joint-`k` angle as a function of the opening angle `θ`:
`θ ↦ sphAngle (A k')(A K)(rotS2 (A K) θ (A ⟨k+2⟩))`, with `K = openingAxis k`. -/
def openedInteriorJointAngle {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (θ : ℝ) : ℝ :=
  sphAngle (jointPrev A k) (A (openingAxis k)) (rotS2 (A (openingAxis k)) θ (jointNext A k))

/-- At `θ = 0` the opened interior joint angle is the original joint-`k` angle of `A`. -/
theorem openedInteriorJointAngle_zero {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    openedInteriorJointAngle A k 0 = jointAngle A k := by
  simp only [openedInteriorJointAngle, jointAngle, jointPrev, jointNext, openingAxis]
  rw [show rotS2 (A ⟨k.val + 1, by have := k.isLt; omega⟩) 0 (A ⟨k.val + 2, by have := k.isLt; omega⟩)
      = A ⟨k.val + 2, by have := k.isLt; omega⟩ by apply S2.ext; rw [rotS2_coe, rot_zero]]

/-- **The opened interior joint angle is continuous in `θ`.**  The two base sides `A K → A k'` and
`A K → A ⟨k+2⟩` are short arcs (the incoming edge and the joint's far edge of the strictly convex arm);
the substrate's generic `continuous_openedJointAngle` then applies with `k = A K`, `p = A k'`,
`q = A ⟨k+2⟩`. -/
theorem continuous_openedInteriorJointAngle {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    Continuous (openedInteriorJointAngle A k) :=
  continuous_openedJointAngle hka hkt



/-- The `θ`-coordinate of an opened vertex: continuous in `θ` (constant if fixed, a rotation coordinate
if rotated). -/
theorem continuous_openTail_coord {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (x : Fin (n + 1))
    (c : Fin 3) :
    Continuous (fun θ : ℝ => ((openTail A K θ x : S2) : E3) c) := by
  by_cases hx : x.val ≤ K.val
  · simp only [openTail_fixed A _ _ hx]
    exact continuous_const
  · simp only [openTail_rot A K _ (show K.val < x.val by omega), rotS2_coe]
    exact continuous_rot_coord (A K : E3) (A x : E3) c

/-- The interior support determinant of a triple `(i, j, l)` under the interior opening, as a function
of `θ`: `θ ↦ sOrient (openTail A K θ i)(openTail A K θ j)(openTail A K θ l)`. -/
def interiorSupport {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (ijl : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) : ℝ → ℝ :=
  fun θ => sOrient (openTail A K θ ijl.1) (openTail A K θ ijl.2.1) (openTail A K θ ijl.2.2)



/-- **Each interior support is continuous in `θ`.**  `sOrient = det3` of the three opened vertices,
each of whose coordinates is `θ`-continuous (`continuous_openTail_coord`); `det3` is a polynomial in the
nine coordinates. -/
theorem continuous_interiorSupport {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (ijl : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) :
    Continuous (interiorSupport A K ijl) := by
  obtain ⟨i, j, l⟩ := ijl
  show Continuous (fun θ : ℝ =>
    det3 ((openTail A K θ i : S2) : E3) ((openTail A K θ j : S2) : E3)
      ((openTail A K θ l : S2) : E3))
  simp only [det3]
  have hi := fun c => continuous_openTail_coord A K i c
  have hj := fun c => continuous_openTail_coord A K j c
  have hl := fun c => continuous_openTail_coord A K l c
  exact
    (((hi 0).mul (((hj 1).mul (hl 2)).sub ((hj 2).mul (hl 1)))).sub
      ((hi 1).mul (((hj 0).mul (hl 2)).sub ((hj 2).mul (hl 0))))).add
      ((hi 2).mul (((hj 0).mul (hl 1)).sub ((hj 1).mul (hl 0))))













































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





/-- **The diagonal inequality from the folded-flat ear (design §4 `diag_le`).**  From `A`'s folded-flat
betweenness equation at the vanishing support `(A (i+1), A i, A j)` (`A i` between `A (i+1)` and
`A j`), the ear comparison `hEar`, and the equal first side `sDist (B (i+1))(B i) = sDist (A (i+1))(A i)`,
the diagonal inequality `sDist (A i)(A j) ≤ sDist (B i)(B j)` follows by `cut_diag_le`
(the spherical reverse triangle inequality on `B`'s bent corner).

This is the banked `SphericalSZStepClose.cut_diag_le`, re-exported with the folded-flat equation made
explicit so the §6 dispatch sees the full design §4 chain. -/
theorem diag_le_of_foldedFlat
    {Ai Aip1 Aj Bi Bip1 Bj : S2}
    (hcol : (Ai : E3) ∈ Submodule.span NNReal ({(Aip1 : E3), (Aj : E3)} : Set E3))
    (hear : sDist Aip1 Aj ≤ sDist Bip1 Bj)
    (hside : sDist Bip1 Bi = sDist Aip1 Ai) :
    sDist Ai Aj ≤ sDist Bi Bj :=
  cut_diag_le (foldedFlat_dist_eq hcol) hear hside

























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



/-- A point in the affine span of two others has vanishing triple product. -/
theorem det3_span (u v : E3) (r s : ℝ) :
    det3 u v (r • u + s • v) = 0 := by
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **Antiparallel (or parallel) tangents force collinearity.**  If the tangent direction of `w` at `v`
is a scalar multiple of the tangent direction of `u` at `v`, then `u, v, w` are great-circle collinear
(`det3 u v w = 0`). -/
theorem det3_zero_of_antiparallel (u v w : S2) (r : ℝ)
    (heq : tangentTo v w = r • tangentTo v u) :
    det3 (u : E3) (v : E3) (w : E3) = 0 := by
  rw [tangentTo_eq, tangentTo_eq] at heq
  rw [smul_sub, smul_smul] at heq
  have hwsub : (w : E3) = r • (u : E3) + (sInner w v - r * sInner u v) • (v : E3) := by
    have hh : (w : E3) = (r • (u : E3) - (r * sInner u v) • (v : E3)) + sInner w v • (v : E3) := by
      rw [← heq]; abel
    rw [hh]; module
  rw [hwsub, det3_span]

/-- **A straight spherical angle forces collinearity.**  `sphAngle u v w = π` ⟹ `det3 u v w = 0`
(the three sphere points lie on a common great circle, `v` between `u` and `w`), via
`InnerProductGeometry.angle_eq_pi_iff`.  The local non-degeneracy fact the substrate lacked. -/
theorem det3_zero_of_sphAngle_pi (u v w : S2) (h : sphAngle u v w = Real.pi) :
    det3 (u : E3) (v : E3) (w : E3) = 0 := by
  rw [sphAngle, InnerProductGeometry.angle_eq_pi_iff] at h
  obtain ⟨_, r, _, heq⟩ := h
  exact det3_zero_of_antiparallel u v w r heq

/-- **Contrapositive: a non-degenerate triple bends strictly below `π`.**  `det3 u v w ≠ 0` ⟹
`sphAngle u v w < π`. -/
theorem sphAngle_lt_pi_of_det3_ne (u v w : S2) (h : det3 (u : E3) (v : E3) (w : E3) ≠ 0) :
    sphAngle u v w < Real.pi := by
  rcases lt_or_eq_of_le (sphAngle_le_pi u v w) with hlt | heq
  · exact hlt
  · exact absurd (det3_zero_of_sphAngle_pi u v w heq) h

/-- **Strict polygon joints are `< π`.**  Each interior joint of a strictly convex arm `B` is strictly
below the straight angle (strict non-incidence ⟹ the joint triple has `det3 > 0`, so by the §1 bridge
the angle is `< π`). -/
theorem strict_jointAngle_lt_pi {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (k : Fin (n - 1)) :
    jointAngle B k < Real.pi := by
  have hki : k.val < n - 1 := k.isLt
  have h2 : 2 ≤ n := hB.two_le
  rw [jointAngle]
  refine sphAngle_lt_pi_of_det3_ne _ _ _ ?_
  have hP := hB.closed_convex.strict_nonincident
  have hik : k.val < n + 1 := by omega
  have hi1 : k.val + 1 < n + 1 := by omega
  have hi2 : k.val + 2 < n + 1 := by omega
  have key := hP ⟨k.val, hik⟩ ⟨k.val + 2, hi2⟩
  have hne1 : (⟨k.val + 2, hi2⟩ : Fin (n + 1)) ≠ ⟨k.val, hik⟩ := by
    intro h; have hv := Fin.val_eq_of_eq h; simp only [] at hv; omega
  have hadd1 : (⟨k.val, hik⟩ : Fin (n + 1)) + 1 = ⟨k.val + 1, hi1⟩ := by
    apply Fin.ext; simp [Fin.add_def]; omega
  have hne2 : (⟨k.val + 2, hi2⟩ : Fin (n + 1)) ≠ ⟨k.val, hik⟩ + 1 := by
    rw [hadd1]; intro h; have hv := Fin.val_eq_of_eq h; simp only [] at hv; omega
  have hpos := key hne1 hne2
  rw [hadd1] at hpos
  unfold sOrient at hpos
  intro hz; rw [hz] at hpos; exact lt_irrefl 0 hpos

/-- **`A` is not a flat fan.**  Under `JointLe A B` and strict `B`, every interior joint of `A` is
`< π`.  This is the premise restriction that EXCLUDES the prior flat-fan counterexamples. -/
theorem jointAngle_lt_pi {n : ℕ} {A B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (k : Fin (n - 1)) :
    jointAngle A k < Real.pi :=
  lt_of_le_of_lt (hangle k) (strict_jointAngle_lt_pi hB k)

















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



/-- `det3` is alternating: a transposition of the last two arguments flips the sign. -/
theorem det3_swap23 (a b c : E3) : det3 a c b = - det3 a b c := by
  simp only [det3]; ring















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





theorem cross_sub_right' (a b c : E3) : cross a (b - c) = cross a b - cross a c := by
  rw [sub_eq_add_neg, cross_add_right, sub_eq_add_neg]
  congr 1
  rw [show (-c) = (-1:ℝ) • c by module, cross_smul_right]; module

/-- For `u, v ⊥ h`, the cross product `u ×₃ v` is parallel to `h`: `h ×₃ (u ×₃ v) = 0`. -/
theorem cross_h_cross {h u v : E3} (hu : (⟪h, u⟫ : ℝ) = 0) (hv : (⟪h, v⟫ : ℝ) = 0) :
    cross h (cross u v) = 0 := by
  rw [cross_cross, hu, hv]; simp

/-- `⟪a, u×v⟫ • h = ⟪a, h⟫ • (u×v)` for `u, v ⊥ h`: the parallelism `u×v ∥ h`, scalarised. -/
theorem apex_parallel {h u v a : E3} (hu : (⟪h, u⟫ : ℝ) = 0) (hv : (⟪h, v⟫ : ℝ) = 0) :
    (⟪a, cross u v⟫ : ℝ) • h = (⟪a, h⟫ : ℝ) • cross u v := by
  have h0 : cross h (cross u v) = 0 := cross_h_cross hu hv
  have key : cross a (cross h (cross u v)) = (⟪a, cross u v⟫ : ℝ) • h - (⟪a, h⟫ : ℝ) • cross u v :=
    cross_cross a h (cross u v)
  rw [h0] at key
  rw [show cross a (0:E3) = 0 from by
    have := cross_smul_right 0 a (0:E3); simpa using this] at key
  linear_combination (norm := module) -key



/-- Lagrange: `‖u×v‖² = ‖u‖²‖v‖² − ⟪u,v⟫²`. -/
theorem norm_cross_sq (u v : E3) :
    (⟪cross u v, cross u v⟫ : ℝ) = ‖u‖^2 * ‖v‖^2 - (⟪u, v⟫:ℝ)^2 := by
  rw [inner_cross_cross, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm v u]; ring

/-- **`sin² + cos²` (area form).**  `(det3 h u v)² = ‖h‖²(‖u‖²‖v‖² − ⟪u,v⟫²)` for `u, v ⊥ h`. -/
theorem det3h_sq {h u v : E3} (hu : (⟪h, u⟫ : ℝ) = 0) (hv : (⟪h, v⟫ : ℝ) = 0) :
    (det3 h u v)^2 = ‖h‖^2 * (‖u‖^2 * ‖v‖^2 - (⟪u, v⟫:ℝ)^2) := by
  have hp := apex_parallel (h := h) (u := u) (v := v) (a := h) hu hv
  rw [real_inner_self_eq_norm_sq, inner_cross_eq_det3] at hp
  have hn := congrArg (fun w => (⟪w, w⟫ : ℝ)) hp
  simp only [inner_smul_left, inner_smul_right, conj_trivial] at hn
  rw [real_inner_self_eq_norm_sq, norm_cross_sq] at hn
  rcases eq_or_lt_of_le (sq_nonneg ‖h‖) with he | hpos
  · have hh0 : h = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg h])
    subst hh0; simp [det3]
  · nlinarith [hn, hpos]












/-- Normalised cosine of the angle from `b` to `p` (at the apex). -/
def ncos (b p : E3) : ℝ := (⟪b,p⟫:ℝ) / (‖b‖ * ‖p‖)



















































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








































/-- `det3` with a third argument shifted along a vector: `det3 a b (c + w) = det3 a b c + det3 a b w`. -/
theorem det3_add_right (a b c w : E3) : det3 a b (c + w) = det3 a b c + det3 a b w := by
  simp only [det3, PiLp.add_apply]; ring

/-- `det3` with a smul third argument: `det3 a b (t • c) = t * det3 a b c`. -/
theorem det3_smul_right (a b c : E3) (t : ℝ) : det3 a b (t • c) = t * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring











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



/-- **Positive interior joints** — the left-arm strengthening that excises the zigzag stratum. -/
def PositiveJoints {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∀ k : Fin (n - 1), 0 < jointAngle A k







/-- **A zero spherical angle forces collinearity** (`angle = 0` ⟹ positively parallel tangents ⟹
`det3 = 0`), via `InnerProductGeometry.angle_eq_zero_iff` and the proven
`det3_zero_of_antiparallel`. -/
theorem det3_zero_of_sphAngle_zero (u v w : S2) (h : sphAngle u v w = 0) :
    det3 (u : E3) (v : E3) (w : E3) = 0 := by
  rw [sphAngle, InnerProductGeometry.angle_eq_zero_iff] at h
  obtain ⟨_, r, _, heq⟩ := h
  exact det3_zero_of_antiparallel u v w r heq

/-- **Contrapositive: a non-degenerate triple bends strictly above `0`.** -/
theorem sphAngle_pos_of_det3_ne (u v w : S2) (h : det3 (u : E3) (v : E3) (w : E3) ≠ 0) :
    0 < sphAngle u v w := by
  rcases lt_or_eq_of_le (sphAngle_nonneg u v w) with hlt | heq
  · exact hlt
  · exact absurd (det3_zero_of_sphAngle_zero u v w heq.symm) h



/-- **Strict polygon joints are `> 0`.**  Mirror of `strict_jointAngle_lt_pi`: the joint triple of
a strictly convex arm has `det3 > 0` (strict non-incidence at `j = k + 2`), so the angle is
positive by the §2 bridge. -/
theorem strict_jointAngle_pos {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (k : Fin (n - 1)) :
    0 < jointAngle B k := by
  have hki : k.val < n - 1 := k.isLt
  have h2 : 2 ≤ n := hB.two_le
  rw [jointAngle]
  refine sphAngle_pos_of_det3_ne _ _ _ ?_
  have hP := hB.closed_convex.strict_nonincident
  have hik : k.val < n + 1 := by omega
  have hi1 : k.val + 1 < n + 1 := by omega
  have hi2 : k.val + 2 < n + 1 := by omega
  have hne1 : (⟨k.val + 2, hi2⟩ : Fin (n + 1)) ≠ ⟨k.val, hik⟩ := by
    intro h; have := congrArg Fin.val h; simp at this
  have hne2 : (⟨k.val + 2, hi2⟩ : Fin (n + 1)) ≠ (⟨k.val, hik⟩ : Fin (n + 1)) + 1 := by
    intro h
    have hsucc : ((⟨k.val, hik⟩ : Fin (n + 1)) + 1) = (⟨k.val + 1, hi1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt hi1]
    rw [hsucc] at h
    have := congrArg Fin.val h; simp at this
  have key := hP ⟨k.val, hik⟩ ⟨k.val + 2, hi2⟩ hne1 hne2
  have hsucc : ((⟨k.val, hik⟩ : Fin (n + 1)) + 1) = (⟨k.val + 1, hi1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp [Fin.add_def, Nat.mod_eq_of_lt hi1]
  rw [hsucc] at key
  exact ne_of_gt key

/-- **Strict arms have positive joints** — the bridge `armMono_of_MainPlus` needs. -/
theorem strictConvexSphArm_positiveJoints {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) : PositiveJoints B :=
  fun k => strict_jointAngle_pos hB k





/-- **Interval sub-arms inherit positive joints**: the ear's interior joints are exactly the
parent's joints `a + i` (`intervalArm_jointAngle`). -/
theorem intervalArm_positiveJoints {N : ℕ} {A : Fin (N + 1) → S2} (a m : ℕ) (hb : a + m ≤ N)
    (hpos : PositiveJoints A) :
    PositiveJoints (intervalArm A a m hb) := by
  intro i
  rw [intervalArm_jointAngle A a m hb i]
  exact hpos ⟨a + i.val, by have := i.isLt; omega⟩







/-- **Endpoint bound from a folded-flat tail.**  If the last vertex `An` is folded flat between
`An1` (the second-to-last) and `A0` (`hflatTail`), the diagonal inequality holds at `(0, n−1)`
(`hdiag`), and the last sides agree (`hsideLast`), then the endpoint bound follows from the
spherical triangle inequality on `B`'s corner.  Stated pointwise on the six sphere points, so it
can be instantiated by any index bookkeeping. -/
theorem endpoint_le_of_tail_fold {A0 An1 An B0 Bn1 Bn : S2}
    (hflatTail : sDist A0 An1 = sDist A0 An + sDist An An1)
    (hdiag : sDist A0 An1 ≤ sDist B0 Bn1)
    (hsideLast : sDist An An1 = sDist Bn Bn1) :
    sDist A0 An ≤ sDist B0 Bn := by
  have htri : sDist B0 Bn1 ≤ sDist B0 Bn + sDist Bn Bn1 := sDist_triangle B0 Bn Bn1
  have h1 : sDist A0 An = sDist A0 An1 - sDist An An1 := by linarith
  rw [h1, hsideLast]
  linarith


















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



/-- **Tangent rays at the apex are positively parallel under betweenness.**  If `p ∈ span≥0 {v, w}`
(the betweenness point `p` on the minor arc from `v` to `w`) and the arc `(v, p)` is short
(`tangentTo v p ≠ 0`), then `tangentTo v p` is a nonnegative multiple of `tangentTo v w`: writing
`p = s • v + t • w` (`s, t ≥ 0`), `tangentTo v p = projOut v p = s • projOut v v + t • projOut v w
= t • tangentTo v w` (since `projOut v v = 0`). -/
theorem tangentTo_eq_nnsmul_of_betweenness {p v w : S2}
    (hcol : (p : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)) :
    ∃ t : ℝ, 0 ≤ t ∧ tangentTo v p = t • tangentTo v w := by
  rw [Submodule.mem_span_pair] at hcol
  obtain ⟨s, t, hst⟩ := hcol
  -- `(↑s) • v + (↑t) • w = p` as real-scalar combination.
  have hst' : (s : ℝ) • (v : E3) + (t : ℝ) • (w : E3) = (p : E3) := by
    have := hst
    rwa [NNReal.smul_def, NNReal.smul_def] at this
  refine ⟨(t : ℝ), t.2, ?_⟩
  -- apply `projOut (v:E3)` to both sides.
  have hv0 : (v : E3) ≠ 0 := by
    intro h; have := v.2; rw [h, norm_zero] at this; norm_num at this
  have hkey : projOut (v : E3) (p : E3)
      = (s : ℝ) • projOut (v : E3) (v : E3) + (t : ℝ) • projOut (v : E3) (w : E3) := by
    rw [← hst', projOut_add, projOut_smul, projOut_smul]
  rw [projOut_self (v : E3) hv0, smul_zero, zero_add] at hkey
  -- `tangentTo v p = projOut v p` and `tangentTo v w = projOut v w`.
  show projOut (v : E3) (p : E3) = (t : ℝ) • projOut (v : E3) (w : E3)
  exact hkey

/-- **Folded-flat betweenness forces the apex spherical angle to `0`.**  If `p ∈ span≥0 {v, w}` and
the arc `(v, p)` is short, then `sphAngle p v w = 0` — the apex `v` sees `p` and `w` in the *same*
tangent direction.  (`tangentTo v p = t • tangentTo v w` with `t ≥ 0`; since `tangentTo v p ≠ 0`,
necessarily `t > 0` and `tangentTo v w ≠ 0`, so `tangentTo v w = t⁻¹ • tangentTo v p` with `t⁻¹ > 0`,
the positive-parallel condition of `InnerProductGeometry.angle_eq_zero_iff`.) -/
theorem sphAngle_zero_of_betweenness {p v w : S2}
    (hsa : ShortArc v p)
    (hcol : (p : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)) :
    sphAngle p v w = 0 := by
  obtain ⟨t, htnn, htvp⟩ := tangentTo_eq_nnsmul_of_betweenness hcol
  -- `tangentTo v p ≠ 0` since the arc `(v, p)` is short.
  have hvp0 : (tangentTo v p : E3) ≠ 0 := (tangentTo_ne_zero_iff v p).2 hsa
  -- from `tangentTo v p = t • tangentTo v w` and `tangentTo v p ≠ 0`: `t ≠ 0` and `tangentTo v w ≠ 0`.
  have ht0 : t ≠ 0 := by
    intro h; rw [h, zero_smul] at htvp; exact hvp0 htvp
  have htpos : 0 < t := lt_of_le_of_ne htnn (Ne.symm ht0)
  have hvw0 : (tangentTo v w : E3) ≠ 0 := by
    intro h; rw [h, smul_zero] at htvp; exact hvp0 htvp
  -- `sphAngle p v w = angle (tangentTo v p) (tangentTo v w) = 0`.
  rw [sphAngle, InnerProductGeometry.angle_eq_zero_iff]
  refine ⟨hvp0, t⁻¹, by positivity, ?_⟩
  rw [htvp, smul_smul, inv_mul_cancel₀ ht0, one_smul]

/-- **(Brick 1) The last-corner betweenness forces the apex joint to `0`.**  For an arm
`A : Fin (N + 1) → S2`, the folded-flat betweenness `A ⟨k⟩ ∈ span≥0 {A ⟨k+1⟩, A ⟨k+2⟩}` at a
last-corner triple (`k + 2 ≤ N`), together with the short edge `(A ⟨k+1⟩, A ⟨k⟩)`, forces the interior
joint at apex `A ⟨k+1⟩` — i.e. `jointAngle A ⟨k, _⟩` — to angle `0`.

The joint index is `k : Fin (N - 1)` (apex vertex `A ⟨k+1⟩`, neighbours `A ⟨k⟩` and `A ⟨k+2⟩`); the
betweenness point `A ⟨k⟩` lies on the minor arc between the apex's two neighbours, so the apex sees them
in the same tangent direction (`sphAngle_zero_of_betweenness`). -/
theorem lastCorner_hcol_forces_joint_zero {N : ℕ} {A : Fin (N + 1) → S2} {k : ℕ}
    (hk2 : k + 2 ≤ N)
    (hsa : ShortArc (A ⟨k + 1, by omega⟩) (A ⟨k, by omega⟩))
    (hcol : (A ⟨k, by omega⟩ : E3)
      ∈ Submodule.span NNReal
        ({(A ⟨k + 1, by omega⟩ : E3), (A ⟨k + 2, by omega⟩ : E3)} : Set E3)) :
    jointAngle A ⟨k, by omega⟩ = 0 := by
  rw [jointAngle]
  -- `jointAngle A ⟨k⟩ = sphAngle (A ⟨k⟩) (A ⟨k+1⟩) (A ⟨k+2⟩)`; apex `v = A ⟨k+1⟩`, between point
  -- `p = A ⟨k⟩`, far point `w = A ⟨k+2⟩`.
  exact sphAngle_zero_of_betweenness (p := A ⟨k, by omega⟩) (v := A ⟨k + 1, by omega⟩)
    (w := A ⟨k + 2, by omega⟩) hsa hcol










































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



/-- A strict orientation `0 < sOrient a b c` forces `a ≠ b` (else `det3 a a c = 0`). -/
theorem ne_of_sOrient_pos_ab {a b c : S2} (h : 0 < sOrient a b c) : a ≠ b := by
  intro he
  apply (ne_of_gt h).symm
  rw [sOrient, he, det3_self_left]



/-- The interior-opened vertex `openTail A K θ r` as a *vector-valued* continuous function of `θ`. -/
theorem continuous_openTail_vec {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (r : Fin (n + 1)) :
    Continuous (fun θ : ℝ => ((openTail A K θ r : S2) : E3)) := by
  by_cases hx : r.val ≤ K.val
  · simp only [openTail_fixed A _ _ hx]
    exact continuous_const
  · simp only [openTail_rot A K _ (show K.val < r.val by omega), rotS2_coe]
    exact continuous_rot (A K : E3) (A r : E3)









/-- A non-incident edge–vertex pair: edge `(c.1, c.1+1)` and a vertex `c.2` off that edge. -/
def NonIncident (n : ℕ) : Type :=
  {c : Fin (n + 1) × Fin (n + 1) // c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}

instance (n : ℕ) : Finite (NonIncident n) := by
  unfold NonIncident; infer_instance

/-- The support constraint at the non-incident pair `c`:
`θ ↦ sOrient (Aδ c.i)(Aδ (c.i+1))(Aδ c.j)`. -/
def supportConstraint {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (c : NonIncident n) : ℝ → ℝ :=
  interiorSupport A K (c.1.1, c.1.1 + 1, c.1.2)

/-- The support constraint is continuous in `θ`. -/
theorem continuous_supportConstraint {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (c : NonIncident n) : Continuous (supportConstraint A K c) :=
  continuous_interiorSupport A K (c.1.1, c.1.1 + 1, c.1.2)

/-- The support constraint unfolds to the opened-arm orientation. -/
theorem supportConstraint_apply {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (c : NonIncident n)
    (θ : ℝ) :
    supportConstraint A K c θ
      = sOrient (openTail A K θ c.1.1) (openTail A K θ (c.1.1 + 1)) (openTail A K θ c.1.2) := rfl

































/-- **Interior reach persistence (general form).**  If at angle `δ` every non-incident support of the
interior-opened arm is strictly positive (`hmix`) and the fixed-`h₀` hemisphere margin is strictly
positive at every vertex (`hhem`, `‖h₀‖ = 1`), then `openTail A K δ` is a `StrictConvexSphArm`.  The
`edge_short` field is derived from the hemisphere positivity (distinct open-hemisphere vertices form a
short arc) together with a strict support (edge endpoints distinct, via vertex `i+2`); `edge_support`
is the weak form of `hmix`. -/
theorem reach_strictConvex_interior {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} {δ : ℝ} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ)) :
    StrictConvexSphArm (openTail A K δ) := by
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  -- distinctness of edge endpoints: pick the non-incident vertex `i + 2`.
  have hedge : ∀ i : Fin (n + 1), ShortArc (openTail A K δ i) (openTail A K δ (i + 1)) := by
    intro i
    have hi := i.isLt
    have h2v : ((2 : Fin (n + 1)) : ℕ) = 2 := by simp; omega
    have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by simp; omega
    have e2 : ((i + 2 : Fin (n + 1)) : ℕ) = (↑i + 2) % (n + 1) := by rw [Fin.val_add, h2v]
    have e1 : ((i + 1 : Fin (n + 1)) : ℕ) = (↑i + 1) % (n + 1) := by rw [Fin.val_add, h1v]
    have hni0 : (i + 2 : Fin (n + 1)) ≠ i := by
      intro he
      have h := congrArg Fin.val he
      rw [e2] at h
      rcases Nat.lt_or_ge (↑i + 2) (n + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h; omega
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h; omega
    have hni1 : (i + 2 : Fin (n + 1)) ≠ i + 1 := by
      intro he
      have h := congrArg Fin.val he
      rw [e2, e1] at h
      rcases Nat.lt_or_ge (↑i + 2) (n + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at h; omega
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
        rcases Nat.lt_or_ge (↑i + 1) (n + 1) with hlt1 | hge1
        · rw [Nat.mod_eq_of_lt hlt1] at h; omega
        · rw [Nat.mod_eq_sub_mod hge1, Nat.mod_eq_of_lt (by omega)] at h; omega
    have hpos := hmix i (i + 2) hni0 hni1
    exact shortArc_of_hemisphere (hhem i) (hhem (i + 1)) (ne_of_sOrient_pos_ab hpos)
  refine { two_le := hA.two_le, closed_convex := ?_ }
  refine { three_le := h3
           edge_short := hedge
           edge_support := ?_
           strict_nonincident := hmix
           open_hemisphere := ⟨h₀, hnorm, hhem⟩ }
  intro i j
  by_cases hji : j = i
  · subst hji; rw [sOrient, det3_self_right]
  · by_cases hji1 : j = i + 1
    · subst hji1; rw [sOrient, det3_self_mid]
    · exact le_of_lt (hmix i j hji hji1)













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



/-- **Frame-coordinate determination.**  Two vectors with equal inner products against a frame
`(p, q, p × q)` (with `p × q ≠ 0`) are equal.  Proved directly from the bac–cab identity
(`cross_cross`) and the Lagrange identity (`norm_sq_cross`), avoiding all basis machinery. -/
theorem eq_of_inner_frame_eq {p q x y : E3} (h : cross p q ≠ 0)
    (hp : (⟪p, x⟫ : ℝ) = ⟪p, y⟫) (hq : (⟪q, x⟫ : ℝ) = ⟪q, y⟫)
    (hc : (⟪cross p q, x⟫ : ℝ) = ⟪cross p q, y⟫) : x = y := by
  rw [← sub_eq_zero]
  -- w := x - y is orthogonal to p, q, cross p q; show w = 0.
  set w := x - y with hw
  have hwp : (⟪w, p⟫ : ℝ) = 0 := by
    have : (⟪w, p⟫ : ℝ) = ⟪p, x⟫ - ⟪p, y⟫ := by
      rw [hw, inner_sub_left, real_inner_comm x p, real_inner_comm y p]
    rw [this, hp, sub_self]
  have hwq : (⟪w, q⟫ : ℝ) = 0 := by
    have : (⟪w, q⟫ : ℝ) = ⟪q, x⟫ - ⟪q, y⟫ := by
      rw [hw, inner_sub_left, real_inner_comm x q, real_inner_comm y q]
    rw [this, hq, sub_self]
  have hwc : (⟪w, cross p q⟫ : ℝ) = 0 := by
    have : (⟪w, cross p q⟫ : ℝ) = ⟪cross p q, x⟫ - ⟪cross p q, y⟫ := by
      rw [hw, inner_sub_left, real_inner_comm x (cross p q), real_inner_comm y (cross p q)]
    rw [this, hc, sub_self]
  -- bac–cab: cross w (cross p q) = ⟪w,q⟫ • p − ⟪w,p⟫ • q = 0.
  have hcwm : cross w (cross p q) = 0 := by
    rw [SphericalRotation.cross_cross, hwp, hwq, zero_smul, zero_smul, sub_zero]
  -- Lagrange: ‖cross w (p×q)‖² = ‖w‖²‖p×q‖² − ⟪w,p×q⟫².  LHS = 0, ⟪w,p×q⟫ = 0.
  have hlag := norm_sq_cross w (cross p q)
  rw [hcwm, norm_zero, hwc] at hlag
  have hmpos : (0 : ℝ) < ‖cross p q‖ ^ 2 := by
    have hne : ‖cross p q‖ ≠ 0 := by simpa [norm_eq_zero] using h
    positivity
  have hw2 : ‖w‖ ^ 2 = 0 := by nlinarith [hlag, hmpos, sq_nonneg (‖w‖)]
  have hwz : ‖w‖ = 0 := by nlinarith [hw2, norm_nonneg w]
  exact norm_eq_zero.mp hwz



/-- **Gram-determinant identity.**  `det3 x y z ^ 2` is a polynomial in the six pairwise inner
products of `x, y, z` (the determinant of their Gram matrix). -/
theorem det3_sq_eq_gram (x y z : E3) :
    det3 x y z ^ 2 =
      (⟪x, x⟫ : ℝ) * (⟪y, y⟫ * ⟪z, z⟫ - ⟪y, z⟫ * ⟪z, y⟫)
        - ⟪x, y⟫ * (⟪y, x⟫ * ⟪z, z⟫ - ⟪y, z⟫ * ⟪z, x⟫)
        + ⟪x, z⟫ * (⟪y, x⟫ * ⟪z, y⟫ - ⟪y, y⟫ * ⟪z, x⟫) := by
  rw [det3]
  simp only [inner_eq_coord]
  ring

/-- If two triples have the same Gram matrix entries, their `det3`s have equal squares. -/
theorem det3_sq_congr {x y z x' y' z' : E3}
    (hxx : (⟪x, x⟫ : ℝ) = ⟪x', x'⟫) (hxy : (⟪x, y⟫ : ℝ) = ⟪x', y'⟫)
    (hxz : (⟪x, z⟫ : ℝ) = ⟪x', z'⟫) (hyx : (⟪y, x⟫ : ℝ) = ⟪y', x'⟫)
    (hyy : (⟪y, y⟫ : ℝ) = ⟪y', y'⟫) (hyz : (⟪y, z⟫ : ℝ) = ⟪y', z'⟫)
    (hzx : (⟪z, x⟫ : ℝ) = ⟪z', x'⟫) (hzy : (⟪z, y⟫ : ℝ) = ⟪z', y'⟫)
    (hzz : (⟪z, z⟫ : ℝ) = ⟪z', z'⟫) :
    det3 x y z ^ 2 = det3 x' y' z' ^ 2 := by
  rw [det3_sq_eq_gram, det3_sq_eq_gram, hxx, hxy, hxz, hyx, hyy, hyz, hzx, hzy, hzz]

/-- **Sign-pinned `det3` congruence.**  Two triples with equal Gram entries and both strictly
positively oriented (positive `det3`) have *equal* `det3`. -/
theorem det3_congr_of_pos {x y z x' y' z' : E3}
    (hxx : (⟪x, x⟫ : ℝ) = ⟪x', x'⟫) (hxy : (⟪x, y⟫ : ℝ) = ⟪x', y'⟫)
    (hxz : (⟪x, z⟫ : ℝ) = ⟪x', z'⟫) (hyx : (⟪y, x⟫ : ℝ) = ⟪y', x'⟫)
    (hyy : (⟪y, y⟫ : ℝ) = ⟪y', y'⟫) (hyz : (⟪y, z⟫ : ℝ) = ⟪y', z'⟫)
    (hzx : (⟪z, x⟫ : ℝ) = ⟪z', x'⟫) (hzy : (⟪z, y⟫ : ℝ) = ⟪z', y'⟫)
    (hzz : (⟪z, z⟫ : ℝ) = ⟪z', z'⟫)
    (hpos : 0 < det3 x y z) (hpos' : 0 < det3 x' y' z') :
    det3 x y z = det3 x' y' z' := by
  have hsq := det3_sq_congr hxx hxy hxz hyx hyy hyz hzx hzy hzz
  nlinarith [hsq, hpos, hpos', sq_nonneg (det3 x y z - det3 x' y' z'),
    sq_nonneg (det3 x y z + det3 x' y' z')]



/-- The Cramer representation of `v` against the frame `(p, q, p × q)`. -/
theorem frame_repr {p q : E3} (h : cross p q ≠ 0) (v : E3) :
    (⟪cross p q, cross p q⟫ : ℝ) • v
      = ((⟪p, v⟫ : ℝ) * ⟪q, q⟫ - ⟪p, q⟫ * ⟪q, v⟫) • p
        + ((⟪p, p⟫ : ℝ) * ⟪q, v⟫ - ⟪p, q⟫ * ⟪p, v⟫) • q
        + (⟪cross p q, v⟫ : ℝ) • cross p q := by
  set m := cross p q with hm
  -- `d = ⟪m,m⟫ = ‖p‖²‖q‖² − ⟪p,q⟫²` (Lagrange).
  have hpm : (⟪p, m⟫ : ℝ) = 0 := by rw [hm]; rw [real_inner_comm]; exact inner_cross_left p q
  have hqm : (⟪q, m⟫ : ℝ) = 0 := by rw [hm]; rw [real_inner_comm]; exact inner_cross_right p q
  have hmp : (⟪m, p⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hpm
  have hmq : (⟪m, q⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hqm
  have hlag : (⟪m, m⟫ : ℝ) = ⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2 := by
    have hL := norm_sq_cross p q
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq] at hL
    rw [hm]; exact hL
  have hcrossp : (⟪cross p q, p⟫ : ℝ) = 0 := inner_cross_left p q
  have hcrossq : (⟪cross p q, q⟫ : ℝ) = 0 := inner_cross_right p q
  have hqp : (⟪q, p⟫ : ℝ) = ⟪p, q⟫ := (real_inner_comm q p).symm
  apply eq_of_inner_frame_eq h
  · -- ⟪p, d•v⟫ = ⟪p, RHS⟫
    simp only [inner_add_right, real_inner_smul_right, hpm, mul_zero, add_zero]
    -- ⟪m,m⟫·⟪p,v⟫ = (⟪p,v⟫⟪q,q⟫−⟪p,q⟫⟪q,v⟫)⟪p,p⟫ + (⟪p,p⟫⟪q,v⟫−⟪p,q⟫⟪p,v⟫)⟪p,q⟫
    rw [hlag]; ring
  · -- ⟪q, d•v⟫ = ⟪q, RHS⟫
    simp only [inner_add_right, real_inner_smul_right, hqm, mul_zero, add_zero]
    rw [hlag, hqp]; ring
  · -- ⟪m, d•v⟫ = ⟪m, RHS⟫
    simp only [inner_add_right, real_inner_smul_right, hcrossp, hcrossq, mul_zero, zero_add,
      add_zero]
    ring

/-- **Frame pairing identity.**  Pairing `frame_repr` with a vector `u` expresses
`‖p×q‖² · ⟪u,v⟫` as a polynomial in the inner products of `u, v` against the frame `(p,q,p×q)` and
the frame's own Gram entries. -/
theorem frame_pairing {p q : E3} (h : cross p q ≠ 0) (u v : E3) :
    (⟪cross p q, cross p q⟫ : ℝ) * ⟪u, v⟫
      = ((⟪p, v⟫ : ℝ) * ⟪q, q⟫ - ⟪p, q⟫ * ⟪q, v⟫) * ⟪u, p⟫
        + ((⟪p, p⟫ : ℝ) * ⟪q, v⟫ - ⟪p, q⟫ * ⟪p, v⟫) * ⟪u, q⟫
        + (⟪cross p q, v⟫ : ℝ) * ⟪u, cross p q⟫ := by
  have hr := frame_repr h v
  have := congrArg (fun w => (⟪u, w⟫ : ℝ)) hr
  simp only [inner_smul_right, inner_add_right] at this
  -- this : ⟪m,m⟫ * ⟪u,v⟫ = coef_a * ⟪u,p⟫ + coef_b * ⟪u,q⟫ + ⟪m,v⟫ * ⟪u,m⟫
  linarith [this]

/-- **The Gram transfer lemma (induction engine).**  Two frames `(p,q,p×q)`, `(p',q',p'×q')`
(both nondegenerate) whose `p,q`-Gram blocks agree, paired with vectors `u,v` and `u',v'` whose
coordinates against the two frames agree, have equal pairings `⟪u,v⟫ = ⟪u',v'⟫`.

`hmm` (the `p×q` self-inner product agreement) follows from the `p,q`-block agreement via Lagrange,
but is taken as an explicit hypothesis to keep the interface symmetric; it is discharged at the call
site. -/
theorem gram_transfer {p q u v p' q' u' v' : E3}
    (h : cross p q ≠ 0) (h' : cross p' q' ≠ 0)
    (hpp : (⟪p, p⟫ : ℝ) = ⟪p', p'⟫) (hpq : (⟪p, q⟫ : ℝ) = ⟪p', q'⟫)
    (hqq : (⟪q, q⟫ : ℝ) = ⟪q', q'⟫)
    (hmm : (⟪cross p q, cross p q⟫ : ℝ) = ⟪cross p' q', cross p' q'⟫)
    (hup : (⟪u, p⟫ : ℝ) = ⟪u', p'⟫) (huq : (⟪u, q⟫ : ℝ) = ⟪u', q'⟫)
    (hum : (⟪u, cross p q⟫ : ℝ) = ⟪u', cross p' q'⟫)
    (hpv : (⟪p, v⟫ : ℝ) = ⟪p', v'⟫) (hqv : (⟪q, v⟫ : ℝ) = ⟪q', v'⟫)
    (hmv : (⟪cross p q, v⟫ : ℝ) = ⟪cross p' q', v'⟫) :
    (⟪u, v⟫ : ℝ) = ⟪u', v'⟫ := by
  have hA := frame_pairing h u v
  have hB := frame_pairing h' u' v'
  -- The two pairing RHSs are equal by the matching hypotheses.
  rw [← hpp, ← hpq, ← hqq, ← hup, ← huq, ← hum, ← hpv, ← hqv, ← hmv, ← hmm] at hB
  -- Now hA, hB say ⟪m,m⟫·⟪u,v⟫ = R and ⟪m,m⟫·⟪u',v'⟫ = R with the same R.
  have hmpos : (0 : ℝ) < ⟪cross p q, cross p q⟫ := by
    have hne : ‖cross p q‖ ≠ 0 := by simpa [norm_eq_zero] using h
    have hpos2 : (0 : ℝ) < ‖cross p q‖ ^ 2 := by positivity
    rwa [← real_inner_self_eq_norm_sq] at hpos2
  have heq : (⟪cross p q, cross p q⟫ : ℝ) * ⟪u, v⟫
      = ⟪cross p q, cross p q⟫ * ⟪u', v'⟫ := by rw [hA, hB]
  exact mul_left_cancel₀ (ne_of_gt hmpos) heq

/-- For two distinct, non-antipodal unit vectors the cross product is nonzero. -/
theorem cross_ne_zero_of_shortArc {p q : S2} (h : ShortArc p q) :
    cross (p : E3) (q : E3) ≠ 0 := by
  -- ‖p×q‖² = 1 − ⟪p,q⟫²; and |⟪p,q⟫| < 1 since p ≠ ±q.
  intro hc
  have hnorm : ‖cross (p : E3) (q : E3)‖ ^ 2 = 1 - (sInner p q) ^ 2 := by
    rw [norm_sq_cross, p.2, q.2]; simp [sInner]
  rw [hc, norm_zero] at hnorm
  -- 0 = 1 − ⟪p,q⟫² ⟹ ⟪p,q⟫² = 1 ⟹ ⟪p,q⟫ = ±1 ⟹ p = ±q, contradicting ShortArc.
  have hsq : sInner p q * sInner p q = 1 := by nlinarith [hnorm]
  have habs : sInner p q = 1 ∨ sInner p q = -1 := mul_self_eq_one_iff.mp hsq
  rcases habs with h1 | h1
  · -- ⟪p,q⟫ = 1 ⟹ p = q
    exact h.1 (sDist_eq_zero_iff.mp (by rw [sDist, h1, Real.arccos_one]))
  · -- ⟪p,q⟫ = −1 ⟹ p = −q
    apply h.2
    have : sDist p q < Real.pi → False := by
      intro hlt; rw [sDist, h1, Real.arccos_neg_one] at hlt; exact lt_irrefl _ hlt
    by_contra hne
    exact this (sDist_lt_pi_of_not_antipodal hne)



/-- `⟪A i, A j⟫` (in `E3`) is `sInner (A i) (A j)`, the spherical inner product. -/
theorem inner_eq_sInner {n : ℕ} (A : Fin (n + 1) → S2) (i j : Fin (n + 1)) :
    (⟪(A i : E3), (A j : E3)⟫ : ℝ) = sInner (A i) (A j) := rfl

/-- Equal spherical distance gives equal spherical inner product (`cos` of `arccos`). -/
theorem sInner_eq_of_sDist_eq {p q p' q' : S2} (h : sDist p q = sDist p' q') :
    sInner p q = sInner p' q' := by
  have := congrArg Real.cos h
  rwa [cos_sDist, cos_sDist] at this

/-- **Consecutive-side congruence.**  Equal side lengths ⟹ equal consecutive inner products. -/
theorem inner_consecutive_eq {n : ℕ} {A B : Fin (n + 1) → S2}
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e) (e : Fin n) :
    (⟪(A e.castSucc : E3), (A e.succ : E3)⟫ : ℝ) = ⟪(B e.castSucc : E3), (B e.succ : E3)⟫ := by
  have h := hs e
  rw [sideLen, sideLen] at h
  rw [inner_eq_sInner, inner_eq_sInner]
  exact sInner_eq_of_sDist_eq h

/-- **Consecutive-triple diagonal congruence (cosine rule).**  For a joint index `i : Fin (n-1)`,
the diagonal inner product `⟪A ⟨i⟩, A ⟨i+2⟩⟫` depends only on the two adjacent side lengths and the
joint angle, hence is equal between two arms with equal sides and equal joints. -/
theorem inner_diag_eq {n : ℕ} {A B : Fin (n + 1) → S2}
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) (i : Fin (n - 1)) :
    (⟪(A ⟨i.val, by have := i.isLt; omega⟩ : E3),
        (A ⟨i.val + 2, by have := i.isLt; omega⟩ : E3)⟫ : ℝ)
      = ⟪(B ⟨i.val, by have := i.isLt; omega⟩ : E3),
        (B ⟨i.val + 2, by have := i.isLt; omega⟩ : E3)⟫ := by
  -- abbreviations for the three vertices of each arm
  set a₀ : S2 := A ⟨i.val, by have := i.isLt; omega⟩
  set a₁ : S2 := A ⟨i.val + 1, by have := i.isLt; omega⟩
  set a₂ : S2 := A ⟨i.val + 2, by have := i.isLt; omega⟩
  set b₀ : S2 := B ⟨i.val, by have := i.isLt; omega⟩
  set b₁ : S2 := B ⟨i.val + 1, by have := i.isLt; omega⟩
  set b₂ : S2 := B ⟨i.val + 2, by have := i.isLt; omega⟩
  -- the diagonal inner product is cos of the diagonal distance; apply the cosine rule
  rw [inner_eq_sInner, inner_eq_sInner]
  rw [show sInner a₀ a₂ = Real.cos (sDist a₀ a₂) from (cos_sDist a₀ a₂).symm,
    show sInner b₀ b₂ = Real.cos (sDist b₀ b₂) from (cos_sDist b₀ b₂).symm]
  rw [spherical_cosine_rule a₀ a₁ a₂, spherical_cosine_rule b₀ b₁ b₂]
  -- match the three local quantities: sDist a₀ a₁ = side i, sDist a₁ a₂ = side (i+1), joint i.
  have hi1 : i.val < n := by have := i.isLt; omega
  have hi2 : i.val + 1 < n := by have := i.isLt; omega
  -- side lengths
  have hside0 : sDist a₀ a₁ = sDist b₀ b₁ := by
    have := hs ⟨i.val, hi1⟩
    simp only [sideLen, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at this
    simpa [a₀, a₁, b₀, b₁] using this
  have hside1 : sDist a₁ a₂ = sDist b₁ b₂ := by
    have := hs ⟨i.val + 1, hi2⟩
    simp only [sideLen, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at this
    simpa [a₁, a₂, b₁, b₂] using this
  -- joint angle
  have hjoint : sphAngle a₀ a₁ a₂ = sphAngle b₀ b₁ b₂ := by
    have := hj i
    simp only [jointAngle] at this
    simpa [a₀, a₁, a₂, b₀, b₁, b₂] using this
  rw [hside0, hside1, hjoint]



/-- Cyclic invariance of `det3`: `det3 a b c = det3 c a b`. -/
theorem det3_cyclic (a b c : E3) : det3 a b c = det3 c a b := by
  rw [det3, det3]; ring

/-- `⟪a×b, a×b⟫ = ⟪a,a⟫⟪b,b⟫ − ⟪a,b⟫⟪b,a⟫` (Binet–Cauchy), so the frame normal's self inner product
is a polynomial in the `(a,b)`-Gram block. -/
theorem inner_cross_self_eq (a b : E3) :
    (⟪cross a b, cross a b⟫ : ℝ) = ⟪a, a⟫ * ⟪b, b⟫ - ⟪a, b⟫ * ⟪b, a⟫ := by
  rw [inner_cross_cross]

/-- `⟪cross a b, c⟫ = det3 a b c` (the cross product on the left). -/
theorem inner_cross_left_eq_det3 (a b c : E3) :
    (⟪cross a b, c⟫ : ℝ) = det3 a b c := by
  rw [real_inner_comm, inner_cross_eq_det3, det3, det3]; ring

/-- `⟪a, cross b c⟫ = det3 b c a` (the cross product on the right, cyclically rotated). -/
theorem inner_cross_right_eq_det3 (a b c : E3) :
    (⟪a, cross b c⟫ : ℝ) = det3 b c a := by
  rw [inner_cross_eq_det3, det3, det3]; ring



/-- **Ordered Gram congruence** (the `i.val ≤ j.val` half).  By strong induction on `j.val`. -/
theorem gram_eq_ordered {n : ℕ} {A B : Fin (n + 1) → S2}
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (heA : ∀ i : Fin (n + 1), ShortArc (A i) (A (i + 1)))
    (heB : ∀ i : Fin (n + 1), ShortArc (B i) (B (i + 1)))
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) :
    ∀ N : ℕ, ∀ i j : Fin (n + 1), i.val ≤ j.val → j.val ≤ N →
      (⟪(A i : E3), (A j : E3)⟫ : ℝ) = ⟪(B i : E3), (B j : E3)⟫ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro i j hij hjN
    -- self inner products are 1.
    by_cases hself : i.val = j.val
    · have : i = j := Fin.ext hself
      subst this
      rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
    -- now i.val < j.val.
    have hlt : i.val < j.val := lt_of_le_of_ne hij hself
    -- consecutive side case: j = i + 1.
    by_cases hcons : j.val = i.val + 1
    · -- ⟪A i, A j⟫ is the side at e = ⟨i.val, _⟩.
      have hin : i.val < n := by omega
      have he := inner_consecutive_eq hs ⟨i.val, hin⟩
      -- identify castSucc/succ with i, j.
      have hcs : (⟨i.val, hin⟩ : Fin n).castSucc = i := by
        apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
      have hsc : (⟨i.val, hin⟩ : Fin n).succ = j := by
        apply Fin.ext; simp [Fin.succ]; omega
      rw [hcs, hsc] at he
      exact he
    -- general case: j.val ≥ i.val + 2 ≥ 2.
    have hj2 : i.val + 2 ≤ j.val := by omega
    -- the predecessor index of j and the frame base.
    have hjval2 : 2 ≤ j.val := by omega
    set r := j.val - 2 with hr
    have hrn : r + 2 = j.val := by omega
    have hr_lt : r < n := by have := j.isLt; omega
    have hr1_lt : r + 1 < n + 1 := by have := j.isLt; omega
    have hr_lt1 : r < n + 1 := by omega
    -- frame vertices
    set p : Fin (n + 1) := ⟨r, hr_lt1⟩ with hp
    set q : Fin (n + 1) := ⟨r + 1, hr1_lt⟩ with hq
    have hpval : p.val = r := rfl
    have hqval : q.val = r + 1 := rfl
    have hjval : j.val = r + 2 := by omega
    have hjeq : j = ⟨r + 2, by have := j.isLt; omega⟩ := by apply Fin.ext; simp [hjval]
    -- p + 1 = q (as Fin (n+1)), so heA at p gives ShortArc (A p) (A q).
    have hpq_succ : (p + 1 : Fin (n + 1)) = q := by
      have hplast : p ≠ Fin.last n := by
        intro hc; rw [hc, Fin.val_last] at hpval; omega
      apply Fin.ext
      rw [Fin.val_add_one, if_neg hplast, hpval, hqval]
    have hshortA : ShortArc (A p) (A q) := by have := heA p; rwa [hpq_succ] at this
    have hshortB : ShortArc (B p) (B q) := by have := heB p; rwa [hpq_succ] at this
    have hcrA : cross (A p : E3) (A q : E3) ≠ 0 := cross_ne_zero_of_shortArc hshortA
    have hcrB : cross (B p : E3) (B q : E3) ≠ 0 := cross_ne_zero_of_shortArc hshortB
    -- index ordering facts
    have hip : i.val ≤ r + 1 := by omega
    -- ===== frame Gram block matches =====
    have gpp : (⟪(A p : E3), (A p : E3)⟫ : ℝ) = ⟪(B p : E3), (B p : E3)⟫ := by
      rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
    have gqq : (⟪(A q : E3), (A q : E3)⟫ : ℝ) = ⟪(B q : E3), (B q : E3)⟫ := by
      rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
    have gpq : (⟪(A p : E3), (A q : E3)⟫ : ℝ) = ⟪(B p : E3), (B q : E3)⟫ := by
      have he := inner_consecutive_eq hs ⟨r, hr_lt⟩
      have hcs : (⟨r, hr_lt⟩ : Fin n).castSucc = p := by
        apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE, hp]
      have hsc : (⟨r, hr_lt⟩ : Fin n).succ = q := by
        apply Fin.ext; simp [Fin.succ, hq]
      rw [hcs, hsc] at he; exact he
    -- cross self inner products match via Lagrange (1·1 − ⟪p,q⟫²).
    have gmm : (⟪cross (A p : E3) (A q : E3), cross (A p : E3) (A q : E3)⟫ : ℝ)
        = ⟪cross (B p : E3) (B q : E3), cross (B p : E3) (B q : E3)⟫ := by
      rw [inner_cross_self_eq, inner_cross_self_eq]
      have hcA' : (⟪(A q : E3), (A p : E3)⟫ : ℝ) = ⟪(A p : E3), (A q : E3)⟫ :=
        real_inner_comm (A p : E3) (A q : E3)
      have hcB' : (⟪(B q : E3), (B p : E3)⟫ : ℝ) = ⟪(B p : E3), (B q : E3)⟫ :=
        real_inner_comm (B p : E3) (B q : E3)
      rw [hcA', hcB', gpp, gqq, gpq]
    -- ===== v = A j coordinates against the frame match =====
    -- ⟪p, v⟫ : the consecutive-triple diagonal at joint r.
    have hjoint_idx : r < n - 1 := by have := j.isLt; omega
    have vp : (⟪(A p : E3), (A j : E3)⟫ : ℝ) = ⟪(B p : E3), (B j : E3)⟫ := by
      have hd := inner_diag_eq hs hj ⟨r, hjoint_idx⟩
      -- identify the diag vertices with p and j.
      have e0 : (⟨(⟨r, hjoint_idx⟩ : Fin (n-1)).val,
          by have := (⟨r, hjoint_idx⟩ : Fin (n-1)).isLt; omega⟩ : Fin (n+1)) = p := by
        apply Fin.ext; simp [hp]
      have e2 : (⟨(⟨r, hjoint_idx⟩ : Fin (n-1)).val + 2,
          by have := (⟨r, hjoint_idx⟩ : Fin (n-1)).isLt; omega⟩ : Fin (n+1)) = j := by
        apply Fin.ext; simp [hjeq]
      rw [e0, e2] at hd; exact hd
    -- ⟪q, v⟫ : the side at e = ⟨r+1, _⟩.
    have vq : (⟪(A q : E3), (A j : E3)⟫ : ℝ) = ⟪(B q : E3), (B j : E3)⟫ := by
      have hin : r + 1 < n := by have := j.isLt; omega
      have he := inner_consecutive_eq hs ⟨r + 1, hin⟩
      have hcs : (⟨r + 1, hin⟩ : Fin n).castSucc = q := by
        apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE, hq]
      have hsc : (⟨r + 1, hin⟩ : Fin n).succ = j := by
        apply Fin.ext; simp [Fin.succ, hjeq]
      rw [hcs, hsc] at he; exact he
    -- ⟪cross p q, v⟫ = det3 (A p)(A q)(A j) = sOrient, positive for both, square matches.
    have vm : (⟪cross (A p : E3) (A q : E3), (A j : E3)⟫ : ℝ)
        = ⟪cross (B p : E3) (B q : E3), (B j : E3)⟫ := by
      rw [inner_cross_left_eq_det3, inner_cross_left_eq_det3]
      -- positivity from CyclicTriplePos at p < q < j.
      have hpltq : p < q := by rw [Fin.lt_def, hpval, hqval]; omega
      have hqltj : q < j := by rw [Fin.lt_def, hqval, hjval]; omega
      have hposA : 0 < det3 (A p : E3) (A q : E3) (A j : E3) := hcA p q j hpltq hqltj
      have hposB : 0 < det3 (B p : E3) (B q : E3) (B j : E3) := hcB p q j hpltq hqltj
      -- gram entries of triple (p,q,j): use gpp,gpq,vp (=⟪p,j⟫), gqq, vq (=⟪q,j⟫), self.
      have gjj : (⟪(A j : E3), (A j : E3)⟫ : ℝ) = ⟪(B j : E3), (B j : E3)⟫ := by
        rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
      exact det3_congr_of_pos gpp gpq vp
        (by rw [real_inner_comm (A p : E3) (A q : E3), real_inner_comm (B p : E3) (B q : E3)]; exact gpq)
        gqq vq
        (by rw [real_inner_comm (A p : E3) (A j : E3), real_inner_comm (B p : E3) (B j : E3)]; exact vp)
        (by rw [real_inner_comm (A q : E3) (A j : E3), real_inner_comm (B q : E3) (B j : E3)]; exact vq)
        gjj hposA hposB
    -- ===== u = A i coordinates against the frame match (from IH) =====
    -- max(i, p) ≤ r+1 < j.val ≤ N, so IH applies (strictly smaller bound).
    have up : (⟪(A i : E3), (A p : E3)⟫ : ℝ) = ⟪(B i : E3), (B p : E3)⟫ := by
      rcases le_total i.val p.val with hle | hle
      · exact IH (r + 1) (by omega) i p hle (by omega)
      · rw [real_inner_comm (A p : E3) (A i : E3), real_inner_comm (B p : E3) (B i : E3)]
        exact IH (r + 1) (by omega) p i hle (by omega)
    have uq : (⟪(A i : E3), (A q : E3)⟫ : ℝ) = ⟪(B i : E3), (B q : E3)⟫ := by
      rcases le_total i.val q.val with hle | hle
      · exact IH (r + 1) (by omega) i q hle (by omega)
      · rw [real_inner_comm (A q : E3) (A i : E3), real_inner_comm (B q : E3) (B i : E3)]
        exact IH (r + 1) (by omega) q i hle (by omega)
    -- ⟪u, cross p q⟫ = det3 (A i)(A p)(A q).  Sign: i<p<q → positive (CyclicTriplePos); else 0.
    have um : (⟪(A i : E3), cross (A p : E3) (A q : E3)⟫ : ℝ)
        = ⟪(B i : E3), cross (B p : E3) (B q : E3)⟫ := by
      rw [inner_cross_right_eq_det3, inner_cross_right_eq_det3]
      -- det3 (A p)(A q)(A i) = sOrient (A p)(A q)(A i) ; we have i ≤ r+1 = q.val.
      rcases lt_or_eq_of_le hip with hilt | hieq
      · -- i.val < r+1 ⟹ i.val ≤ r ; further split i.val < r vs = r.
        rcases lt_or_eq_of_le (show i.val ≤ r by omega) with hir | hir
        · -- i < p < q : positive triple (cyclic order p,q,i  ↔  i,p,q via det3_cyclic).
          have hipp : i < p := by rw [Fin.lt_def, hpval]; omega
          have hpltq : p < q := by rw [Fin.lt_def, hpval, hqval]; omega
          have hposA : 0 < det3 (A i : E3) (A p : E3) (A q : E3) := hcA i p q hipp hpltq
          have hposB : 0 < det3 (B i : E3) (B p : E3) (B q : E3) := hcB i p q hipp hpltq
          -- det3 (A p)(A q)(A i) = det3 (A i)(A p)(A q) by cyclic.
          rw [det3_cyclic (A p : E3) (A q : E3) (A i : E3),
            det3_cyclic (B p : E3) (B q : E3) (B i : E3)]
          -- gram of (i,p,q): ⟪i,i⟫,⟪i,p⟫(=up),⟪i,q⟫(=uq),⟪p,p⟫,⟪p,q⟫,⟪q,q⟫ all match.
          have gii : (⟪(A i : E3), (A i : E3)⟫ : ℝ) = ⟪(B i : E3), (B i : E3)⟫ := by
            rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
          exact det3_congr_of_pos gii up uq
            (by rw [real_inner_comm (A i : E3) (A p : E3), real_inner_comm (B i : E3) (B p : E3)]; exact up)
            gpp gpq
            (by rw [real_inner_comm (A i : E3) (A q : E3), real_inner_comm (B i : E3) (B q : E3)]; exact uq)
            (by rw [real_inner_comm (A p : E3) (A q : E3), real_inner_comm (B p : E3) (B q : E3)]; exact gpq)
            gqq hposA hposB
        · -- i.val = r = p.val ⟹ A i = A p, det3 (A p)(A q)(A p) = 0.
          have hieqp : i = p := Fin.ext (by rw [hpval]; exact hir)
          rw [hieqp]
          rw [show det3 (A p : E3) (A q : E3) (A p : E3) = 0 by rw [det3]; ring,
            show det3 (B p : E3) (B q : E3) (B p : E3) = 0 by rw [det3]; ring]
      · -- i.val = r+1 = q.val ⟹ A i = A q, det3 (A p)(A q)(A q) = 0.
        have hieqq : i = q := Fin.ext (by rw [hqval]; exact hieq)
        rw [hieqq]
        rw [show det3 (A p : E3) (A q : E3) (A q : E3) = 0 by rw [det3]; ring,
          show det3 (B p : E3) (B q : E3) (B q : E3) = 0 by rw [det3]; ring]
    -- ===== assemble via gram_transfer =====
    exact gram_transfer hcrA hcrB gpp gpq gqq gmm up uq um vp vq vm

/-- **Full Gram congruence.**  Symmetric closure of `gram_eq_ordered`: every pairwise vertex inner
product agrees between the two arms. -/
theorem gram_eq {n : ℕ} {A B : Fin (n + 1) → S2}
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (heA : ∀ i : Fin (n + 1), ShortArc (A i) (A (i + 1)))
    (heB : ∀ i : Fin (n + 1), ShortArc (B i) (B (i + 1)))
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) (i j : Fin (n + 1)) :
    (⟪(A i : E3), (A j : E3)⟫ : ℝ) = ⟪(B i : E3), (B j : E3)⟫ := by
  rcases le_total i.val j.val with hle | hle
  · exact gram_eq_ordered hcA hcB heA heB hs hj (max i.val j.val) i j hle (le_max_right _ _)
  · rw [real_inner_comm (A j : E3) (A i : E3), real_inner_comm (B j : E3) (B i : E3)]
    exact gram_eq_ordered hcA hcB heA heB hs hj (max i.val j.val) j i hle (le_max_left _ _)



/-- **R-cong: spherical SSS/angle endpoint congruence (Gram-congruence form).**  Two spherical arms
with equal side lengths and equal interior joint angles, both satisfying the convex cyclic-triple
orientation property, have equal endpoint distance. -/
theorem congruent_endpoint_eq {n : ℕ} {A B : Fin (n + 1) → S2}
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (heA : ∀ i : Fin (n + 1), ShortArc (A i) (A (i + 1)))
    (heB : ∀ i : Fin (n + 1), ShortArc (B i) (B (i + 1)))
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) :
    sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)) := by
  rw [sDist, sDist, sInner, sInner]
  rw [gram_eq hcA hcB heA heB hs hj 0 (Fin.last n)]

/-- **R-cong from `StrictConvexSphArm`, conditional on the cyclic-triple residue.**  The `ShortArc`
edge hypotheses are discharged from `StrictConvexSphArm` (its `edge_short` field); the convex
cyclic-triple orientation `CyclicTriplePos` of both arms remains as the named hypothesis (it is the
substrate's HINGE Lemma 2.3, not banked from `StrictConvexSphArm` alone). -/
theorem congruent_endpoint_eq_arm {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) :
    sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)) :=
  congruent_endpoint_eq hcA hcB hA.closed_convex.edge_short hB.closed_convex.edge_short hs hj

/-- **Endpoint congruence in `endpt` form**, ready to discharge the `(P2)` equal-joints branch of the
Schoenberg–Zaremba step (`SphericalSZFinal` §R-cong). -/
theorem endpt_eq_of_congruent {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) :
    ProofsInTheBook.SphericalArm.endpt A = ProofsInTheBook.SphericalArm.endpt B := by
  unfold ProofsInTheBook.SphericalArm.endpt
  exact congruent_endpoint_eq_arm hA hB hcA hcB hs hj



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



/-- **(R-cong, fully discharged) The no-deficit congruence step.**  A strictly convex `A`, strictly
convex `B`, equal sides, nondecreasing joints, and `deficitCount A B = 0` give `endpt A = endpt B`,
hence `endpt A ≤ endpt B`.  The cyclic-triple orientation hypotheses of `endpt_eq_of_congruent` are
discharged unconditionally from strict convexity (`cyclicTriplePos_unconditional`). -/
theorem congruence_step {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B) (hnd : deficitCount A B = 0) :
    endpt A ≤ endpt B := by
  have hjeq : ∀ k : Fin (n - 1), jointAngle A k = jointAngle B k :=
    all_joints_eq_of_no_deficit hangle hnd
  have heq : endpt A = endpt B :=
    endpt_eq_of_congruent hA hB
      (cyclicTriplePos_unconditional hA.closed_convex)
      (cyclicTriplePos_unconditional hB.closed_convex)
      hside hjeq
  exact le_of_eq heq

















/-- **The strict-or-vanishing dichotomy for a weakly convex arm.**  Either some non-incident support of
`A` vanishes, or `A` is strictly convex (every non-incident support is strictly positive, the missing
`strict_nonincident` field built from the weak `edge_support ≥ 0` being `≠ 0`). -/
theorem strict_or_vanishing {n : ℕ} {A : Fin (n + 1) → S2} (hA : WeakConvexSphArm A) :
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧ sOrient (A i) (A (i + 1)) (A j) = 0) ∨
      StrictConvexSphArm A := by
  by_cases hvanish :
      ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧ sOrient (A i) (A (i + 1)) (A j) = 0
  · exact Or.inl hvanish
  · -- no vanishing non-incident support ⟹ every non-incident support is strictly positive.
    refine Or.inr ?_
    push Not at hvanish
    refine { two_le := hA.two_le, closed_convex := ?_ }
    refine { three_le := hA.closed_convex.three_le
             edge_short := hA.closed_convex.edge_short
             edge_support := hA.closed_convex.edge_support
             strict_nonincident := ?_
             open_hemisphere := hA.closed_convex.open_hemisphere }
    intro i j hji hji1
    exact lt_of_le_of_ne (hA.closed_convex.edge_support i j)
      (fun heq => hvanish i j hji hji1 heq.symm)

















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



/-- The opening axis `K = openingAxis k = ⟨k+1⟩` is interior: `1 ≤ K.val` and `K.val < n`. -/
theorem openingAxis_interior {n : ℕ} (k : Fin (n - 1)) :
    1 ≤ (openingAxis k).val ∧ (openingAxis k).val < n := by
  have := k.isLt
  simp only [openingAxis]
  omega

/-- **The joint-`k` angle of the interior-opened arm equals the opened interior joint angle.**  Opening
about `K = openingAxis k = ⟨k+1⟩` fixes vertices `≤ k+1` (so `A ⟨k⟩` and the axis `A ⟨k+1⟩`) and rotates
`A ⟨k+2⟩`, so the joint-`k` triple `(A ⟨k⟩, A ⟨k+1⟩, rotS2 (A K) δ (A ⟨k+2⟩))` is exactly
`(jointPrev A k, A K, rotS2 (A K) δ (jointNext A k))`, whose spherical angle is
`openedInteriorJointAngle A k δ`. -/
theorem jointAngle_openTail_eq_openedInterior {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ) :
    jointAngle (openTail A (openingAxis k) δ) k = openedInteriorJointAngle A k δ := by
  have hk := k.isLt
  have hKval : (openingAxis k).val = k.val + 1 := rfl
  have hv0 : openTail A (openingAxis k) δ ⟨k.val, by omega⟩ = A ⟨k.val, by omega⟩ :=
    openTail_fixed A (openingAxis k) δ (by simp only [openingAxis, Fin.val_mk]; omega)
  -- the axis vertex `⟨k+1⟩ = openingAxis k` is fixed by the opening.
  have hKeq : (openingAxis k : Fin (n + 1)) = (⟨k.val + 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext; rw [hKval]
  have hv1 : openTail A (openingAxis k) δ ⟨k.val + 1, by omega⟩ = A (openingAxis k) := by
    rw [← hKeq]; exact openTail_axis A (openingAxis k) δ
  have hv2 : openTail A (openingAxis k) δ ⟨k.val + 2, by omega⟩
      = rotS2 (A (openingAxis k)) δ (A ⟨k.val + 2, by omega⟩) :=
    openTail_rot A (openingAxis k) δ (by simp only [openingAxis, Fin.val_mk]; omega)
  simp only [jointAngle, openedInteriorJointAngle, jointPrev, jointNext, hv0, hv1, hv2]



/-- The short-arc base hypotheses for the joint `k` from strict convexity.  `K = openingAxis k = ⟨k+1⟩`;
`hka : ShortArc (A K) (jointPrev A k)` is the reversed edge `⟨k⟩→⟨k+1⟩`, `hkt : ShortArc (A K) (jointNext A k)`
is the edge `⟨k+1⟩→⟨k+2⟩`. -/
theorem shortArcs_of_strict {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) (k : Fin (n - 1)) :
    ShortArc (A (openingAxis k)) (jointPrev A k) ∧ ShortArc (A (openingAxis k)) (jointNext A k) := by
  have hk := k.isLt
  have hes := hA.closed_convex.edge_short
  have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    simp only [Fin.val_one']; rw [Nat.mod_eq_of_lt (by omega)]
  -- `(⟨m⟩ : Fin (n+1)) + 1 = ⟨m+1⟩` when `m + 1 < n + 1`.
  have add_one : ∀ m : ℕ, (hm : m + 1 < n + 1) →
      ((⟨m, by omega⟩ : Fin (n + 1)) + 1) = (⟨m + 1, hm⟩ : Fin (n + 1)) := by
    intro m hm
    apply Fin.ext
    rw [Fin.val_add, h1v, Fin.val_mk, Nat.mod_eq_of_lt hm]
  -- `hka`: edge ⟨k⟩→⟨k+1⟩ reversed.
  have hka0 : ShortArc (A ⟨k.val, by omega⟩) (A ((⟨k.val, by omega⟩ : Fin (n + 1)) + 1)) :=
    hes ⟨k.val, by omega⟩
  rw [add_one k.val (by omega)] at hka0
  -- `hkt`: edge ⟨k+1⟩→⟨k+2⟩.
  have e_axis : (openingAxis k : Fin (n + 1)) = ⟨k.val + 1, by omega⟩ := by
    apply Fin.ext; rfl
  have hkt0 : ShortArc (A (openingAxis k)) (A ((openingAxis k : Fin (n + 1)) + 1)) :=
    hes (openingAxis k)
  rw [e_axis, add_one (k.val + 1) (by omega)] at hkt0
  refine ⟨?_, ?_⟩
  · -- ShortArc (A K) (jointPrev A k) = ShortArc (A ⟨k+1⟩) (A ⟨k⟩) = (hka0).symm
    have hp : jointPrev A k = A ⟨k.val, by omega⟩ := rfl
    have ha : (A (openingAxis k)) = A ⟨k.val + 1, by omega⟩ := by rw [e_axis]
    rw [hp, ha]
    exact hka0.symm
  · have hn : jointNext A k = A ⟨k.val + 2, by omega⟩ := rfl
    rw [hn]
    exact hkt0

















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



/-- **Brick 1.**  At the rotation axis `a`, the tangent toward the rotated point `rotS2 a δ p` is the
rotation of the tangent toward `p`.  This is `tangentTo_rotS2` at base point `= a`, using that the
axis is fixed (`rotS2 a δ a = a`). -/
theorem tangentTo_axis_rotS2 (a p : S2) (δ : ℝ) :
    tangentTo a (rotS2 a δ p) = rot (a : E3) δ (tangentTo a p) := by
  -- The axis is fixed by `rotS2`: `rotS2 a δ a = a`.
  have hfix : rotS2 a δ a = a := by
    apply S2.ext
    rw [rotS2_coe, rot_axis a.2]
  -- rewrite the LEFT base `a` as `rotS2 a δ a`, then apply the general tangent action.
  calc tangentTo a (rotS2 a δ p)
      = tangentTo (rotS2 a δ a) (rotS2 a δ p) := by rw [hfix]
    _ = rot (a : E3) δ (tangentTo a p) := tangentTo_rotS2 a δ a p
















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



theorem det3_cyclic (a b c : E3) : det3 a b c = det3 b c a := by
  simp only [det3]; ring

theorem det3_swap12 (a b c : E3) : det3 a b c = -det3 b a c := by
  simp only [det3]; ring









/-- `ncos b ρ = -1` forces antiparallelism: `ρ = -(t • b)` with `t = ‖ρ‖/‖b‖ > 0`. -/
theorem antiparallel_of_ncos_neg_one {b ρ : E3} (hb : b ≠ 0) (hρ : ρ ≠ 0)
    (hc : ncos b ρ = -1) : ∃ t : ℝ, 0 < t ∧ ρ = -(t • b) := by
  have hbn : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hρn : (0:ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hd : (0:ℝ) < ‖b‖ * ‖ρ‖ := by positivity
  have hinner : (⟪b, ρ⟫ : ℝ) = -(‖b‖ * ‖ρ‖) := by
    rw [ncos, div_eq_iff (ne_of_gt hd)] at hc
    linarith [hc]
  have hneg : (⟪b, -ρ⟫ : ℝ) = ‖b‖ * ‖-ρ‖ := by
    rw [inner_neg_right, hinner, norm_neg]; ring
  have hpar := inner_eq_norm_mul_iff_real.mp hneg
  -- hpar : ‖-ρ‖ • b = ‖b‖ • -ρ
  rw [norm_neg] at hpar
  have h2 : ‖ρ‖ • b = -(‖b‖ • ρ) := by rw [hpar, smul_neg]
  have hb0' : (‖b‖ : ℝ) ≠ 0 := ne_of_gt hbn
  refine ⟨‖ρ‖ / ‖b‖, by positivity, ?_⟩
  have h3 := congrArg (fun v : E3 => (‖b‖)⁻¹ • v) h2
  simp only [smul_smul, smul_neg] at h3
  rw [inv_mul_cancel₀ hb0', one_smul] at h3
  -- h3 : (‖b‖⁻¹ * ‖ρ‖) • b = -ρ
  rw [div_eq_inv_mul, h3, neg_neg]



/-- **Collinearity from a vanishing oriented area.**  For `b, u ⊥ h`, `h ≠ 0`, `b ≠ 0`:
`det3 h b u = 0` forces `u = c • b` for some `c : ℝ`. -/
theorem collinear_of_det3_zero {h b u : E3} (hb0 : (⟪h,b⟫:ℝ) = 0) (hu0 : (⟪h,u⟫:ℝ) = 0)
    (hh : h ≠ 0) (hb : b ≠ 0) (hzero : det3 h b u = 0) : ∃ c : ℝ, u = c • b := by
  rcases eq_or_ne u 0 with hu | hu
  · exact ⟨0, by rw [hu, zero_smul]⟩
  have hbn : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hun : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hsq := det3h_sq (h := h) (u := b) (v := u) hb0 hu0
  rw [hzero] at hsq
  -- 0 = ‖h‖²(‖b‖²‖u‖² − ⟪b,u⟫²)
  have hsq' : ‖h‖^2 * (‖b‖^2 * ‖u‖^2 - (⟪b,u⟫:ℝ)^2) = 0 := by
    have h0 := hsq.symm
    simpa using h0
  have hD : ‖b‖^2 * ‖u‖^2 - (⟪b,u⟫:ℝ)^2 = 0 := by
    rcases mul_eq_zero.mp hsq' with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  have h2 : ((⟪b,u⟫:ℝ) - ‖b‖ * ‖u‖) * ((⟪b,u⟫:ℝ) + ‖b‖ * ‖u‖) = 0 := by
    linear_combination -hD
  rcases mul_eq_zero.mp h2 with h3 | h3
  · -- parallel: ⟪b,u⟫ = ‖b‖‖u‖
    have hpos : (⟪b, u⟫ : ℝ) = ‖b‖ * ‖u‖ := by linarith
    have hpar := inner_eq_norm_mul_iff_real.mp hpos
    -- hpar : ‖u‖ • b = ‖b‖ • u
    have h4 := congrArg (fun v : E3 => (‖b‖)⁻¹ • v) hpar
    simp only [smul_smul] at h4
    rw [inv_mul_cancel₀ (ne_of_gt hbn), one_smul] at h4
    exact ⟨‖b‖⁻¹ * ‖u‖, h4.symm⟩
  · -- antiparallel: ncos = -1 route
    have hneg : (⟪b, u⟫ : ℝ) = -(‖b‖ * ‖u‖) := by linarith
    have hd : (‖b‖ * ‖u‖ : ℝ) ≠ 0 := by positivity
    have hc : ncos b u = -1 := by
      rw [ncos, hneg, neg_div, div_self hd]
    obtain ⟨t, _, hu'⟩ := antiparallel_of_ncos_neg_one hb hu hc
    exact ⟨-t, by rw [hu', neg_smul]⟩







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



/-- `det3` additive in the *middle* argument. -/
theorem det3_add_mid (a b c d : E3) : det3 a (b + c) d = det3 a b d + det3 a c d := by
  simp only [det3, PiLp.add_apply]; ring

/-- `det3` homogeneous in the *middle* argument. -/
theorem det3_smul_mid (a b d : E3) (t : ℝ) : det3 a (t • b) d = t * det3 a b d := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring



/-- **(Brick 1) Extract the span coefficients.**  From the NNReal span membership
`(p:E3) ∈ span≥0 {v, w}`, produce `a b : ℝ≥0` with `(a:ℝ)•v + (b:ℝ)•w = p` (the real-scalar
combination).  This is exactly FFCT19's `Submodule.mem_span_pair` + `NNReal.smul_def` pattern. -/
theorem span_pair_coeffs_S2 {p v w : S2}
    (hcol : (p : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)) :
    ∃ a b : ℝ≥0, (a : ℝ) • (v : E3) + (b : ℝ) • (w : E3) = (p : E3) := by
  rw [Submodule.mem_span_pair] at hcol
  obtain ⟨a, b, hab⟩ := hcol
  refine ⟨a, b, ?_⟩
  have := hab
  rwa [NNReal.smul_def, NNReal.smul_def] at this



/-- **(Brick 2) Unit = nonnegative multiple of unit ⟹ scalar `1` and equality.**  If `p = a • v`
with `p`, `v` on the sphere and `a ≥ 0`, then `a = 1` and `p = v`.  (Take norms: `1 = a · 1`, so
`a = 1`, hence `p = 1 • v = v`.) -/
theorem nnreal_smul_unit_eq_unit {p v : S2} {a : ℝ} (ha : 0 ≤ a)
    (hpv : (p : E3) = a • (v : E3)) :
    a = 1 ∧ p = v := by
  -- norms of both sides: `‖p‖ = 1`, `‖v‖ = 1`, `‖a • v‖ = |a| · ‖v‖ = a`.
  have hnp : ‖(p : E3)‖ = 1 := p.2
  have hnv : ‖(v : E3)‖ = 1 := v.2
  have hnorm : (1 : ℝ) = a := by
    have := congrArg (fun x : E3 => ‖x‖) hpv
    simp only [norm_smul, Real.norm_eq_abs] at this
    rw [hnp, hnv, mul_one, abs_of_nonneg ha] at this
    linarith [this]
  refine ⟨hnorm.symm, ?_⟩
  -- `p = a • v = 1 • v = v` as `E3`, hence as `S2` by injectivity of the coercion.
  apply S2.ext
  rw [hpv, ← hnorm, one_smul]



/-- **(Brick 3) `b = 0` is impossible under a short predecessor edge.**  If `p = a•v + b•w` with the
nonnegative coefficients and `b = 0`, then `p = a•v` with `a ≥ 0`, so `p = v` (Brick 2),
contradicting `ShortArc p v` (whose first conjunct is `p ≠ v`).  Hence `0 < b`. -/
theorem coeff_b_pos_of_edge_short {p v w : S2} {a b : ℝ≥0}
    (hpvw : (a : ℝ) • (v : E3) + (b : ℝ) • (w : E3) = (p : E3))
    (hpv : ShortArc p v) :
    0 < (b : ℝ) := by
  rcases lt_or_eq_of_le b.2 with hpos | hzero
  · exact hpos
  · -- `b = 0`: then `p = a•v`, forcing `p = v`, contradicting `ShortArc p v`.
    exfalso
    have hb0 : (b : ℝ) = 0 := hzero.symm
    have hpav : (p : E3) = (a : ℝ) • (v : E3) := by
      rw [← hpvw, hb0, zero_smul, add_zero]
    have := nnreal_smul_unit_eq_unit (a := (a : ℝ)) a.2 hpav
    exact hpv.1 this.2



/-- The apex-transported area form: for the unit apex `v`, `det3 (v:E3) (tangentTo v u) (tangentTo v w)
= det3 u v w`.  (The tangents differ from `u, w` by multiples of `v`, which drop out of the
determinant; the cyclic/repeat identities collapse the rest.) -/
theorem det3_apex_tangent_eq {u v w : S2} :
    det3 (v : E3) (tangentTo v u) (tangentTo v w) = -det3 (u : E3) (v : E3) (w : E3) := by
  -- expand the two tangents; everything is then a polynomial identity in the coordinates and the
  -- two scalars `sInner u v`, `sInner w v`, closed by `ring` (the apex form differs from
  -- `det3 u v w` by one row swap, hence the sign).
  rw [tangentTo_eq, tangentTo_eq]
  simp only [det3, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **(Forward bridge) A vanishing apex area form forces the spherical angle into `{0, π}`.**
If `det3 u v w = 0` and both arcs `(v, u)`, `(v, w)` are short (so both tangents are nonzero),
then `sphAngle u v w = 0` or `sphAngle u v w = π`. -/
theorem sphAngle_eq_zero_or_pi_of_det3_zero {u v w : S2}
    (hvu : ShortArc v u) (hvw : ShortArc v w)
    (hdet : det3 (u : E3) (v : E3) (w : E3) = 0) :
    sphAngle u v w = 0 ∨ sphAngle u v w = Real.pi := by
  -- both tangents at the apex are nonzero.
  have htu : tangentTo v u ≠ 0 := (tangentTo_ne_zero_iff v u).2 hvu
  have htw : tangentTo v w ≠ 0 := (tangentTo_ne_zero_iff v w).2 hvw
  -- the apex `v` is nonzero and orthogonal to both tangents.
  have hv0 : (v : E3) ≠ 0 := by
    intro h; have := v.2; rw [h, norm_zero] at this; norm_num at this
  have horthu : (⟪(v : E3), tangentTo v u⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact tangentTo_orthogonal v u
  have horthw : (⟪(v : E3), tangentTo v w⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact tangentTo_orthogonal v w
  -- transport: the apex area form vanishes (it is `-det3 u v w`).
  have hzero : det3 (v : E3) (tangentTo v u) (tangentTo v w) = 0 := by
    rw [det3_apex_tangent_eq, hdet, neg_zero]
  -- collinearity: `tangentTo v w = c • tangentTo v u`.
  obtain ⟨c, hc⟩ := collinear_of_det3_zero horthu horthw hv0 htu hzero
  -- `c ≠ 0` (else `tangentTo v w = 0`).
  have hc0 : c ≠ 0 := by
    intro h; rw [h, zero_smul] at hc; exact htw hc
  -- dichotomy by the sign of `c`.
  rcases lt_trichotomy c 0 with hneg | hcz | hpos
  · right
    rw [sphAngle, InnerProductGeometry.angle_eq_pi_iff]
    exact ⟨htu, c, hneg, hc⟩
  · exact absurd hcz hc0
  · left
    rw [sphAngle, InnerProductGeometry.angle_eq_zero_iff]
    exact ⟨htu, c, hpos, hc⟩



/-- **(Brick 4) The corrected predecessor kill.**  For an interior fold index `i ≥ 1` with the
nondegenerate span representation `(a:ℝ)•A(i+1) + (b:ℝ)•A j = A i`, `a, b > 0`, and the two weak
supports of the predecessor edge `(A(i-1), A i)` at the two fold neighbours
(`0 ≤ sOrient (A(i-1)) (A i) (A(i+1))`, `0 ≤ sOrient (A(i-1)) (A i) (A j)`), the fold is impossible,
under `PositiveJoints A` and `jointAngle A · < π` (the non-flat restriction `JointLe A B` + strict
`B` supplies).

The audited algebra (`u = A(i-1)`, `p = A i`, `v = A(i+1)`, `w = A j`):
`det3 u p v = -b·det3 u v w`, `det3 u p w = a·det3 u v w`; the two supports with `a, b > 0` force
`det3 u v w = 0`, hence `det3 u p v = 0`, i.e. the adjacent joint triple at apex `A i` vanishes, so
the interior joint at index `i-1` is in `{0, π}` — excluded by positivity and the non-flat bound. -/
theorem far_fold_no_predecessor {n : ℕ} {A : Fin (n + 1) → S2} {i j : ℕ}
    (hi1 : 1 ≤ i) (hij : i + 2 < j) (hj : j < n + 1)
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hpre : i - 1 < n + 1) (hii : i < n + 1) (hi2 : i + 1 < n + 1)
    (hcoeff : a • (A ⟨i + 1, hi2⟩ : E3) + b • (A ⟨j, hj⟩ : E3) = (A ⟨i, hii⟩ : E3))
    (hsuppv : 0 ≤ sOrient (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩))
    (hsuppw : 0 ≤ sOrient (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨j, hj⟩))
    (hposJoint : 0 < jointAngle A ⟨i - 1, by omega⟩)
    (hltJoint : jointAngle A ⟨i - 1, by omega⟩ < Real.pi)
    (hsau : ShortArc (A ⟨i, hii⟩) (A ⟨i - 1, hpre⟩))
    (hsav : ShortArc (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩)) :
    False := by
  -- name the four sphere points.
  set u : E3 := (A ⟨i - 1, hpre⟩ : E3) with hu
  set p : E3 := (A ⟨i, hii⟩ : E3) with hp
  set v : E3 := (A ⟨i + 1, hi2⟩ : E3) with hv
  set w : E3 := (A ⟨j, hj⟩ : E3) with hw
  -- the supports are `det3` (unfold `sOrient`).
  have hsuppv' : 0 ≤ det3 u p v := hsuppv
  have hsuppw' : 0 ≤ det3 u p w := hsuppw
  -- the two audited identities.
  have hpvw : a • v + b • w = p := hcoeff
  -- `det3 u p v = a·det3 u v v + b·det3 u w v = b·det3 u w v = -b·det3 u v w`.
  have hidv : det3 u p v = -b * det3 u v w := by
    rw [← hpvw, det3_add_mid, det3_smul_mid, det3_smul_mid]
    -- `det3 u v v = 0`, `det3 u w v = -det3 u v w`.
    have hvv : det3 u v v = 0 := by simp only [det3]; ring
    have hwv : det3 u w v = -det3 u v w := by simp only [det3]; ring
    rw [hvv, hwv]; ring
  -- `det3 u p w = a·det3 u v w + b·det3 u w w = a·det3 u v w`.
  have hidw : det3 u p w = a * det3 u v w := by
    rw [← hpvw, det3_add_mid, det3_smul_mid, det3_smul_mid]
    have hww : det3 u w w = 0 := by simp only [det3]; ring
    rw [hww]; ring
  -- from the supports + positivity: `det3 u v w = 0`.
  have hdet0 : det3 u v w = 0 := by
    have h1 : 0 ≤ -b * det3 u v w := hidv ▸ hsuppv'
    have h2 : 0 ≤ a * det3 u v w := hidw ▸ hsuppw'
    -- `a·D ≥ 0` with `a > 0` ⟹ `D ≥ 0`; `-b·D ≥ 0` with `b > 0` ⟹ `D ≤ 0`.
    nlinarith [h1, h2, ha, hb, mul_pos ha hb]
  -- hence the adjacent triple `det3 u p v = 0`.
  have hadj0 : det3 u p v = 0 := by rw [hidv, hdet0]; ring
  -- the adjacent triple is exactly `det3 (A(i-1)) (A i) (A(i+1))`, apex `A i` = joint `i-1`.
  -- bridge: `det3 u p v = 0` ⟹ `sphAngle (A(i-1)) (A i) (A(i+1)) ∈ {0, π}`.
  -- short arcs at the apex `A i`: `(A i, A(i-1))` and `(A i, A(i+1))`.
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero (u := A ⟨i - 1, hpre⟩) (v := A ⟨i, hii⟩)
    (w := A ⟨i + 1, hi2⟩) hsau hsav (by rw [← hu, ← hp, ← hv]; exact hadj0)
  -- the joint angle at index `i-1` is this spherical angle.
  have hjoint_eq : jointAngle A ⟨i - 1, by omega⟩
      = sphAngle (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    rw [jointAngle]
    have e0 : (⟨(i - 1) , by omega⟩ : Fin (n + 1)) = (⟨i - 1, hpre⟩ : Fin (n + 1)) := rfl
    have e1 : (⟨(i - 1) + 1, by omega⟩ : Fin (n + 1)) = (⟨i, hii⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (i - 1) + 1 = i; omega
    have e2 : (⟨(i - 1) + 2, by omega⟩ : Fin (n + 1)) = (⟨i + 1, hi2⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (i - 1) + 2 = i + 1; omega
    rw [e0, e1, e2]
  -- contradiction: the joint is in `(0, π)` but the bridge forces it into `{0, π}`.
  rcases hbridge with h0 | hπ
  · rw [hjoint_eq, h0] at hposJoint; exact lt_irrefl 0 hposJoint
  · rw [hjoint_eq, hπ] at hltJoint; exact lt_irrefl Real.pi hltJoint



/-- **(Brick 5) Far-fold boundary classification — the `i = 0` half.**  Given a weakly convex
`PositiveJoints` arm `A`, a strictly convex `B` with `JointLe A B`, fold indices `i + 2 < j < n+1`,
and the *nondegenerate* fold datum
`∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ (a:ℝ)•A(i+1) + (b:ℝ)•A j = A i`, the fold can only occur at `i = 0`.

Proof: if `i ≥ 1`, the predecessor edge `(A(i-1), A i)` exists, its two weak supports at the fold
neighbours hold (`edge_support`), and its incoming/outgoing arcs are short (`edge_short`), so
Brick 4 (`far_fold_no_predecessor`) derives `False`.  The non-flat bound the kill needs is
`jointAngle A · < π` from `jointAngle_lt_pi hB hangle`. -/
theorem far_fold_boundary_classification_of_nondeg {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hnd : ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) = (A ⟨i, by omega⟩ : E3)) :
    i = 0 := by
  by_contra hi0
  have hi1 : 1 ≤ i := by omega
  obtain ⟨a, b, ha, hb, hcoeff⟩ := hnd
  -- index bounds.
  have hii : i < n + 1 := by omega
  have hi2 : i + 1 < n + 1 := by omega
  have hpre : i - 1 < n + 1 := by omega
  -- the predecessor edge as a `Fin`-edge of the closed polygon: `(A ⟨i-1⟩, A ⟨i-1⟩ + 1)`.
  have hsucc : ((⟨i - 1, hpre⟩ : Fin (n + 1)) + 1) = (⟨i, hii⟩ : Fin (n + 1)) := by
    have hn2 : 2 ≤ n := hA.two_le
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    show ((⟨i - 1, hpre⟩ : Fin (n + 1)) + 1).val = i
    rw [Fin.val_add, Fin.val_mk, hone,
      Nat.mod_eq_of_lt (show (i - 1) + 1 < n + 1 by omega)]
    omega
  -- weak supports of the predecessor edge at the two fold neighbours.
  have hsuppv : 0 ≤ sOrient (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    have h := hA.closed_convex.edge_support ⟨i - 1, hpre⟩ ⟨i + 1, hi2⟩
    rwa [hsucc] at h
  have hsuppw : 0 ≤ sOrient (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨j, hj⟩) := by
    have h := hA.closed_convex.edge_support ⟨i - 1, hpre⟩ ⟨j, hj⟩
    rwa [hsucc] at h
  -- short predecessor edge arcs.
  have hedge : ShortArc (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) := by
    have h := hA.closed_convex.edge_short ⟨i - 1, hpre⟩
    rwa [hsucc] at h
  have hsau : ShortArc (A ⟨i, hii⟩) (A ⟨i - 1, hpre⟩) := hedge.symm
  have hedgeFwd : ShortArc (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    have hn2 : 2 ≤ n := hA.two_le
    have h := hA.closed_convex.edge_short ⟨i, hii⟩
    have hsucc2 : ((⟨i, hii⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc2] at h
  -- the non-flat bound and positivity at joint index `i-1`.
  have hposJoint : 0 < jointAngle A ⟨i - 1, by omega⟩ := hposA ⟨i - 1, by omega⟩
  have hltJoint : jointAngle A ⟨i - 1, by omega⟩ < Real.pi :=
    jointAngle_lt_pi hB hangle ⟨i - 1, by omega⟩
  -- apply Brick 4.
  exact far_fold_no_predecessor hi1 hij hj ha hb hpre hii hi2 hcoeff hsuppv hsuppw
    hposJoint hltJoint hsau hedgeFwd





















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









/-- **(Brick 2) The determinant-vanishing tail step.**  With `v = A 1`, `w = A j`, `z₀ = A 0`,
`zt = A t`, `z' = A (t+1)`:
* `z₀ = a•v + b•w` (the `i = 0` fold), `b > 0`;
* `zt = c•v + d•w` (cone membership of `A t`), `d > 0`;
* `0 ≤ det3 z₀ v z'` (support of edge `(A 0, A 1)` at `A (t+1)`);
* `0 ≤ det3 zt z' v` (support of edge `(A t, A (t+1))` at `A 1`);

then `det3 v w z' = 0`.

The two supports are `-b · det3 v w z'` and `d · det3 v w z'`; with `b, d > 0` they force the area
form to vanish.  (Symbolically verified: `S₁ = -b·D`, `S₂ = d·D`.) -/
theorem far_fold_tail_collinear_step
    {v w z₀ zt z' : E3} {a b c d : ℝ}
    (hb : 0 < b) (hd : 0 < d)
    (hz0 : z₀ = a • v + b • w)
    (hzt : zt = c • v + d • w)
    (hsupp1 : 0 ≤ det3 z₀ v z')
    (hsupp2 : 0 ≤ det3 zt z' v) :
    det3 v w z' = 0 := by
  -- `det3 z₀ v z' = -b · det3 v w z'`.
  have h1 : det3 z₀ v z' = -b * det3 v w z' := by
    subst hz0; simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `det3 zt z' v = d · det3 v w z'`.
  have h2 : det3 zt z' v = d * det3 v w z' := by
    subst hzt; simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `-b·D ≥ 0` with `b > 0` ⟹ `D ≤ 0`; `d·D ≥ 0` with `d > 0` ⟹ `D ≥ 0`.
  have hle : det3 v w z' ≤ 0 := by nlinarith [h1 ▸ hsupp1, hb]
  have hge : 0 ≤ det3 v w z' := by nlinarith [h2 ▸ hsupp2, hd]
  linarith





/-- **(Brick 3) Coplanar triple ⟹ vanishing `det3`.**  If all three of `x, y, z` lie in the common
2-plane `span {v, w}` (as real combinations), then `det3 x y z = 0`. -/
theorem coplanar_triple_det3_zero {v w x y z : E3}
    (hx : ∃ p q : ℝ, p • v + q • w = x)
    (hy : ∃ p q : ℝ, p • v + q • w = y)
    (hz : ∃ p q : ℝ, p • v + q • w = z) :
    det3 x y z = 0 := by
  obtain ⟨p1, q1, hx⟩ := hx
  obtain ⟨p2, q2, hy⟩ := hy
  obtain ⟨p3, q3, hz⟩ := hz
  subst hx; subst hy; subst hz
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring





/-- **(Brick 4) Interior collinearity is impossible.**  A vanishing consecutive triple
`det3 (A (t-1)) (A t) (A (t+1)) = 0` at an interior position (`1 ≤ t`, `t + 1 < n + 1`), with the two
short joint arcs at apex `A t`, contradicts `PositiveJoints A` and `jointAngle A · < π`.

This is the tail analogue of FFCT21's predecessor kill: the propagated cone membership collapses the
apex `A t` joint onto a flat angle, excluded on the satisfiable class. -/
theorem far_fold_tail_not_interior {n : ℕ} {A B : Fin (n + 1) → S2}
    (hposA : PositiveJoints A) (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {t : ℕ} (ht1 : 1 ≤ t) (htn : t + 1 < n + 1)
    (hpre : t - 1 < n + 1) (htt : t < n + 1) (ht2 : t + 1 < n + 1)
    (hsau : ShortArc (A ⟨t, htt⟩) (A ⟨t - 1, hpre⟩))
    (hsav : ShortArc (A ⟨t, htt⟩) (A ⟨t + 1, ht2⟩))
    (hcol : det3 (A ⟨t - 1, hpre⟩ : E3) (A ⟨t, htt⟩ : E3) (A ⟨t + 1, ht2⟩ : E3) = 0) :
    False := by
  -- the apex `A t` sees a flat angle towards `A (t-1)`, `A (t+1)`.
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero (u := A ⟨t - 1, hpre⟩) (v := A ⟨t, htt⟩)
    (w := A ⟨t + 1, ht2⟩) hsau hsav hcol
  -- the joint angle at interior index `t-1`.
  have hposJoint : 0 < jointAngle A ⟨t - 1, by omega⟩ := hposA ⟨t - 1, by omega⟩
  have hltJoint : jointAngle A ⟨t - 1, by omega⟩ < Real.pi :=
    jointAngle_lt_pi hB hangle ⟨t - 1, by omega⟩
  have hjoint_eq : jointAngle A ⟨t - 1, by omega⟩
      = sphAngle (A ⟨t - 1, hpre⟩) (A ⟨t, htt⟩) (A ⟨t + 1, ht2⟩) := by
    rw [jointAngle]
    have e1 : (⟨(t - 1) + 1, by omega⟩ : Fin (n + 1)) = (⟨t, htt⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (t - 1) + 1 = t; omega
    have e2 : (⟨(t - 1) + 2, by omega⟩ : Fin (n + 1)) = (⟨t + 1, ht2⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (t - 1) + 2 = t + 1; omega
    rw [show (⟨(t - 1), by omega⟩ : Fin (n + 1)) = (⟨t - 1, hpre⟩ : Fin (n + 1)) from rfl, e1, e2]
  rcases hbridge with h0 | hπ
  · rw [hjoint_eq, h0] at hposJoint; exact lt_irrefl 0 hposJoint
  · rw [hjoint_eq, hπ] at hltJoint; exact lt_irrefl Real.pi hltJoint

























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



/-- **`NoNonadjacentRepeat A`** — the arm `A` never revisits a vertex at two *nonadjacent* positions:
for indices `r + 2 ≤ s` (both in range, `s < n + 1`), the vertices `A r` and `A s` are distinct.

This is the global geometric fact that, on a weakly convex `PositiveJoints` arm, the chain cannot
return to a previously visited vertex without flattening an interior joint.  Supplying it from
`PositiveJoints` alone is the audited out-of-plane master gap (the same obstruction as the tail-half
cone propagation, `HANDOFF/design-rounds/ch13-B5-B1-audit.md` line 3); here it is the honest
explicit, satisfiable hypothesis (see the non-vacuity guards below). -/
def NoNonadjacentRepeat {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1), r + 2 ≤ s →
    A ⟨r, hr⟩ ≠ A ⟨s, hs⟩



/-- **The reduction (unconditional).**  From the fold datum `(a : ℝ)•A(i+1) + (b : ℝ)•A j = A i`
with `a, b : ℝ≥0`, if `a = 0` then `A i = A j` (and `b = 1`).

Proof: with `a = 0` the datum reads `A i = b • A j`; both are unit vectors and `b ≥ 0`, so
`nnreal_smul_unit_eq_unit` (FFCT21 Brick 2) gives `b = 1` and `A i = A j`. -/
theorem repeat_of_a_eq_zero {n : ℕ} {A : Fin (n + 1) → S2} {i j : ℕ}
    (hi2 : i + 1 < n + 1) (hj : j < n + 1) (hii : i < n + 1)
    {a b : ℝ≥0}
    (hcoeff : (a : ℝ) • (A ⟨i + 1, hi2⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) = (A ⟨i, hii⟩ : E3))
    (ha0 : (a : ℝ) = 0) :
    A ⟨i, hii⟩ = A ⟨j, hj⟩ := by
  -- with `a = 0` the datum is `A i = b • A j`.
  have hpav : (A ⟨i, hii⟩ : E3) = (b : ℝ) • (A ⟨j, hj⟩ : E3) := by
    rw [← hcoeff, ha0, zero_smul, zero_add]
  -- Brick 2: a nonnegative multiple of a unit equal to a unit forces equality.
  exact (nnreal_smul_unit_eq_unit (a := (b : ℝ)) b.2 hpav).2



/-- **(`no_repeat_of_positiveJoints`) The leading coefficient is strictly positive.**  Given the fold
datum `(a : ℝ)•A(i+1) + (b : ℝ)•A j = A i` with `a, b : ℝ≥0`, the nonadjacency `i + 2 < j < n+1`, and
the no-repeat hypothesis `NoNonadjacentRepeat A`, the leading coefficient is strictly positive:
`0 < (a : ℝ)`.

This is the exact input the FFCT21 consumption site (`far_fold_i_eq_zero` / the `hnd` datum of
`far_fold_boundary_classification_of_nondeg`) names "out of scope".  Proof: `a ≥ 0` always; if
`a = 0`, the reduction `repeat_of_a_eq_zero` produces the nonadjacent repeat `A i = A j`, contradicted
by `NoNonadjacentRepeat A` at the positions `i, j` (`i + 2 ≤ j`). -/
theorem no_repeat_of_positiveJoints {n : ℕ} {A : Fin (n + 1) → S2}
    (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    {a b : ℝ≥0}
    (hcoeff : (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3)
      = (A ⟨i, by omega⟩ : E3)) :
    0 < (a : ℝ) := by
  rcases lt_or_eq_of_le a.2 with hpos | hzero
  · exact hpos
  · exfalso
    have ha0 : (a : ℝ) = 0 := hzero.symm
    have hii : i < n + 1 := by omega
    have hi2 : i + 1 < n + 1 := by omega
    -- the nonadjacent repeat `A i = A j`.
    have hrep : A ⟨i, hii⟩ = A ⟨j, hj⟩ :=
      repeat_of_a_eq_zero hi2 hj hii hcoeff ha0
    -- contradict `NoNonadjacentRepeat` at `(i, j)` with `i + 2 ≤ j`.
    exact hnr i j hii hj (by omega) hrep



/-- **Assemble the full nondegenerate fold datum.**  From the NNReal span membership
`A i ∈ span≥0 {A(i+1), A j}` (the raw far-fold input), weak convexity, and `NoNonadjacentRepeat A`,
produce the full datum `∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ (a:ℝ)•A(i+1) + (b:ℝ)•A j = A i` that
`far_fold_boundary_classification_of_nondeg` consumes.

`b > 0` is FFCT21 Brick 3 (`coeff_b_pos_of_edge_short`) from the short fold edge `(A i, A(i+1))`;
`a > 0` is `no_repeat_of_positiveJoints`.  This eliminates the `hapos` hypothesis entirely. -/
theorem far_fold_nondeg_datum_of_no_repeat {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3)
        = (A ⟨i, by omega⟩ : E3) := by
  have hii : i < n + 1 := by omega
  have hi2 : i + 1 < n + 1 := by omega
  -- Brick 1: extract the nonnegative coefficients.
  obtain ⟨a, b, hcoeff⟩ := span_pair_coeffs_S2 hcol
  -- the short fold edge `(A i, A(i+1))` from weak convexity.
  have hedge : ShortArc (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    have hn2 : 2 ≤ n := hA.two_le
    have h := hA.closed_convex.edge_short ⟨i, hii⟩
    have hsucc2 : ((⟨i, hii⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc2] at h
  -- `b > 0` (FFCT21 Brick 3) and `a > 0` (this module).
  have hbpos : 0 < (b : ℝ) := coeff_b_pos_of_edge_short hcoeff hedge
  have hapos : 0 < (a : ℝ) := no_repeat_of_positiveJoints hnr hij hj hcoeff
  exact ⟨a, b, hapos, hbpos, hcoeff⟩



/-- **The full boundary classification with `a > 0` discharged from no-repeat.**  Combining the
assembled datum (`far_fold_nondeg_datum_of_no_repeat`) with FFCT21's `i = 0` half: from the raw span
membership `A i ∈ span≥0 {A(i+1), A j}`, weak convexity, `PositiveJoints`, and `NoNonadjacentRepeat`,
the far fold can only occur at `i = 0`. -/
theorem far_fold_boundary_i_eq_zero_of_span {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A) (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    i = 0 :=
  far_fold_boundary_classification_of_nondeg hA hposA hB hangle hij hj
    (far_fold_nondeg_datum_of_no_repeat hA hnr hij hj hcol)

















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









/-- `det3` additive in the *first* argument. -/
theorem det3_add_fst (a b c d : E3) : det3 (a + b) c d = det3 a c d + det3 b c d := by
  simp only [det3, PiLp.add_apply]; ring

/-- `det3` homogeneous in the *first* argument. -/
theorem det3_smul_fst (a c d : E3) (t : ℝ) : det3 (t • a) c d = t * det3 a c d := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring







/-- **(Brick T1) The fold forces a strictly negative `A 2`-witness.**  Under `WeakConvexSphArm A`,
`PositiveJoints A`, the non-flat bound (`StrictConvexSphArm B`, `JointLe A B`), and a fold
`A 0 = a • A 1 + b • A j` with `b > 0` and `2 < j`, the witness determinant is strictly negative:
`det3 (A 1) (A j) (A 2) < 0`.

Route (anchored to the support convention `0 ≤ det3 (A r) (A (r+1)) (A k)`):
weak support of edge `(A 0, A 1)` at `A 2` gives `0 ≤ det3 (A 0) (A 1) (A 2)`.  Substituting the
fold and using first-argument linearity with `det3 (A 1) (A 1) (A 2) = 0` and
`det3 (A j) (A 1) (A 2) = - det3 (A 1) (A j) (A 2)`:
`det3 (A 0) (A 1) (A 2) = b · det3 (A j) (A 1) (A 2) = - b · det3 (A 1) (A j) (A 2)`,
so `det3 (A 1) (A j) (A 2) ≤ 0`.  Equality would make `A 0, A 1, A 2` coplanar through the origin;
since `det3 (A 1) (A j) (A 2) = 0` with the fold also gives `det3 (A 0) (A 1) (A 2) = 0` … but the
*adjacent* triple needed is `det3 (A 0) (A 1) (A 2)`; we instead read the joint at `A 1` directly off
`det3 (A 0) (A 1) (A 2) = 0` via the FFCT21 bridge, refuting `PositiveJoints` + `< π`. -/
theorem fold_A2_witness_negative {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {j : ℕ} (hj : j < n + 1) (_hjfar : 2 < j)
    (h1 : 1 < n + 1) (h2 : 2 < n + 1) (h0 : 0 < n + 1)
    {a b : ℝ} (hb : 0 < b)
    (hfold :
      (A ⟨0, h0⟩ : E3) =
        a • (A ⟨1, h1⟩ : E3) + b • (A ⟨j, hj⟩ : E3)) :
    det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0 := by
  -- successor identity `(⟨0⟩ + 1) = ⟨1⟩` in `Fin (n+1)`.
  have hsucc01 : ((⟨0, h0⟩ : Fin (n + 1)) + 1) = (⟨1, h1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show 0 + 1 < n + 1 by omega)]
  -- weak support of edge `(A 0, A 1)` at `A 2`:  `0 ≤ det3 (A 0) (A 1) (A 2)`.
  have hsupp : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨0, h0⟩ ⟨2, h2⟩
    rw [hsucc01] at h
    exact h
  -- the algebraic identity `det3 (A 0) (A 1) (A 2) = - b · det3 (A 1) (A j) (A 2)`.
  have hid : det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3)
      = - b * det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) := by
    rw [hfold, det3_add_fst, det3_smul_fst, det3_smul_fst]
    -- `det3 (A 1) (A 1) (A 2) = 0`, `det3 (A j) (A 1) (A 2) = - det3 (A 1) (A j) (A 2)`.
    have h11 : det3 (A ⟨1, h1⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) = 0 := by
      simp only [det3]; ring
    have hj1 : det3 (A ⟨j, hj⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3)
        = - det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) := by
      simp only [det3]; ring
    rw [h11, hj1]; ring
  -- hence `det3 (A 1) (A j) (A 2) ≤ 0`.
  have hle : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) ≤ 0 := by
    nlinarith [hid ▸ hsupp, hb]
  -- strict: equality forces a flat joint at `A 1`, refuted.
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    -- `det3 (A 1) (A j) (A 2) = 0` ⟹ `det3 (A 0) (A 1) (A 2) = 0`.
    have hadj0 : det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) = 0 := by
      rw [hid, heq]; ring
    -- short arcs at the apex `A 1`: edges `(A 0, A 1)` and `(A 1, A 2)`.
    have hsau : ShortArc (A ⟨1, h1⟩) (A ⟨0, h0⟩) := by
      have h := hA.closed_convex.edge_short ⟨0, h0⟩
      rw [hsucc01] at h
      exact h.symm
    have hsucc12 : ((⟨1, h1⟩ : Fin (n + 1)) + 1) = (⟨2, h2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show 1 + 1 < n + 1 by omega)]
    have hsav : ShortArc (A ⟨1, h1⟩) (A ⟨2, h2⟩) := by
      have h := hA.closed_convex.edge_short ⟨1, h1⟩
      rw [hsucc12] at h
      exact h
    -- bridge: flat apex at `A 1`.
    have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero (u := A ⟨0, h0⟩) (v := A ⟨1, h1⟩)
      (w := A ⟨2, h2⟩) hsau hsav hadj0
    -- joint angle at index `0`.
    have hposJoint : 0 < jointAngle A ⟨0, by omega⟩ := hposA ⟨0, by omega⟩
    have hltJoint : jointAngle A ⟨0, by omega⟩ < Real.pi :=
      jointAngle_lt_pi hB hangle ⟨0, by omega⟩
    have hjoint_eq : jointAngle A ⟨0, by omega⟩
        = sphAngle (A ⟨0, h0⟩) (A ⟨1, h1⟩) (A ⟨2, h2⟩) := by
      rw [jointAngle]
    rcases hbridge with hz | hpi
    · rw [hjoint_eq, hz] at hposJoint; exact lt_irrefl 0 hposJoint
    · rw [hjoint_eq, hpi] at hltJoint; exact lt_irrefl Real.pi hltJoint



/-- **(Brick T2) The `A j` coefficient is nonnegative.**  With the witness determinant
`D2 := det3 (A 1) (A j) (A 2) < 0`, a real representation `A r = c • A 1 + d • A j`, and the weak
support of edge `(A 1, A 2)` at `A r` (`0 ≤ det3 (A 1) (A 2) (A r)`, the landed support orientation),
the `A j` coefficient is nonnegative: `0 ≤ d`.

Sign chain: expand the support determinant using the representation and first-slot drop
`det3 (A 1) (A 2) (A 1) = 0`:
`det3 (A 1) (A 2) (A r) = d · det3 (A 1) (A 2) (A j) = - d · det3 (A 1) (A j) (A 2) = - d · D2`.
Since `D2 < 0`, `0 ≤ - d · D2` forces `0 ≤ d`. -/
theorem fold_coeff_d_nonneg_of_A2_witness {n : ℕ} {A : Fin (n + 1) → S2}
    {j r : ℕ} (hj : j < n + 1) (hr : r < n + 1) (h1 : 1 < n + 1) (h2 : 2 < n + 1)
    (hD2 :
      det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0)
    {c d : ℝ}
    (hrepr :
      (A ⟨r, hr⟩ : E3) =
        c • (A ⟨1, h1⟩ : E3) + d • (A ⟨j, hj⟩ : E3))
    (hsupp12 :
      0 ≤ det3 (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) (A ⟨r, hr⟩ : E3)) :
    0 ≤ d := by
  -- expand `det3 (A 1) (A 2) (A r) = - d · D2`.
  have hexp : det3 (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) (A ⟨r, hr⟩ : E3)
      = - d * det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) := by
    rw [hrepr]
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `0 ≤ - d · D2` with `D2 < 0` ⟹ `0 ≤ d`.
  rw [hexp] at hsupp12
  nlinarith [hsupp12, hD2]



/-- **The forward collinearity at `t+1` (FFCT22 wrapper, support-convention aligned).**  From the
fold `A 0 = a • A 1 + b • A j` (`b > 0`), the current signed-line datum
`A t = c • A 1 + d • A j` (`d > 0`), and the two weak supports
`0 ≤ det3 (A 0) (A 1) (A (t+1))` (edge `(A 0, A 1)` at `A (t+1)`) and
`0 ≤ det3 (A t) (A (t+1)) (A 1)` (edge `(A t, A (t+1))` at `A 1`), the witness area form vanishes:
`det3 (A 1) (A j) (A (t+1)) = 0`. -/
theorem tail_step_collinear {n : ℕ} {A : Fin (n + 1) → S2}
    {j t : ℕ} (hj : j < n + 1) (h1 : 1 < n + 1) (h0 : 0 < n + 1)
    (htt : t < n + 1) (ht2 : t + 1 < n + 1)
    {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hfold : (A ⟨0, h0⟩ : E3) = a • (A ⟨1, h1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hcurr : (A ⟨t, htt⟩ : E3) = c • (A ⟨1, h1⟩ : E3) + d • (A ⟨j, hj⟩ : E3))
    (hsupp1 : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨t + 1, ht2⟩ : E3))
    (hsupp2 : 0 ≤ det3 (A ⟨t, htt⟩ : E3) (A ⟨t + 1, ht2⟩ : E3) (A ⟨1, h1⟩ : E3)) :
    det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨t + 1, ht2⟩ : E3) = 0 :=
  far_fold_tail_collinear_step (v := (A ⟨1, h1⟩ : E3)) (w := (A ⟨j, hj⟩ : E3))
    (z₀ := (A ⟨0, h0⟩ : E3)) (zt := (A ⟨t, htt⟩ : E3)) (z' := (A ⟨t + 1, ht2⟩ : E3))
    hb hd hfold hcurr hsupp1 hsupp2





/-- **The absorption refutation.**  If the propagated representation has `d' = 0`, so
`A (t+1) = c' • A 1`, then `A (t+1) = ± A 1`; both are refuted: `+ A 1` by the no-repeat hypothesis
(at a nonadjacent index `2 ≤ t`), `- A 1` by the antiparallel-exclusion hypothesis. -/
theorem tail_step_absorb_refuted {n : ℕ} {A : Fin (n + 1) → S2}
    {t : ℕ} (h1 : 1 < n + 1) (ht2 : t + 1 < n + 1) (_ht_ge : 2 ≤ t)
    {c' : ℝ}
    (hrepr0 : (A ⟨t + 1, ht2⟩ : E3) = c' • (A ⟨1, h1⟩ : E3))
    (hnorepeat : A ⟨1, h1⟩ ≠ A ⟨t + 1, ht2⟩)
    (hnotanti : (A ⟨t + 1, ht2⟩ : E3) ≠ - (A ⟨1, h1⟩ : E3)) :
    False := by
  -- `‖A (t+1)‖ = 1 = |c'| · ‖A 1‖ = |c'|`, so `|c'| = 1`, i.e. `c' = 1 ∨ c' = -1`.
  have hnorm : |c'| = 1 := by
    have := congrArg (fun x : E3 => ‖x‖) hrepr0
    simp only [norm_smul, Real.norm_eq_abs] at this
    rw [(A ⟨t + 1, ht2⟩).2, (A ⟨1, h1⟩).2, mul_one] at this
    linarith [this]
  have hcases : c' = 1 ∨ c' = -1 := abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hnorm
  rcases hcases with hc | hc
  · -- `A (t+1) = A 1`: nonadjacent repeat.
    apply hnorepeat
    apply S2.ext
    rw [hrepr0, hc, one_smul]
  · -- `A (t+1) = - A 1`: antiparallel.
    apply hnotanti
    rw [hrepr0, hc]
    simp




















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



/-- **(Brick U1) No antipodal vertices.**  On a weakly convex arm `A`, whose closure carries an open
supporting hemisphere `⟪h, A i⟫ > 0` for all `i`, two vertices can never be antipodal:
`(A ⟨r, hr⟩ : E3) ≠ - (A ⟨s, hs⟩ : E3)`.  If they were, `0 < ⟪h, A r⟫ = - ⟪h, A s⟫ < 0`. -/
theorem not_antipodal_of_hemisphere {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1) :
    (A ⟨r, hr⟩ : E3) ≠ - (A ⟨s, hs⟩ : E3) := by
  obtain ⟨h, _, hpos⟩ := hA.closed_convex.open_hemisphere
  intro hanti
  have hr' : 0 < (⟪h, (A ⟨r, hr⟩ : E3)⟫ : ℝ) := hpos ⟨r, hr⟩
  have hs' : 0 < (⟪h, (A ⟨s, hs⟩ : E3)⟫ : ℝ) := hpos ⟨s, hs⟩
  rw [hanti, inner_neg_right] at hr'
  linarith



/-- The reciprocal-basis decomposition.  For any `v w z : E3` with `m := v × w`, the vector triple
products give `‖m‖² • z = ⟪z, m⟫ • m + (det3-free combination of v, w)`.  Concretely, writing
`g_vv = ⟪v,v⟫`, `g_ww = ⟪w,w⟫`, `g_vw = ⟪v,w⟫`, `z_v = ⟪z,v⟫`, `z_w = ⟪z,w⟫`, and using
`⟪z, m⟫ = det3 v w z` (which we will set to `0`):
`‖m‖² • z = ⟪z,m⟫ • m + (z_v g_ww − z_w g_vw) • v + (z_w g_vv − z_v g_vw) • w`.
This is the standard Gram/reciprocal identity; here proved by `cross_cross` expansion. -/
theorem recip_basis_decomp (v w z : E3) :
    (‖cross v w‖ ^ 2 : ℝ) • z =
      (⟪z, cross v w⟫ : ℝ) • cross v w
        + ((⟪z, v⟫ : ℝ) * ⟪w, w⟫ - (⟪z, w⟫ : ℝ) * ⟪v, w⟫) • v
        + ((⟪z, w⟫ : ℝ) * ⟪v, v⟫ - (⟪z, v⟫ : ℝ) * ⟪v, w⟫) • w := by
  set m : E3 := cross v w with hm
  -- `m × (m × z) = ⟪m,z⟫ • m − ⟪m,m⟫ • z`  (cross_cross a b c = ⟪a,c⟫•b − ⟪a,b⟫•c).
  have hmmz : cross m (cross m z) = (⟪m, z⟫ : ℝ) • m - (⟪m, m⟫ : ℝ) • z := cross_cross m m z
  -- `m × z = cross (v×w) z`.  Expand `cross (cross v w) z = -(cross z (cross v w))`.
  have hmz : cross m z = (⟪z, v⟫ : ℝ) • w - (⟪z, w⟫ : ℝ) • v := by
    have e1 : cross z (cross v w) = (⟪z, w⟫ : ℝ) • v - (⟪z, v⟫ : ℝ) • w := cross_cross z v w
    have e2 : cross m z = - cross z m := by
      rw [hm]; rw [cross_antisymm]
    rw [e2, hm, e1]; module
  -- now `cross m (cross m z) = cross m ((z_v)•w − (z_w)•v)`.
  have hmw : cross m w = (⟪w, v⟫ : ℝ) • w - (⟪w, w⟫ : ℝ) • v := by
    have e1 : cross w (cross v w) = (⟪w, w⟫ : ℝ) • v - (⟪w, v⟫ : ℝ) • w := cross_cross w v w
    have e2 : cross m w = - cross w m := by rw [hm, cross_antisymm]
    rw [e2, hm, e1]; module
  have hmv : cross m v = (⟪v, v⟫ : ℝ) • w - (⟪v, w⟫ : ℝ) • v := by
    have e1 : cross v (cross v w) = (⟪v, w⟫ : ℝ) • v - (⟪v, v⟫ : ℝ) • w := cross_cross v v w
    have e2 : cross m v = - cross v m := by rw [hm, cross_antisymm]
    rw [e2, hm, e1]; module
  -- assemble: `cross m (cross m z) = z_v • (cross m w) − z_w • (cross m v)`.
  have hexpand : cross m (cross m z)
      = (⟪z, v⟫ : ℝ) • cross m w - (⟪z, w⟫ : ℝ) • cross m v := by
    rw [hmz, cross_sub_right', cross_smul_right, cross_smul_right]
  rw [hexpand, hmw, hmv] at hmmz
  -- `⟪m,m⟫ = ‖m‖²` and `⟪w,v⟫ = ⟪v,w⟫`.
  have hmm : (⟪m, m⟫ : ℝ) = ‖m‖ ^ 2 := real_inner_self_eq_norm_sq m
  have hwv : (⟪w, v⟫ : ℝ) = (⟪v, w⟫ : ℝ) := real_inner_comm v w
  rw [hmm, hwv] at hmmz
  -- hmmz : z_v•(g_vw•w − g_ww•v) − z_w•(g_vv•w − g_vw•v) = ⟪m,z⟫•m − ‖m‖²•z
  -- rearrange to the target.
  have hmz_comm : (⟪m, z⟫ : ℝ) = (⟪z, m⟫ : ℝ) := real_inner_comm z m
  rw [hmz_comm] at hmmz
  -- solve for ‖m‖²•z.
  rw [hm] at hmmz ⊢
  linear_combination (norm := module) hmmz

/-- **(Brick U2) Span extraction from a vanishing area form over an independent base pair.**
Two UNIT vectors `v, w` with `v ≠ w` and `v ≠ - w` are linearly independent, and any `z` with
`det3 v w z = 0` lies in their real span: `∃ c d : ℝ, z = c • v + d • w`. -/
theorem lin_indep_span_of_det3_zero {v w z : E3}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hne : v ≠ w) (hanti : v ≠ - w)
    (hdet : det3 v w z = 0) :
    ∃ c d : ℝ, z = c • v + d • w := by
  -- `m = v × w` is nonzero: else `‖v×w‖² = ‖v‖²‖w‖² − ⟪v,w⟫² = 0`, forcing `⟪v,w⟫ = ±1`, i.e. `v = ±w`.
  have hmne : cross v w ≠ 0 := by
    intro h0
    have hnsq : (⟪cross v w, cross v w⟫ : ℝ) = 0 := by rw [h0]; simp
    rw [norm_cross_sq, hv, hw] at hnsq
    -- `1·1 − ⟪v,w⟫² = 0` ⟹ `⟪v,w⟫² = 1` ⟹ `⟪v,w⟫ = 1 ∨ = -1`.
    have hg2 : (⟪v, w⟫ : ℝ) ^ 2 = 1 := by nlinarith [hnsq]
    have hcases : (⟪v, w⟫ : ℝ) = 1 ∨ (⟪v, w⟫ : ℝ) = -1 := by
      have hfac : ((⟪v, w⟫ : ℝ) - 1) * ((⟪v, w⟫ : ℝ) + 1) = 0 := by nlinarith [hg2]
      rcases mul_eq_zero.mp hfac with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hcases with h1 | h1
    · -- ⟪v,w⟫ = 1 = ‖v‖‖w‖ ⟹ v = w (equality in Cauchy–Schwarz).
      apply hne
      have hpar := inner_eq_norm_mul_iff_real.mp (by rw [h1, hv, hw, mul_one])
      -- hpar : ‖w‖ • v = ‖v‖ • w
      rw [hv, hw, one_smul, one_smul] at hpar
      exact hpar
    · -- ⟪v,w⟫ = -1 ⟹ v = -w.
      apply hanti
      have hpar := inner_eq_norm_mul_iff_real.mp
        (show (⟪v, -w⟫ : ℝ) = ‖v‖ * ‖-w‖ by rw [inner_neg_right, h1, hv, norm_neg, hw]; ring)
      rw [hv, norm_neg, hw, one_smul, one_smul] at hpar
      -- hpar : v = -w
      rw [hpar]
  -- ⟪z, m⟫ = det3 v w z = 0 (cyclic + inner_cross_eq_det3).
  have hzm : (⟪z, cross v w⟫ : ℝ) = 0 := by
    rw [inner_cross_eq_det3, det3_cyclic z v w]; exact hdet
  -- the reciprocal-basis decomposition with ⟪z,m⟫ = 0.
  have hdecomp := recip_basis_decomp v w z
  rw [hzm, zero_smul, zero_add] at hdecomp
  -- `‖m‖² ≠ 0`.
  have hmsq : (‖cross v w‖ ^ 2 : ℝ) ≠ 0 := by
    have : (0:ℝ) < ‖cross v w‖ := norm_pos_iff.mpr hmne
    positivity
  -- divide out ‖m‖².
  refine ⟨(‖cross v w‖ ^ 2)⁻¹ * ((⟪z, v⟫ : ℝ) * ⟪w, w⟫ - (⟪z, w⟫ : ℝ) * ⟪v, w⟫),
          (‖cross v w‖ ^ 2)⁻¹ * ((⟪z, w⟫ : ℝ) * ⟪v, v⟫ - (⟪z, v⟫ : ℝ) * ⟪v, w⟫), ?_⟩
  have hscaled := congrArg (fun x : E3 => (‖cross v w‖ ^ 2)⁻¹ • x) hdecomp
  simp only at hscaled
  rw [smul_smul, inv_mul_cancel₀ hmsq, one_smul, smul_add, smul_smul, smul_smul] at hscaled
  exact hscaled



/-- **(Brick U3a) `A 1 ≠ A j`** in the far-fold tail context (`1 + 2 ≤ j`): a nonadjacent repeat,
excluded by `NoNonadjacentRepeat`. -/
theorem A1_ne_Aj {n : ℕ} {A : Fin (n + 1) → S2}
    (hnr : NoNonadjacentRepeat A) {j : ℕ} (h1 : 1 < n + 1) (hj : j < n + 1) (hjfar : 3 ≤ j) :
    A ⟨1, h1⟩ ≠ A ⟨j, hj⟩ :=
  hnr 1 j h1 hj (by omega)

/-- **(Brick U3b) `A 1 ≠ - A j`** in the far-fold tail context: antipodal pair excluded by the open
hemisphere (Brick U1). -/
theorem A1_not_antipodal_Aj {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) {j : ℕ} (h1 : 1 < n + 1) (hj : j < n + 1) :
    (A ⟨1, h1⟩ : E3) ≠ - (A ⟨j, hj⟩ : E3) :=
  not_antipodal_of_hemisphere hA h1 hj

/-- **(Brick U3c) Span representation of a tail vertex on the fold line.**  Given the collinearity
`det3 (A 1) (A j) z = 0` and the nondegeneracy of the base pair `A 1, A j`, the vertex `z = A k`
has a real representation `A k = c • A 1 + d • A j`. -/
theorem repr_of_collinear {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    {j k : ℕ} (h1 : 1 < n + 1) (hj : j < n + 1) (hk : k < n + 1) (hjfar : 3 ≤ j)
    (hdet : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨k, hk⟩ : E3) = 0) :
    ∃ c d : ℝ, (A ⟨k, hk⟩ : E3) = c • (A ⟨1, h1⟩ : E3) + d • (A ⟨j, hj⟩ : E3) :=
  lin_indep_span_of_det3_zero (A ⟨1, h1⟩).2 (A ⟨j, hj⟩).2
    (fun h => A1_ne_Aj hnr h1 hj hjfar (S2.ext h))
    (A1_not_antipodal_Aj hA h1 hj) hdet



/-- **(Brick U4) The two-step tail refutation.**  In the far-fold `i = 0` configuration with a fold
`A 0 = a • A 1 + b • A j` (`b > 0`) at an *interior* tail index (`3 ≤ j`, `j + 2 < n + 1`), the
signed-line propagation runs exactly TWO steps from the seed at `j`, putting `A (j+1)` and `A (j+2)`
on the fold line `span {A 1, A j}`.  The consecutive triple `A j, A (j+1), A (j+2)` is then coplanar
(`det3 = 0`), and `far_fold_tail_not_interior` at apex `A (j+1)` (joint index `j`) contradicts
`PositiveJoints A` and the non-flat bound `jointAngle A · < π`.  Hence `False`. -/
theorem tail_two_step_refutation {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (hnr : NoNonadjacentRepeat A)
    {j : ℕ} (hjfar : 3 ≤ j) (hjtail : j + 2 < n + 1)
    (h0 : 0 < n + 1) (h1 : 1 < n + 1) (h2 : 2 < n + 1) (hj : j < n + 1)
    {a b : ℝ} (hb : 0 < b)
    (hfold : (A ⟨0, h0⟩ : E3) = a • (A ⟨1, h1⟩ : E3) + b • (A ⟨j, hj⟩ : E3)) :
    False := by
  -- index bounds for the three tail vertices.
  have hj1 : j + 1 < n + 1 := by omega
  have hj2 : j + 2 < n + 1 := hjtail
  -- the controlled witness sign `D2 := det3 (A 1) (A j) (A 2) < 0`.
  have hD2 : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0 :=
    fold_A2_witness_negative hA hposA hB hangle hj (by omega) h1 h2 h0 hb hfold
  -- ===== Step 1 (t = j): push A (j+1) onto the line. =====
  -- the seed datum at j: `A j = 0•A 1 + 1•A j`, with d = 1 > 0.
  -- collinearity `det3 (A 1) (A j) (A (j+1)) = 0` from `tail_step_collinear` (t := j).
  -- weak supports of the two edges.
  have hsucc01 : ((⟨0, h0⟩ : Fin (n + 1)) + 1) = (⟨1, h1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show 0 + 1 < n + 1 by omega)]
  have hsuccj : ((⟨j, hj⟩ : Fin (n + 1)) + 1) = (⟨j + 1, hj1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show j + 1 < n + 1 by omega)]
  -- support of edge (A 0, A 1) at A (j+1): `0 ≤ det3 (A 0) (A 1) (A (j+1))`.
  have hsupp1_s1 : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨0, h0⟩ ⟨j + 1, hj1⟩
    rw [hsucc01] at h; exact h
  -- support of edge (A j, A (j+1)) at A 1: `0 ≤ det3 (A j) (A (j+1)) (A 1)`.
  have hsupp2_s1 : 0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) (A ⟨1, h1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨j, hj⟩ ⟨1, h1⟩
    rw [hsuccj] at h; exact h
  -- seed representation `A j = 0•A 1 + 1•A j`.
  have hseed : (A ⟨j, hj⟩ : E3) = (0:ℝ) • (A ⟨1, h1⟩ : E3) + (1:ℝ) • (A ⟨j, hj⟩ : E3) := by
    rw [zero_smul, one_smul, zero_add]
  have hcol1 : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) = 0 :=
    tail_step_collinear hj h1 h0 hj hj1 hb (by norm_num : (0:ℝ) < 1) hfold hseed
      hsupp1_s1 hsupp2_s1
  -- span representation of A (j+1).
  obtain ⟨c1, d1, hrepr1⟩ := repr_of_collinear hA hnr h1 hj hj1 hjfar hcol1
  -- ===== Step 2 (t = j+1): push A (j+2) onto the line. =====
  -- We need d1 > 0 to apply tail_step_collinear at t = j+1; obtain it via T2 + absorption refutation.
  -- weak support of edge (A 1, A 2) at A (j+1): `0 ≤ det3 (A 1) (A 2) (A (j+1))`.
  have hsucc12 : ((⟨1, h1⟩ : Fin (n + 1)) + 1) = (⟨2, h2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show 1 + 1 < n + 1 by omega)]
  have hsupp12_s1 : 0 ≤ det3 (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨1, h1⟩ ⟨j + 1, hj1⟩
    rw [hsucc12] at h; exact h
  -- T2: `0 ≤ d1`.
  have hd1_nonneg : 0 ≤ d1 :=
    fold_coeff_d_nonneg_of_A2_witness hj hj1 h1 h2 hD2 hrepr1 hsupp12_s1
  -- absorption refutation: d1 = 0 would force A (j+1) = ± A 1 (repeat / antipodal), excluded.
  have hd1_pos : 0 < d1 := by
    rcases lt_or_eq_of_le hd1_nonneg with hpos | hzero
    · exact hpos
    · exfalso
      have hrepr0 : (A ⟨j + 1, hj1⟩ : E3) = c1 • (A ⟨1, h1⟩ : E3) := by
        rw [hrepr1, ← hzero, zero_smul, add_zero]
      exact tail_step_absorb_refuted h1 hj1 (by omega) hrepr0
        (hnr 1 (j + 1) h1 hj1 (by omega))
        (not_antipodal_of_hemisphere hA hj1 h1)
  -- collinearity at t = j+1: `det3 (A 1) (A j) (A (j+2)) = 0`.
  have hsuccj1 : ((⟨j + 1, hj1⟩ : Fin (n + 1)) + 1) = (⟨j + 2, hj2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show (j + 1) + 1 < n + 1 by omega)]
  have hsupp1_s2 : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨j + 2, hj2⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨0, h0⟩ ⟨j + 2, hj2⟩
    rw [hsucc01] at h; exact h
  have hsupp2_s2 : 0 ≤ det3 (A ⟨j + 1, hj1⟩ : E3) (A ⟨j + 2, hj2⟩ : E3) (A ⟨1, h1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨j + 1, hj1⟩ ⟨1, h1⟩
    rw [hsuccj1] at h; exact h
  -- the (j+2)-index collinearity: use the FFCT22 step directly with v=A1, w=Aj, zt = A(j+1).
  have hcol2 : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨j + 2, hj2⟩ : E3) = 0 :=
    far_fold_tail_collinear_step (v := (A ⟨1, h1⟩ : E3)) (w := (A ⟨j, hj⟩ : E3))
      (z₀ := (A ⟨0, h0⟩ : E3)) (zt := (A ⟨j + 1, hj1⟩ : E3)) (z' := (A ⟨j + 2, hj2⟩ : E3))
      hb hd1_pos hfold hrepr1 hsupp1_s2 hsupp2_s2
  -- span representation of A (j+2).
  obtain ⟨c2, d2, hrepr2⟩ := repr_of_collinear hA hnr h1 hj hj2 hjfar hcol2
  -- ===== The consecutive triple A j, A (j+1), A (j+2) is coplanar. =====
  have htriple : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) (A ⟨j + 2, hj2⟩ : E3) = 0 :=
    coplanar_triple_det3_zero
      (v := (A ⟨1, h1⟩ : E3)) (w := (A ⟨j, hj⟩ : E3))
      ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
      ⟨c1, d1, hrepr1.symm⟩
      ⟨c2, d2, hrepr2.symm⟩
  -- ===== Fire far_fold_tail_not_interior at t = j+1 (apex A (j+1), joint index j). =====
  -- short arcs at apex A (j+1): towards A j and A (j+2).
  -- ShortArc (A (j+1)) (A j): from edge_short of edge (A j, A (j+1)) symmetrised.
  have hsau : ShortArc (A ⟨j + 1, hj1⟩) (A ⟨(j + 1) - 1, by omega⟩) := by
    have hidx : (⟨(j + 1) - 1, by omega⟩ : Fin (n + 1)) = (⟨j, hj⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (j + 1) - 1 = j; omega
    rw [hidx]
    have h := hA.closed_convex.edge_short ⟨j, hj⟩
    rw [hsuccj] at h; exact h.symm
  have hsav : ShortArc (A ⟨j + 1, hj1⟩) (A ⟨(j + 1) + 1, by omega⟩) := by
    have hidx : (⟨(j + 1) + 1, by omega⟩ : Fin (n + 1)) = (⟨j + 2, hj2⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (j + 1) + 1 = j + 2; omega
    rw [hidx]
    have h := hA.closed_convex.edge_short ⟨j + 1, hj1⟩
    rw [hsuccj1] at h; exact h
  -- the collinearity in the t-1,t,t+1 shape for t = j+1.
  have hcol_triple : det3 (A ⟨(j + 1) - 1, by omega⟩ : E3) (A ⟨j + 1, hj1⟩ : E3)
      (A ⟨(j + 1) + 1, by omega⟩ : E3) = 0 := by
    have hidx1 : (⟨(j + 1) - 1, by omega⟩ : Fin (n + 1)) = (⟨j, hj⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (j + 1) - 1 = j; omega
    have hidx2 : (⟨(j + 1) + 1, by omega⟩ : Fin (n + 1)) = (⟨j + 2, hj2⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (j + 1) + 1 = j + 2; omega
    rw [hidx1, hidx2]; exact htriple
  exact far_fold_tail_not_interior hposA hB hangle (t := j + 1) (by omega) (by omega)
    (by omega) hj1 (by omega) hsau hsav hcol_triple



/-- **(Brick U5) Far-fold boundary classification — the UNCONDITIONAL B5.**  From the raw NNReal span
membership `A i ∈ span≥0 {A (i+1), A j}` (the FFCT23 input shape), weak convexity, `PositiveJoints`,
the non-flat bound, and `NoNonadjacentRepeat`, the far fold is a boundary fold:
`i = 0 ∧ (j = n ∨ j = n − 1)`.  NO `TailConePropagates` hypothesis is needed — the tail half is
closed by the signed-line two-step refutation `tail_two_step_refutation`.

Route: FFCT23's `far_fold_boundary_i_eq_zero_of_span` gives `i = 0`; then if `j + 2 < n + 1`
(`j ≤ n − 2`, the interior tail), the `i = 0` fold datum reads `A 0 = a • A 1 + b • A j` with `b > 0`
(FFCT23's assembled nondegenerate datum), and U4 derives `False`; hence `¬(j + 2 < n + 1)`, so with
`j < n + 1`: `j = n ∨ j = n − 1` by `omega`. -/
theorem far_fold_boundary_classification_unconditional {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    i = 0 ∧ (j = n ∨ j = n - 1) := by
  -- the `i = 0` half (FFCT23).
  have hi0 : i = 0 := far_fold_boundary_i_eq_zero_of_span hA hposA hnr hB hangle hij hj hcol
  refine ⟨hi0, ?_⟩
  -- the tail half: refute `j ≤ n - 2` via U4.
  by_contra hjne
  -- from `¬(j = n ∨ j = n - 1)` and `j < n + 1`: `j + 2 < n + 1`.
  have hjnn : j ≠ n := fun h => hjne (Or.inl h)
  have hjnn1 : j ≠ n - 1 := fun h => hjne (Or.inr h)
  have hjtail : j + 2 < n + 1 := by omega
  -- specialise the span membership at i = 0.
  subst hi0
  -- index facts.
  have h0 : 0 < n + 1 := by omega
  have h1 : 1 < n + 1 := by omega
  have h2 : 2 < n + 1 := by omega
  have hjfar : 3 ≤ j := by omega
  -- assemble the nondegenerate datum `∃ a b, 0 < a ∧ 0 < b ∧ a•A1 + b•Aj = A0`.
  have hnd := far_fold_nondeg_datum_of_no_repeat hA hnr hij hj hcol
  obtain ⟨a, b, _ha, hb, hcoeff⟩ := hnd
  -- rewrite to the fold orientation `A 0 = a•A 1 + b•A j` (real coercions).
  have hfold : (A ⟨0, h0⟩ : E3) = (a : ℝ) • (A ⟨1, h1⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) := by
    -- hcoeff : (a:ℝ)•A(0+1) + (b:ℝ)•A j = A 0.  Indices `0+1` and `1` coincide.
    have hidx : (⟨0 + 1, by omega⟩ : Fin (n + 1)) = (⟨1, h1⟩ : Fin (n + 1)) := by
      apply Fin.ext; rfl
    have hidx0 : (⟨0, by omega⟩ : Fin (n + 1)) = (⟨0, h0⟩ : Fin (n + 1)) := rfl
    rw [hidx] at hcoeff
    rw [hidx0] at hcoeff
    exact hcoeff.symm
  exact tail_two_step_refutation hA hposA hB hangle hnr hjfar hjtail h0 h1 h2 hj hb hfold

/-- **(Brick U5 / T7 headline) The downstream-swap form.**  This mirrors FFCT22's conditional
`far_fold_boundary_classification` but with the `TailConePropagates` hypothesis (`htail`) REMOVED:
the tail half is now closed unconditionally.  The `hnd` nondegenerate-coefficient datum is consumed
exactly as FFCT22's version, plus the satisfiable `NoNonadjacentRepeat A` (already the assumption of
FFCT23's `i = 0` half), so the downstream consumer swaps `htail` out for `hnr` in one line. -/
theorem far_fold_boundary_classification_final {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hnd : ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) = (A ⟨i, by omega⟩ : E3)) :
    i = 0 ∧ (j = n ∨ j = n - 1) := by
  -- reconstruct the NNReal span membership from the explicit datum, then apply U5.
  obtain ⟨a, b, _ha, _hb, hcoeff⟩ := hnd
  have hmem : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3) := by
    rw [Submodule.mem_span_pair]
    exact ⟨a, b, by rw [NNReal.smul_def, NNReal.smul_def]; exact hcoeff⟩
  exact far_fold_boundary_classification_unconditional hA hposA hB hangle hnr hij hj hmem

















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





























/-- Rotation is injective on `E3`: `rot k θ` is norm-preserving and additive, so `rot k θ u =
rot k θ v → u = v`. -/
theorem rot_injective {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) {u v : E3}
    (h : rot k θ u = rot k θ v) : u = v := by
  have hz : rot k θ (u - v) = 0 := by rw [rot_sub, h, sub_self]
  have : ‖u - v‖ = 0 := by rw [← norm_rot hk θ (u - v), hz, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)













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



/-- **The joint's axis-anchored support is strictly negative (the sign-bug root).**  For a strictly
convex arm `A` and an interior joint `k` (axis `K = openingAxis k = ⟨k+1⟩`), the triple
`(A K, jointPrev A k, jointNext A k) = (A⟨k+1⟩, A⟨k⟩, A⟨k+2⟩)` has *negative* orientation:
`sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0`.

This is the swap of the strictly-positive consecutive support
`0 < sOrient (A⟨k⟩)(A⟨k+1⟩)(A⟨k+2⟩)` (`cut_diagonal_supports`).  Via the keystone-sign bridge
`inner_tangent_cross_eq_neg_sOrient`, a *negative* `sOrient (A K)(jointPrev)(jointNext)` means the
oriented tangent datum `⟪tangentTo (A K) jointPrev, (A K) × tangentTo (A K) jointNext⟫ > 0`, so the
`-θ` keystone `openedAngle_ge_of_oriented_neg` governs: the opened interior joint **widens under `-θ`**
and **closes under `+θ`** — the opposite of the monitored family's `+δ` convention. -/
theorem joint_axis_support_neg {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) :
    sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0 := by
  have hk := k.isLt
  haveI : NeZero (n + 1) := ⟨by omega⟩
  -- the consecutive support is strictly positive.
  have hlt0 : (⟨k.val, by omega⟩ : Fin (n + 1)) < (⟨k.val + 1, by omega⟩ : Fin (n + 1)) :=
    Fin.mk_lt_mk.mpr (by omega)
  have hlt1 : (⟨k.val + 1, by omega⟩ : Fin (n + 1)) < (⟨k.val + 2, by omega⟩ : Fin (n + 1)) :=
    Fin.mk_lt_mk.mpr (by omega)
  have hpos : 0 < sOrient (A ⟨k.val, by omega⟩) (A ⟨k.val + 1, by omega⟩) (A ⟨k.val + 2, by omega⟩) :=
    cut_diagonal_supports hA.closed_convex hlt0 hlt1
  -- rewrite the three vertices into jointPrev / openingAxis / jointNext form.
  have ep : jointPrev A k = A ⟨k.val, by omega⟩ := rfl
  have en : jointNext A k = A ⟨k.val + 2, by omega⟩ := rfl
  have ea : (A (openingAxis k)) = A ⟨k.val + 1, by omega⟩ := by
    congr 1
  rw [ep, en, ea]
  -- sOrient (A⟨k+1⟩)(A⟨k⟩)(A⟨k+2⟩) = -sOrient (A⟨k⟩)(A⟨k+1⟩)(A⟨k+2⟩)  (swap first two).
  have hswap : sOrient (A ⟨k.val + 1, by omega⟩) (A ⟨k.val, by omega⟩) (A ⟨k.val + 2, by omega⟩)
      = - sOrient (A ⟨k.val, by omega⟩) (A ⟨k.val + 1, by omega⟩) (A ⟨k.val + 2, by omega⟩) := by
    simp only [sOrient, det3]; ring
  rw [hswap]; linarith





/-- **Interior endpoint monotonicity in the genuine opening direction `-δ`.**  At the opening axis
`K = openingAxis k` of a strictly convex arm, opening by `-δ` (`0 ≤ δ`, within the great-semicircle
angle cap at the base triangle) does not decrease the endpoint.  This is the banked
`endpt_openTail_interior_mono` specialised to the opening axis; it is the *correct* companion to the
requested (false) `+δ` lemma.  Note `K.val = k+1 ≥ 1` and `K.val = k+1 < n` are exactly
`openingAxis_interior`. -/
theorem endpt_openTail_interior_mono_neg {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδπ : δ + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi) :
    endpt A ≤ endpt (openTail A (openingAxis k) (-δ)) := by
  obtain ⟨hK0, hKn⟩ := openingAxis_interior k
  exact endpt_openTail_interior_mono hA hK0 hKn hδ0 hδπ























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

















/-- The equator index set of the opened arm: vertices pushed onto the `h₀`-equator. -/
def equatorSet {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ) :
    Fin (n + 1) → Prop :=
  fun r => (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ) = 0

instance equatorSet_decidable {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ) :
    DecidablePred (equatorSet A K h₀ δ) := fun _ => Classical.dec _













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



/-- **Antipodal third column vanishing.**  For any `x y : E3`, `det3 x y (-x) = 0`. -/
theorem det3_antipodal_third_eq_zero (x y : E3) : det3 x y (-x) = 0 := by
  simp only [det3, PiLp.neg_apply]; ring

/-- **Antipodal support vanishing.**  If the third vertex is the antipode of the first
(`(c : E3) = -(a : E3)`), then `sOrient a b c = 0`. -/
theorem sOrient_antipodal_third_eq_zero {a b c : S2} (h : (c : E3) = -(a : E3)) :
    sOrient a b c = 0 := by
  rw [sOrient, h, det3_antipodal_third_eq_zero]



/-- **LEVER 1 — antipodal equator pair excluded by strict supports.**  In the all-supports-strict
branch (`hmix`), if two opened-arm vertices `A' r`, `A' s` are antipodal (`(A' r : E3) = -(A' s : E3)`)
with `r ≠ s` and `r ≠ s + 1`, then `False`: the non-incident support `sOrient (A' s) (A' (s+1)) (A' r)`
vanishes identically (the antipodal `det3`), contradicting its strict positivity. -/
theorem antipodal_pair_excluded_of_strict {n : ℕ} {A : Fin (n + 1) → S2} {K : Fin (n + 1)} {δ : ℝ}
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    {r s : Fin (n + 1)} (hrs : r ≠ s) (hrs1 : r ≠ s + 1)
    (hanti : ((openTail A K δ r : S2) : E3) = -((openTail A K δ s : S2) : E3)) :
    False := by
  have hzero : sOrient (openTail A K δ s) (openTail A K δ (s + 1)) (openTail A K δ r) = 0 :=
    sOrient_antipodal_third_eq_zero hanti
  have hpos : 0 < sOrient (openTail A K δ s) (openTail A K δ (s + 1)) (openTail A K δ r) :=
    hmix s r hrs hrs1
  rw [hzero] at hpos
  exact lt_irrefl _ hpos











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



/-- **Separation core.**  For a *finite* set `s` of vectors in `E3`, if the origin is not in the
convex hull of `s`, then there is a direction `t` strictly positive against every member of `s`. -/
theorem exists_inner_pos_of_zero_notMem_convexHull {s : Set E3} (hfin : s.Finite)
    (h0 : (0 : E3) ∉ convexHull ℝ s) :
    ∃ t : E3, ∀ v ∈ s, 0 < (⟪t, v⟫ : ℝ) := by
  -- the convex hull of a finite set is convex and closed; `0` is outside it.
  have hconv : Convex ℝ (convexHull ℝ s) := convex_convexHull ℝ s
  have hclosed : IsClosed (convexHull ℝ s) := hfin.isClosed_convexHull ℝ
  obtain ⟨f, u, hf0, hfb⟩ :=
    geometric_hahn_banach_point_closed hconv hclosed h0
  -- `f 0 = 0 < u`, and `u < f x` for every hull point; in particular for every `v ∈ s ⊆ hull`.
  have hf0' : (0 : ℝ) < u := by simpa using hf0
  -- Riesz: realise `f` as `⟪t, ·⟫`.
  refine ⟨(InnerProductSpace.toDual ℝ E3).symm f, fun v hv => ?_⟩
  have hvhull : v ∈ convexHull ℝ s := subset_convexHull ℝ s hv
  have : u < f v := hfb v hvhull
  have hriesz : (⟪(InnerProductSpace.toDual ℝ E3).symm f, v⟫ : ℝ) = f v :=
    InnerProductSpace.toDual_symm_apply
  rw [hriesz]
  linarith



/-- **`det3` edge functional over a weighted Finset sum.**  For fixed `a b : E3`,
`det3 a b (∑ y ∈ t, w y • y) = ∑ y ∈ t, w y * det3 a b y`. -/
theorem det3_edge_centerSum (a b : E3) (t : Finset E3) (w : E3 → ℝ) :
    det3 a b (∑ y ∈ t, w y • y) = ∑ y ∈ t, w y * det3 a b y := by
  classical
  induction t using Finset.induction with
  | empty => simp [det3]
  | insert x t hx ih =>
      rw [Finset.sum_insert hx, ProofsInTheBook.ZinanFFCT10.det3_add_right,
        ProofsInTheBook.ZinanFFCT10.det3_smul_right, ih, Finset.sum_insert hx]
















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

/-- The apex (mid) vertex of interior joint `r` is `P (r.val + 1)` whether written via `Fin` addition
or the nat index. -/
 theorem P_jIdx_succ {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P (jIdx r + 1) = P ⟨r.val + 1, by have := r.isLt; omega⟩ := by
  congr 1; apply Fin.ext; rw [jIdx_succ_val]

 theorem P_jIdx_succ_succ {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P ((jIdx r + 1) + 1) = P ⟨r.val + 2, by have := r.isLt; omega⟩ := by
  congr 1; apply Fin.ext; rw [jIdx_succ_succ_val]

 theorem P_jIdx {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    P (jIdx r) = P ⟨r.val, by have := r.isLt; omega⟩ := rfl

/-- The interior joint at `r` equals the spherical angle of the three consecutive vertices
`P (r.val), P (r.val+1), P (r.val+2)`. -/
 theorem jointAngle_eq_consecutive {n : ℕ} (P : Fin (n + 1) → S2) (r : Fin (n - 1)) :
    jointAngle P r =
      sphAngle (P ⟨r.val, by have := r.isLt; omega⟩) (P ⟨r.val + 1, by have := r.isLt; omega⟩)
        (P ⟨r.val + 2, by have := r.isLt; omega⟩) := rfl



/-- **A flat interior joint is impossible** under the open-joint bound.  If the consecutive triple
`det3 (P r.val) (P (r.val+1)) (P (r.val+2)) = 0` with both joint arcs at the apex short
(`hsau`, `hsav`), the joint at `r` is in `{0, π}`, contradicting `0 < jointAngle P r < π`. -/
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

/-- The two edges adjacent to the apex of interior joint `r` both have a vanishing area form against
`z`, in the nat-indexed orientation needed for the span extraction. -/
 theorem edge_planes_at_apex {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (r : Fin (n - 1)) :
    det3 (P ⟨r.val, by have := r.isLt; omega⟩ : E3) (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
        (z : E3) = 0 ∧
      det3 (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3)
        (P ⟨r.val + 2, by have := r.isLt; omega⟩ : E3) (z : E3) = 0 := by
  have h1 := hallplanes (jIdx r)
  have h2 := hallplanes (jIdx r + 1)
  rw [P_jIdx P r, P_jIdx_succ P r] at h1
  rw [P_jIdx_succ P r, P_jIdx_succ_succ P r] at h2
  exact ⟨h1, h2⟩

/-- **The non-pole apex collapse.**  If the apex `P (r.val+1)` of interior joint `r` is not a pole
(`(P apex : E3) ≠ ± z`), the two adjacent edge planes (both containing the independent pair
`{z, P apex}`) coincide, putting all three consecutive vertices in `span {z, P apex}`, so the
consecutive triple `det3 = 0`. -/
 theorem consecutive_det3_zero_of_nonpole {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
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
  -- `z, apex` are unit and linearly independent (`apex ≠ ± z`).
  have hzu : ‖zz‖ = 1 := z.2
  have hau : ‖apex‖ = 1 := (P _).2
  -- after `set`, `hne : apex ≠ zz` and `hanti : apex ≠ -zz`.
  have hzne : zz ≠ apex := fun h => hne h.symm
  have hzanti : zz ≠ -apex := by
    intro h
    -- `zz = -apex ⟹ apex = -zz`.
    exact hanti (by rw [h]; simp)
  -- `det3 z apex x = 0` from `det3 x apex z = 0` (= `det3 (P r)(P r+1) z`).
  have hdetx : det3 zz apex x = 0 := by
    have hcyc : det3 zz apex x = -det3 x apex zz := by simp only [det3]; ring
    rw [hcyc, he1, neg_zero]
  -- `det3 z apex y = 0` from `det3 apex y z = 0` (= `det3 (P r+1)(P r+2) z`).
  have hdety : det3 zz apex y = 0 := by
    have hcyc : det3 zz apex y = det3 apex y zz := by simp only [det3]; ring
    rw [hcyc, he2]
  -- span extractions over the independent base pair `(z, apex)`.
  obtain ⟨c1, d1, hx'⟩ := lin_indep_span_of_det3_zero hzu hau hzne hzanti hdetx
  obtain ⟨c2, d2, hy'⟩ := lin_indep_span_of_det3_zero hzu hau hzne hzanti hdety
  -- `apex` itself is in `span {z, apex}`.
  have hap' : apex = (0 : ℝ) • zz + (1 : ℝ) • apex := by simp
  -- the consecutive triple is coplanar.
  exact coplanar_triple_det3_zero ⟨c1, d1, hx'.symm⟩ ⟨0, 1, hap'.symm⟩ ⟨c2, d2, hy'.symm⟩

/-- **§4 — the meridian-pencil collapse kernel.**  A closed chain `P : Fin (n+1) → S2` (`2 ≤ n`),
every edge of which is a short arc (`hside`, cyclic incl. wrap), every edge plane of which contains a
common unit axis `z` (`hallplanes`), with all interior joints in `(0, π)` (`hjopen`), is impossible. -/
theorem commonLine_collapse_forces_flat_joint {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hn : 2 ≤ n)
    (hside : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1)))
    (hallplanes : ∀ i : Fin (n + 1), det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    False := by
  classical
  -- The two short joint arcs at the apex of interior joint `r`, in the orientation FFCT21 wants.
  have hshort_apex : ∀ r : Fin (n - 1),
      ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩) (P ⟨r.val, by have := r.isLt; omega⟩) ∧
        ShortArc (P ⟨r.val + 1, by have := r.isLt; omega⟩)
          (P ⟨r.val + 2, by have := r.isLt; omega⟩) := by
    intro r
    have e1 := hside (jIdx r)
    have e2 := hside (jIdx r + 1)
    rw [P_jIdx P r, P_jIdx_succ P r] at e1
    rw [P_jIdx_succ P r, P_jIdx_succ_succ P r] at e2
    -- `e1 : ShortArc (P r) (P r+1)`, `e2 : ShortArc (P r+1) (P r+2)`.  Symmetrize the first.
    exact ⟨e1.symm, e2⟩
  -- Decide whether some interior apex is a non-pole vertex.
  by_cases hsome : ∃ r : Fin (n - 1),
      (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ (z : E3) ∧
        (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) ≠ -(z : E3)
  · -- CASE (a): a non-pole apex.  The collapse gives a flat joint.
    obtain ⟨r, hne, hanti⟩ := hsome
    obtain ⟨hsau, hsav⟩ := hshort_apex r
    have hcol := consecutive_det3_zero_of_nonpole hallplanes r hne hanti
    exact flat_interior_joint_absurd r hsau hsav hcol (hjopen r)
  · -- CASE (b): every interior apex is a pole `P apex = ± z`.
    push_neg at hsome
    -- A uniform pole fact: each interior apex is `+z` or `-z`.
    have hpole : ∀ r : Fin (n - 1),
        (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = (z : E3) ∨
          (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = -(z : E3) := by
      intro r
      by_cases h1 : (P ⟨r.val + 1, by have := r.isLt; omega⟩ : E3) = (z : E3)
      · exact Or.inl h1
      · exact Or.inr (hsome r h1)
    rcases Nat.lt_or_ge 2 n with hn3 | hn2
    · -- `n ≥ 3`: the interior apexes at joints `0` and `1` are vertices `P 1`, `P 2`, ADJACENT.
      -- Both poles ⟹ the edge `(P 1, P 2)` is equal or antipodal ⟹ contradicts `ShortArc`.
      have hp0 := hpole ⟨0, by omega⟩
      have hp1 := hpole ⟨1, by omega⟩
      -- `(⟨0,_⟩).val = 0` and `(⟨1,_⟩).val = 1` hold by `rfl`; the hypotheses are already
      -- about `P ⟨0+1⟩`, `P ⟨1+1⟩`.
      -- `hp0 : P 1 = ± z`, `hp1 : P 2 = ± z`.  Identify the vertices and use the edge `(P 1, P 2)`.
      have hsh := (hshort_apex ⟨0, by omega⟩).2
      -- `hsh : ShortArc (P ⟨0+1⟩) (P ⟨0+2⟩)`; expand into the E3 inequalities.
      have hsh1 : (P ⟨0 + 1, by omega⟩ : E3) ≠ (P ⟨0 + 2, by omega⟩ : E3) := by
        intro he; exact hsh.1 (S2.ext he)
      have hsh2 : (P ⟨0 + 1, by omega⟩ : E3) ≠ -(P ⟨0 + 2, by omega⟩ : E3) := hsh.2
      -- Now `P 1 ∈ {z, -z}` and `P 2 ∈ {z, -z}` give equal or antipodal — both excluded.
      rcases hp0 with hp0z | hp0z <;> rcases hp1 with hp1z | hp1z
      · exact hsh1 (by rw [hp0z, hp1z])
      · exact hsh2 (by rw [hp0z, hp1z, neg_neg])
      · exact hsh2 (by rw [hp0z, hp1z])
      · exact hsh1 (by rw [hp0z, hp1z])
    · -- `n = 2`: a single interior joint `r = 0`, apex `P 1` a pole, collapsed by the WRAP edge.
      have hneq : n = 2 := by omega
      subst hneq
      -- the single interior joint; `(⟨0,_⟩).val = 0` by `rfl`.
      have hp0 := hpole ⟨0, by omega⟩
      -- `hp0 : P 1 = ± z`.  WRAP edge `i = 2`: `det3 (P 2) (P 3) z = 0`, and `P 3 = P 0`.
      -- `(2 : Fin 3) + 1 = 0`.
      have hwrap := hallplanes 2
      have h21 : ((2 : Fin 3) + 1) = (0 : Fin 3) := by decide
      rw [h21] at hwrap
      -- `hwrap : det3 (P 2) (P 0) z = 0`.
      -- The vertices in `jointAngle 0` are `P 0, P 1, P 2` (nat-indexed).
      -- `det3 (P 0) (P 1) (P 2) = ± det3 (P 2) (P 0) z = 0` (cyclic, pole `P 1 = ± z`).
      have hP2 : (P (2 : Fin 3) : E3) = (P ⟨0 + 2, by omega⟩ : E3) := rfl
      have hP0 : (P (0 : Fin 3) : E3) = (P ⟨0, by omega⟩ : E3) := rfl
      set x : E3 := (P ⟨0, by omega⟩ : E3) with hx
      set mid : E3 := (P ⟨0 + 1, by omega⟩ : E3) with hmid
      set y : E3 := (P ⟨0 + 2, by omega⟩ : E3) with hy
      have hmidpole : mid = (z : E3) ∨ mid = -(z : E3) := by
        rw [hmid]; convert hp0 using 3
      have hwrap' : det3 y x (z : E3) = 0 := by
        rw [← hP2, ← hP0]; exact hwrap
      -- `det3 x z y = det3 y x z` (genuine cyclic) `= 0`.
      have hxzy : det3 x (z : E3) y = 0 := by
        have hcyc : det3 x (z : E3) y = det3 y x (z : E3) := by simp only [det3]; ring
        rw [hcyc]; exact hwrap'
      have hcol : det3 x mid y = 0 := by
        rcases hmidpole with hz | hz
        · rw [hz]; exact hxzy
        · -- `det3 x (-z) y = -det3 x z y = 0` (middle-slot linearity).
          rw [hz]
          have hneg : det3 x (-(z : E3)) y = -det3 x (z : E3) y := by
            simp only [det3, PiLp.neg_apply]; ring
          rw [hneg, hxzy, neg_zero]
      obtain ⟨hsau, hsav⟩ := hshort_apex ⟨0, by omega⟩
      -- `(⟨0,_⟩ : Fin (2-1)).val = 0` by rfl, so `hsau, hsav, hcol` already have the right shape.
      exact flat_interior_joint_absurd (⟨0, by omega⟩ : Fin (2 - 1)) hsau hsav hcol
        (hjopen ⟨0, by omega⟩)









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



























/-- The exact oriented tangent datum of the joint at `δ = 0`: `s = ‖u‖‖w‖ · sin γ` (the `+` sign,
opposite to `OpeningDirectionPositive`).  Derived from `joint_axis_support_neg` (so `s > 0`) and the
Pythagorean identity `c² + s² = N²` with `c = N cos γ`. -/
theorem joint_orientedDatum_eq {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    (⟪tangentTo (A (openingAxis k)) (jointPrev A k),
        cross (A (openingAxis k) : E3) (tangentTo (A (openingAxis k)) (jointNext A k))⟫ : ℝ)
      = ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
          * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖
          * Real.sin (jointAngle A k) := by
  set a := A (openingAxis k) with ha
  set p := jointPrev A k with hp
  set q := jointNext A k with hq
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (a : E3) w⟫ with hs
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  -- `γ = jointAngle A k = sphAngle p a q`.
  have hγeq : jointAngle A k = sphAngle p a q := by
    simp only [hp, hq, ha, jointAngle, jointPrev, jointNext, openingAxis]
  set γ : ℝ := jointAngle A k with hγ
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff a p).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff a q).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  -- `c = N cos γ` and `0 ≤ γ ≤ π`.
  have hγ0 : 0 ≤ γ := by rw [hγeq]; exact sphAngle_nonneg _ _ _
  have hγπ : γ ≤ Real.pi := by rw [hγeq]; exact sphAngle_le_pi _ _ _
  have hcEq : c = N * Real.cos γ := by
    have hcos : Real.cos γ = c / N := by
      rw [hγeq, sphAngle, InnerProductGeometry.cos_angle]
    rw [hcos]; field_simp
  -- Pythagoras: `c² + s² = N²`.
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (a : E3)) (u := u) (w := w) a.2
      (tangentTo_orthogonal a p) (tangentTo_orthogonal a q)
    rw [hc, hs, hN]; rw [mul_pow]; linear_combination this
  -- `s² = (N sin γ)²`.
  have hsinγ : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0 hγπ
  have hssq : s ^ 2 = (N * Real.sin γ) ^ 2 := by
    have hsincos : Real.sin γ ^ 2 = 1 - Real.cos γ ^ 2 := by
      have := Real.sin_sq_add_cos_sq γ; linarith
    have hsc : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [hsc, hcEq]
    linear_combination (-(N ^ 2)) * hsincos
  -- `s > 0` from `joint_axis_support_neg`.
  have hspos : 0 < s := by
    have hbridge : s = -sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) := by
      rw [hs, hu, hw, inner_tangent_cross_eq_neg_sOrient]
    rw [hbridge]; linarith [joint_axis_support_neg hA k]
  -- so `s = +(N sin γ)` (the positive root).
  have hge : 0 ≤ N * Real.sin γ := mul_nonneg (le_of_lt hNp) hsinγ
  have hsEq : s = N * Real.sin γ := by
    nlinarith [hssq, hspos, hge, sq_nonneg (s - N * Real.sin γ)]
  rw [hs] at hsEq ⊢
  rw [hsEq, hN]

/-- **Mirrored oriented angle addition (`-θ` opening, `+` orientation).**  Under the orientation
`⟪u, a × w⟫ = +‖u‖‖w‖ sin γ` (the strictly-convex-arm sign) and the branch `0 ≤ γ + θ ≤ π`, opening by
`-θ` *adds* `θ`: `sphAngle p a (rotS2 a (-θ) q) = γ + θ`. -/
theorem sphAngle_axis_rotS2_neg_eq_add_of_oriented {a p q : S2} {θ γ : ℝ}
    (hp : ShortArc a p) (hq : ShortArc a q) (hγ : γ = sphAngle p a q)
    (horient : (⟪tangentTo a p, cross (a : E3) (tangentTo a q)⟫ : ℝ)
      = ‖tangentTo a p‖ * ‖tangentTo a q‖ * Real.sin γ)
    (hbranch0 : 0 ≤ γ + θ) (hbranchπ : γ + θ ≤ Real.pi) :
    sphAngle p a (rotS2 a (-θ) q) = γ + θ := by
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  have hu0 : u ≠ 0 := (tangentTo_ne_zero_iff a p).2 hp
  have hw0 : w ≠ 0 := (tangentTo_ne_zero_iff a q).2 hq
  have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu0
  have hnw : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw0
  have horth : (⟪w, (a : E3)⟫ : ℝ) = 0 := tangentTo_orthogonal a q
  have hangle_uw : γ = InnerProductGeometry.angle u w := by rw [hγ, sphAngle]
  have hinner_uw : (⟪u, w⟫ : ℝ) = Real.cos γ * (‖u‖ * ‖w‖) := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
    rw [← hangle_uw] at h; linarith [h]
  have hLHS : sphAngle p a (rotS2 a (-θ) q) = InnerProductGeometry.angle u (rot (a : E3) (-θ) w) := by
    rw [sphAngle]; congr 1; rw [hw]; exact tangentTo_axis_rotS2 a q (-θ)
  -- `⟪u, rot a (-θ) w⟫ = cos(γ+θ) · (‖u‖‖w‖)`.
  have hinner_rot : (⟪u, rot (a : E3) (-θ) w⟫ : ℝ) = Real.cos (γ + θ) * (‖u‖ * ‖w‖) := by
    rw [inner_rot_tangent (a : E3) (-θ) horth, hinner_uw, horient, Real.cos_neg, Real.sin_neg,
      Real.cos_add]
    ring
  have hnorm_rot : ‖rot (a : E3) (-θ) w‖ = ‖w‖ := norm_rot a.2 (-θ) w
  have hcosLHS : Real.cos (sphAngle p a (rotS2 a (-θ) q)) = Real.cos (γ + θ) := by
    rw [hLHS, InnerProductGeometry.cos_angle, hnorm_rot, hinner_rot]; field_simp
  have hmem1 : sphAngle p a (rotS2 a (-θ) q) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨sphAngle_nonneg _ _ _, sphAngle_le_pi _ _ _⟩
  have hmem2 : γ + θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hbranch0, hbranchπ⟩
  exact Real.injOn_cos.eq_iff hmem1 hmem2 |>.1 hcosLHS

/-- **The opened-by-`-θ` interior joint angle adds `θ`** (on the additive branch).  Instantiates the
mirrored addition at the joint's tangents; the `+` orientation is `joint_orientedDatum_eq`. -/
theorem openedNegJointAngle_eq_add {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    {θ : ℝ} (hθ : 0 ≤ θ) (hbranch : jointAngle A k + θ ≤ Real.pi) :
    openedInteriorJointAngle A k (-θ) = jointAngle A k + θ := by
  have hγ : jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) := by
    simp only [jointAngle, jointPrev, jointNext, openingAxis]
  have hγnn : 0 ≤ jointAngle A k := by rw [hγ]; exact sphAngle_nonneg _ _ _
  rw [openedInteriorJointAngle]
  exact sphAngle_axis_rotS2_neg_eq_add_of_oriented
    (a := A (openingAxis k)) (p := jointPrev A k) (q := jointNext A k)
    hka hkt hγ (joint_orientedDatum_eq hA k hka hkt) (add_nonneg hγnn hθ) hbranch

/-- **The signed joint support under `-θ` is the branch-free sinusoid `N sin (γ + θ)`.**  The joint's
own signed support `sOrient (jointPrev)(A K)(rotS2 (A K) (-θ) (jointNext))` equals
`‖u‖‖w‖ · sin (jointAngle A k + θ)` for **every** `θ` (no branch restriction); its nonnegativity hence
forces `sin (γ + θ) ≥ 0`, the branch control of §4. -/
theorem support_openNeg_eq_sin {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) (θ : ℝ) :
    sOrient (jointPrev A k) (A (openingAxis k))
        (rotS2 (A (openingAxis k)) (-θ) (jointNext A k))
      = ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
          * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖
          * Real.sin (jointAngle A k + θ) := by
  set a := A (openingAxis k) with ha
  set p := jointPrev A k with hp
  set q := jointNext A k with hq
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  -- `sOrient p a (rotS2 a (-θ) q) = ⟪u, a × rot a (-θ) w⟫`.
  have hq' : tangentTo a (rotS2 a (-θ) q) = rot (a : E3) (-θ) w := by rw [hw]; exact tangentTo_axis_rotS2 a q (-θ)
  have hbridge : sOrient p a (rotS2 a (-θ) q)
      = (⟪u, cross (a : E3) (tangentTo a (rotS2 a (-θ) q))⟫ : ℝ) := by
    have h := inner_tangent_cross_eq_neg_sOrient a p (rotS2 a (-θ) q)
    -- `⟪u, a × tangent⟫ = -sOrient a p (rotS2 a (-θ) q)`; and `sOrient p a · = -sOrient a p ·`.
    have hswap : sOrient p a (rotS2 a (-θ) q) = - sOrient a p (rotS2 a (-θ) q) := by
      simp only [sOrient, det3]; ring
    rw [hswap, ← h, hu]
  rw [hbridge, hq']
  -- `a × rot a (-θ) w = rot a (-θ) (a × w)` (rotation commutes with cross by the axis).
  have hcomm : cross (a : E3) (rot (a : E3) (-θ) w) = rot (a : E3) (-θ) (cross (a : E3) w) := by
    rw [rot_cross a.2 (-θ) (a : E3) w, rot_axis a.2]
  rw [hcomm]
  -- `a × w ⟂ a`, so `inner_rot_tangent` applies.
  have horthcw : (⟪cross (a : E3) w, (a : E3)⟫ : ℝ) = 0 := inner_cross_left (a : E3) w
  rw [inner_rot_tangent (a : E3) (-θ) horthcw]
  -- `⟪u, a × w⟫ = N sin γ`,  `⟪u, a × (a × w)⟫ = -⟪u,w⟫ = -N cos γ`.
  have hsval : (⟪u, cross (a : E3) w⟫ : ℝ) = ‖u‖ * ‖w‖ * Real.sin (jointAngle A k) := by
    rw [hu, hw, ha, hp, hq]; exact joint_orientedDatum_eq hA k hka hkt
  -- `a × (a × w) = ⟪a,w⟫ a − ⟪a,a⟫ w = -w` (since `⟪a,w⟫=0`, `‖a‖=1`).
  have haa : (⟪(a : E3), w⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact tangentTo_orthogonal a q
  have haa1 : (⟪(a : E3), (a : E3)⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, a.2]; norm_num
  have hcc : cross (a : E3) (cross (a : E3) w) = -w := by
    rw [cross_cross, haa, haa1]; simp
  have hcval : (⟪u, cross (a : E3) (cross (a : E3) w)⟫ : ℝ) = -(‖u‖ * ‖w‖ * Real.cos (jointAngle A k)) := by
    rw [hcc, inner_neg_right]
    -- `⟪u, w⟫ = N cos γ`.
    have hcosγ : (⟪u, w⟫ : ℝ) = ‖u‖ * ‖w‖ * Real.cos (jointAngle A k) := by
      have hγeq : jointAngle A k = InnerProductGeometry.angle u w := by
        simp only [hu, hw, ha, hp, hq, jointAngle, jointPrev, jointNext, openingAxis, sphAngle]
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
      rw [← hγeq] at h; linear_combination -h
    rw [hcosγ]
  rw [hsval, hcval, Real.cos_neg, Real.sin_neg]
  rw [Real.sin_add]; ring



/-- The non-incident edge–vertex pair monitoring the deficient joint: edge `(k, k+1)`, vertex `k+2`. -/
def jointWitness {n : ℕ} (k : Fin (n - 1)) : NonIncident n :=
  ⟨(⟨k.val, by have := k.isLt; omega⟩, ⟨k.val + 2, by have := k.isLt; omega⟩),
    ⟨by
        intro he
        have h := Fin.val_eq_of_eq he
        simp only [Fin.val_mk] at h; omega,
      by
        intro he
        have hk := k.isLt
        -- the `+1` of the edge first-vertex `⟨k⟩`, computed at `.val`.
        have hadd : ((⟨k.val, by omega⟩ : Fin (n + 1)) + 1).val = k.val + 1 := by
          have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by
            simp only [Fin.val_one']; rw [Nat.mod_eq_of_lt (by omega)]
          rw [Fin.val_add, Fin.val_mk, h1v, Nat.mod_eq_of_lt (by omega)]
        have h := Fin.val_eq_of_eq he
        rw [hadd] at h
        simp only [Fin.val_mk] at h
        omega⟩⟩

/-- The joint-witness support constraint, opened by `-θ`, is exactly the joint's signed support. -/
theorem supportConstraint_jointWitness_neg {n : ℕ} {A : Fin (n + 1) → S2} (k : Fin (n - 1)) (θ : ℝ) :
    supportConstraint A (openingAxis k) (jointWitness k) (-θ)
      = sOrient (jointPrev A k) (A (openingAxis k))
          (rotS2 (A (openingAxis k)) (-θ) (jointNext A k)) := by
  rw [supportConstraint_apply]
  -- the three opened vertices: index k (fixed = jointPrev), k+1 = axis (fixed), k+2 (rotated = jointNext).
  have hk := k.isLt
  have hKval : (openingAxis k).val = k.val + 1 := rfl
  have hv0 : openTail A (openingAxis k) (-θ) ⟨k.val, by omega⟩ = jointPrev A k := by
    rw [openTail_fixed A (openingAxis k) (-θ) (by simp only [openingAxis, Fin.val_mk]; omega)]; rfl
  have he1 : ((jointWitness k).1.1 + 1) = (openingAxis k : Fin (n + 1)) := by
    -- `(jointWitness k).1.1 = ⟨k, _⟩`, so `+1 = ⟨k+1⟩ = openingAxis k`.
    apply Fin.ext
    show (((⟨k.val, by omega⟩ : Fin (n + 1)) + 1).val) = (openingAxis k).val
    rw [Fin.val_add, Fin.val_mk, hKval]
    have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      simp only [Fin.val_one']; rw [Nat.mod_eq_of_lt (by omega)]
    rw [h1v, Nat.mod_eq_of_lt (by omega)]
  have hv1 : openTail A (openingAxis k) (-θ) ((jointWitness k).1.1 + 1) = A (openingAxis k) := by
    rw [he1]; exact openTail_axis A (openingAxis k) (-θ)
  have hv2 : openTail A (openingAxis k) (-θ) ⟨k.val + 2, by omega⟩
      = rotS2 (A (openingAxis k)) (-θ) (jointNext A k) := by
    rw [openTail_rot A (openingAxis k) (-θ) (by simp only [openingAxis, Fin.val_mk]; omega)]; rfl
  show sOrient (openTail A (openingAxis k) (-θ) (jointWitness k).1.1)
      (openTail A (openingAxis k) (-θ) ((jointWitness k).1.1 + 1))
      (openTail A (openingAxis k) (-θ) (jointWitness k).1.2) = _
  rw [hv1]
  show sOrient (openTail A (openingAxis k) (-θ) ⟨k.val, by omega⟩) (A (openingAxis k))
      (openTail A (openingAxis k) (-θ) ⟨k.val + 2, by omega⟩) = _
  rw [hv0, hv2]





























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







/-- Base consecutive distinctness from strict convexity (cyclic, all `i`). -/
theorem base_consecutive_ne {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (i : Fin (n + 1)) : A i ≠ A (i + 1) :=
  (hA.closed_convex.edge_short i).1





































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



/-- **The `∃ h'` sibling of `weakConvex_of_supportStuck_of_hemiPos`.**  From the closure supports
(`≥ 0`), edge distinctness, and a strict open-hemisphere witness `h'` for *some* unit `h'` (rather than
the fixed ambient `h₀`), the opened arm is `WeakConvexSphArm`.  The proof is the original's, reading the
existential witness off `hhem`. -/
theorem weakConvex_of_supportStuckW_of_hemiPos_anyH {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {K : Fin (n + 1)} {δ : ℝ}
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 ≤ sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    (hdist : ∀ i : Fin (n + 1), openTail A K δ i ≠ openTail A K δ (i + 1))
    (hhem : ∃ h' : E3, ‖h'‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h', ((openTail A K δ r : S2) : E3)⟫ : ℝ)) :
    WeakConvexSphArm (openTail A K δ) := by
  obtain ⟨h', hnorm, hhem'⟩ := hhem
  -- verbatim from `weakConvex_of_supportStuck_of_hemiPos`, with `h'` the supplied witness.
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  have hedge : ∀ i : Fin (n + 1), ShortArc (openTail A K δ i) (openTail A K δ (i + 1)) :=
    fun i => shortArc_of_hemisphere (hhem' i) (hhem' (i + 1)) (hdist i)
  refine { two_le := hA.two_le, closed_convex := ?_ }
  refine { three_le := h3
           edge_short := hedge
           edge_support := ?_
           open_hemisphere := ⟨h', hnorm, hhem'⟩ }
  intro i j
  by_cases hji : j = i
  · subst hji; rw [sOrient, det3_self_right]
  · by_cases hji1 : j = i + 1
    · subst hji1; rw [sOrient, det3_self_mid]
    · exact hsupp i j hji hji1



















































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



/-- The **base support monitor**, opened by `-θ`: `θ ↦ sOrient (A 0)(A K)(rotS2 (A K) (-θ)(A last))`,
the signed support of the base triangle `(A 0, A K = axis, A last)` as the endpoint vertex `A last`
rotates by `-θ` about the axis.  Its nonnegativity is exactly the base great-semicircle (cap) condition. -/
def baseCapSupportW {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) : ℝ → ℝ :=
  fun θ => sOrient (A 0) (A (openingAxis k))
    (rotS2 (A (openingAxis k)) (-θ) (A (Fin.last n)))

/-- The base monitor is continuous in `θ` (the rotation `rotS2 (A K) (-θ)(A last)` is continuous and
`sOrient = det3` is continuous). -/
theorem continuous_baseCapSupportW {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    Continuous (baseCapSupportW A k) := by
  show Continuous (fun θ : ℝ =>
    det3 (A 0 : E3) (A (openingAxis k) : E3)
      ((rotS2 (A (openingAxis k)) (-θ) (A (Fin.last n)) : S2) : E3))
  simp only [rotS2_coe, det3]
  -- the first two vertices are constant; the third rotates (`continuous_rot ∘ neg`, per coordinate).
  have ha : ∀ c, Continuous (fun _ : ℝ => (A 0 : E3) c) := fun c => continuous_const
  have hb : ∀ c, Continuous (fun _ : ℝ => (A (openingAxis k) : E3) c) := fun c => continuous_const
  have hl : ∀ c, Continuous
      (fun θ : ℝ => (rot (A (openingAxis k) : E3) (-θ) (A (Fin.last n) : E3)) c) := fun c =>
    (continuous_rot_coord (A (openingAxis k) : E3) (A (Fin.last n) : E3) c).comp continuous_neg
  exact
    (((ha 0).mul (((hb 1).mul (hl 2)).sub ((hb 2).mul (hl 1)))).sub
      ((ha 1).mul (((hb 0).mul (hl 2)).sub ((hb 2).mul (hl 0))))).add
      ((ha 2).mul (((hb 0).mul (hl 1)).sub ((hb 1).mul (hl 0))))



















/-- **The base oriented tangent datum** `s = +‖u‖‖w‖ · sin γbase` (the `+` orientation).  Here
`a := A K`, `u := tangentTo (A K)(A 0)`, `w := tangentTo (A K)(A last)`, `γbase := sphAngle (A 0)(A K)(A last)`.
Derived (mirroring `joint_orientedDatum_eq`) from the **strict** base support
`0 < sOrient (A 0)(A K)(A last)` (`cut_diagonal_supports`), so the datum `s = -sOrient (A K)(A 0)(A last) > 0`,
and Pythagoras `c² + s² = N²` pins it to the positive root `N sin γbase`. -/
theorem base_orientedDatum_eq {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hka : ShortArc (A (openingAxis k)) (A 0))
    (hkt : ShortArc (A (openingAxis k)) (A (Fin.last n))) :
    (⟪tangentTo (A (openingAxis k)) (A 0),
        cross (A (openingAxis k) : E3) (tangentTo (A (openingAxis k)) (A (Fin.last n)))⟫ : ℝ)
      = ‖tangentTo (A (openingAxis k)) (A 0)‖
          * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖
          * Real.sin (sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n))) := by
  set a := A (openingAxis k) with ha
  set p := A 0 with hp
  set q := A (Fin.last n) with hq
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (a : E3) w⟫ with hs
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  set γ : ℝ := sphAngle p a q with hγ
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff a p).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff a q).2 hkt
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
    have := tangentPlane_pythag (k := (a : E3)) (u := u) (w := w) a.2
      (tangentTo_orthogonal a p) (tangentTo_orthogonal a q)
    rw [hc, hs, hN]; rw [mul_pow]; linear_combination this
  have hsinγ : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0 hγπ
  have hssq : s ^ 2 = (N * Real.sin γ) ^ 2 := by
    have hsincos : Real.sin γ ^ 2 = 1 - Real.cos γ ^ 2 := by
      have := Real.sin_sq_add_cos_sq γ; linarith
    have hsc : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [hsc, hcEq]
    linear_combination (-(N ^ 2)) * hsincos
  -- `s > 0` from the strict positive base support `0 < sOrient (A 0)(A K)(A last)`.
  have hspos : 0 < s := by
    obtain ⟨hK0, hKn⟩ := openingAxis_interior k
    haveI : NeZero (n + 1) := ⟨by omega⟩
    have h0K : (0 : Fin (n + 1)) < openingAxis k := by rw [Fin.lt_def, Fin.val_zero]; omega
    have hKl : openingAxis k < Fin.last n := by rw [Fin.lt_def, Fin.val_last]; omega
    have hdiag : 0 < sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) :=
      cut_diagonal_supports hA.closed_convex h0K hKl
    -- `s = ⟪u, a × w⟫ = -sOrient a p q = -sOrient (A K)(A 0)(A last) = sOrient (A 0)(A K)(A last) > 0`.
    have hbridge : s = -sOrient a p q := by
      rw [hs, hu, hw, inner_tangent_cross_eq_neg_sOrient]
    have hswap : sOrient a p q = -sOrient p a q := by
      have := sOrient_swap p a q  -- sOrient p q a = -sOrient p a q ; need swap first two
      simp only [sOrient, det3] at this ⊢; ring
    rw [hbridge, hswap]
    -- `sOrient p a q = sOrient (A 0)(A K)(A last)`.
    have hpaq : sOrient p a q = sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) := by
      rw [hp, ha, hq]
    rw [hpaq]; linarith
  have hge : 0 ≤ N * Real.sin γ := mul_nonneg (le_of_lt hNp) hsinγ
  have hsEq : s = N * Real.sin γ := by
    nlinarith [hssq, hspos, hge, sq_nonneg (s - N * Real.sin γ)]
  rw [hs] at hsEq ⊢
  rw [hsEq, hN]

/-- **The base support under `-θ` is the branch-free sinusoid `N · sin (γbase + θ)`.**  Mirror of
`ZinanFFCT37.support_openNeg_eq_sin`, with the base triple and the base oriented datum
`base_orientedDatum_eq`.  Holds for **every** `θ` (no branch restriction). -/
theorem baseSupport_openNeg_eq_sin {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hka : ShortArc (A (openingAxis k)) (A 0))
    (hkt : ShortArc (A (openingAxis k)) (A (Fin.last n))) (θ : ℝ) :
    baseCapSupportW A k θ
      = ‖tangentTo (A (openingAxis k)) (A 0)‖
          * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖
          * Real.sin (sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) + θ) := by
  set a := A (openingAxis k) with ha
  set p := A 0 with hp
  set q := A (Fin.last n) with hq
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  show sOrient p a (rotS2 a (-θ) q)
    = ‖u‖ * ‖w‖ * Real.sin (sphAngle p a q + θ)
  have hq' : tangentTo a (rotS2 a (-θ) q) = rot (a : E3) (-θ) w := by
    rw [hw]; exact tangentTo_axis_rotS2 a q (-θ)
  have hbridge : sOrient p a (rotS2 a (-θ) q)
      = (⟪u, cross (a : E3) (tangentTo a (rotS2 a (-θ) q))⟫ : ℝ) := by
    have h := inner_tangent_cross_eq_neg_sOrient a p (rotS2 a (-θ) q)
    have hswap : sOrient p a (rotS2 a (-θ) q) = - sOrient a p (rotS2 a (-θ) q) := by
      simp only [sOrient, det3]; ring
    rw [hswap, ← h, hu]
  rw [hbridge, hq']
  have hcomm : cross (a : E3) (rot (a : E3) (-θ) w) = rot (a : E3) (-θ) (cross (a : E3) w) := by
    rw [rot_cross a.2 (-θ) (a : E3) w, rot_axis a.2]
  rw [hcomm]
  have horthcw : (⟪cross (a : E3) w, (a : E3)⟫ : ℝ) = 0 := inner_cross_left (a : E3) w
  rw [inner_rot_tangent (a : E3) (-θ) horthcw]
  -- `⟪u, a × w⟫ = N sin γ` (base oriented datum); `⟪u, a × (a × w)⟫ = -N cos γ`.
  have hsval : (⟪u, cross (a : E3) w⟫ : ℝ)
      = ‖u‖ * ‖w‖ * Real.sin (sphAngle p a q) := by
    rw [hu, hw, ha, hp, hq]; exact base_orientedDatum_eq hA k hka hkt
  have haa : (⟪(a : E3), w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact tangentTo_orthogonal a q
  have haa1 : (⟪(a : E3), (a : E3)⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, a.2]; norm_num
  have hcc : cross (a : E3) (cross (a : E3) w) = -w := by
    rw [cross_cross, haa, haa1]; simp
  have hcval : (⟪u, cross (a : E3) (cross (a : E3) w)⟫ : ℝ)
      = -(‖u‖ * ‖w‖ * Real.cos (sphAngle p a q)) := by
    rw [hcc, inner_neg_right]
    have hcosγ : (⟪u, w⟫ : ℝ) = ‖u‖ * ‖w‖ * Real.cos (sphAngle p a q) := by
      have hγeq : sphAngle p a q = InnerProductGeometry.angle u w := by
        rw [hu, hw, sphAngle]
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
      rw [← hγeq] at h; linear_combination -h
    rw [hcosγ]
  rw [hsval, hcval, Real.cos_neg, Real.sin_neg]
  rw [Real.sin_add]; ring



/-- **The strict base nondegeneracy** `γbase < π`.  From the strict convex base support
`0 < sOrient (A 0)(A K)(A last) = det3 …` via `sphAngle_lt_pi_of_det3_ne`. -/
theorem base_sphAngle_lt_pi {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) :
    sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) < Real.pi := by
  obtain ⟨hK0, hKn⟩ := openingAxis_interior k
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have h0K : (0 : Fin (n + 1)) < openingAxis k := by rw [Fin.lt_def, Fin.val_zero]; omega
  have hKl : openingAxis k < Fin.last n := by rw [Fin.lt_def, Fin.val_last]; omega
  have hdiag : 0 < sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) :=
    cut_diagonal_supports hA.closed_convex h0K hKl
  refine sphAngle_lt_pi_of_det3_ne _ _ _ ?_
  intro hz
  rw [sOrient] at hdiag
  rw [hz] at hdiag; exact lt_irrefl 0 hdiag







































































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



/-- `det3` cyclic rotation `det3 a b c = det3 c a b` (the even permutation, two transpositions).
Pure coordinate algebra. -/
theorem det3_cyc_rot (a b c : E3) : det3 a b c = det3 c a b := by
  simp only [det3]; ring

/-- The `sOrient` cyclic rotation `sOrient a b c = sOrient c a b` (the even permutation), inherited
from `det3_cyc_rot` through `sOrient = det3 ∘ coe`. -/
theorem sOrient_cyc_rot (a b c : S2) : sOrient a b c = sOrient c a b := by
  simp only [sOrient]; exact det3_cyc_rot _ _ _

/-- The wraparound index identity `Fin.last n + 1 = 0` in `Fin (n + 1)` (so the closed polygon's
last edge is `(last, 0)`). -/
theorem lastAddOne_eq_zero (n : ℕ) : (Fin.last n + 1 : Fin (n + 1)) = 0 := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_last, Fin.val_zero, Fin.val_one']
  rcases n with _ | m
  · rfl
  · rw [Nat.mod_eq_of_lt (show 1 < m + 1 + 1 by omega)]
    simp [Nat.mod_self]



/-- **Base-stuck = opened diagonal zero.**  `baseCapSupportW A k δ*_WB` is, by definition, the
oriented base support with the endpoint vertex opened by `-δ*_WB`; since `openTail A K (-δ*_WB)`
fixes `0` and `K` (both `≤ K`) and rotates `last` (`K.val < n`), it equals the diagonal support
`sOrient (A'_WB 0)(A'_WB K)(A'_WB last)` of the opened arm. -/
theorem baseStuck_eq_openedDiagonal {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ) :
    baseCapSupportW A k δ
      = sOrient (openTail A (openingAxis k) (-δ) 0)
          (openTail A (openingAxis k) (-δ) (openingAxis k))
          (openTail A (openingAxis k) (-δ) (Fin.last n)) := by
  obtain ⟨hK1, hKn⟩ := openingAxis_interior k
  -- `A'_WB 0 = A 0`, `A'_WB K = A K`, `A'_WB last = rotS2 (A K)(-δ)(A last)`.
  rw [openTail_zero, openTail_axis,
      openTail_rot A (openingAxis k) (-δ) (r := Fin.last n) (by rw [Fin.val_last]; exact hKn)]
  rfl



/-- **(Brick 1, the cyclic-identity bridge.)**  In the opened closed polygon `A'_WB := openTail A K
(-δ)`, a zero diagonal support at the triple `(0, K, last)` is **literally** a zero non-incident
edge support at the wraparound pair `(i, j) = (Fin.last n, K)`:
`i = last`, `i + 1 = last + 1 = 0` (Fin wrap), and the support
`sOrient (A'_WB last)(A'_WB 0)(A'_WB K)` equals the diagonal by `det3` cyclic rotation.  The two
`NonIncident` side conditions `j ≠ i` (`K ≠ last`) and `j ≠ i + 1` (`K ≠ 0`) hold because `K` is an
interior axis (`1 ≤ K.val < n`). -/
theorem baseDiagonal_zero_is_wrapEdgeSupport_zero {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1))
    (δ : ℝ)
    (hdiag : sOrient (openTail A (openingAxis k) (-δ) 0)
        (openTail A (openingAxis k) (-δ) (openingAxis k))
        (openTail A (openingAxis k) (-δ) (Fin.last n)) = 0) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) (-δ) i)
        (openTail A (openingAxis k) (-δ) (i + 1))
        (openTail A (openingAxis k) (-δ) j) = 0 := by
  obtain ⟨hK1, hKn⟩ := openingAxis_interior k
  refine ⟨Fin.last n, openingAxis k, ?_, ?_, ?_⟩
  · -- `K ≠ last`: `K.val < n = (last).val`.
    intro h
    rw [h, Fin.val_last] at hKn
    exact lt_irrefl n hKn
  · -- `K ≠ last + 1 = 0`: `1 ≤ K.val`.
    rw [lastAddOne_eq_zero]
    intro h
    rw [h, Fin.val_zero] at hK1
    exact absurd hK1 (by norm_num)
  · -- the wrap-edge support `sOrient (A'_WB last)(A'_WB 0)(A'_WB K)` = the diagonal (cyclic).
    rw [lastAddOne_eq_zero]
    -- goal: `sOrient (A'_WB last)(A'_WB 0)(A'_WB K) = 0`; `hdiag` is the diagonal `(0,K,last)`.
    -- `sOrient (0)(K)(last) = sOrient (last)(0)(K)` (cyclic, a=0,b=K,c=last).
    rw [sOrient_cyc_rot] at hdiag
    exact hdiag















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


