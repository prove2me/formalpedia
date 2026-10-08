-- Prove2me | Definitions.Def_P2MAssembly_Chapter13V2_Part5
-- name    : P2MAssembly_Chapter13V2_Part5
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T20:47:05.619875+00:00
-- url     : https://prove2.me/theorems/a0b78d1f-3df0-41a5-b727-e20c064bbee3
-- title:
--   Marked-map reductions and three-dimensional vertex stars
-- statement:
--   This part contains near-triangulation, chord-side and component-counting interfaces, marked-sphere reductions, and spherical subarc comparisons. A vertex star has an apex and at least three neighbors with nonzero raw directions in a common open hemisphere; determinant support is nonnegative and strict at nonincident directions. Its internal dihedral angle is the angle of outer raw vectors projected perpendicular to the middle raw vector. The intermediate ConvexPolytopeRealization interface records two star families, a common signed map, equal link sides and closing chords, and compatibility conditions used to combine the geometry with sign counting. These fields are an intermediate interface, not extra arguments of the final headline.
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

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A near-triangulation is a simple sphere map with one distinguished simple
outer boundary cycle of length at least three; every other face has length
three. -/
structure NearTriangulation (M : CombMap D) where
  sphere : M.IsSphereMap
  simpleGraph : M.IsSimpleGraph
  outerFace : M.Face
  outerCycle : BoundaryCycle M outerFace
  outer_simple : outerCycle.VertexNodup
  outer_len : 3 ≤ outerCycle.length
  inner_tri : ∀ f : M.Face, f ≠ outerFace → M.faceLen f = 3

@[simp]
lemma dartFace_phi (M : CombMap D) (d : D) :
    M.dartFace (M.φ d) = M.dartFace d := by
  unfold dartFace
  exact Quotient.sound ⟨-1, by simp⟩







lemma faceLen_dartFace_eq_card_support_cycleOf (M : CombMap D) {d : D}
    (hφ : M.φ d ≠ d) :
    M.faceLen (M.dartFace d) = (M.φ.cycleOf d).support.card := by
  have hset :
      (Finset.univ.filter
          (fun x => Quotient.mk (cycleSetoid M.φ) x = M.dartFace d))
        = (M.φ.cycleOf d).support := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dartFace,
      Equiv.Perm.mem_support_cycleOf_iff' hφ, Quotient.eq]
    exact Equiv.Perm.sameCycle_comm
  simpa [faceLen] using congrArg Finset.card hset



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

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {α : Type*} [DecidableEq α]

namespace CombMap

open ProofsInTheBook.PlanarMap.CombMap



/--
The Thomassen list hypotheses for a near-triangulation `M` with a distinguished
*precolored boundary edge* `s(p, q)`.

The two endpoints `p, q` are adjacent on the outer cycle, precolored by singleton
lists `{cp}`, `{cq}` with distinct colors; every other boundary vertex has a list
of size at least `3`; every interior (non-boundary) vertex has a list of size at
least `5`.
-/
structure ThomassenLists {M : CombMap D} (hNT : NearTriangulation M)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) : Prop where
  /-- `p` is on the outer boundary. -/
  p_boundary : hNT.outerCycle.IsBoundaryVertex p
  /-- `q` is on the outer boundary. -/
  q_boundary : hNT.outerCycle.IsBoundaryVertex q
  /-- `p` and `q` are joined by an outer-boundary edge: a precolored edge. -/
  pq_boundary_edge : hNT.outerCycle.IsBoundaryEdge s(p, q)
  /-- The two precolored endpoints carry distinct colors. -/
  colors_ne : cp ≠ cq
  /-- `p` is precolored to the singleton `{cp}`. -/
  list_p : L p = {cp}
  /-- `q` is precolored to the singleton `{cq}`. -/
  list_q : L q = {cq}
  /-- Every other boundary vertex has list size at least three. -/
  boundary_ge_three : ∀ v : M.Vertex,
    hNT.outerCycle.IsBoundaryVertex v → v ≠ p → v ≠ q → 3 ≤ (L v).card
  /-- Every interior (non-boundary) vertex has list size at least five. -/
  interior_ge_five : ∀ v : M.Vertex,
    ¬ hNT.outerCycle.IsBoundaryVertex v → 5 ≤ (L v).card

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



variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}

/-- The reconstruction datum for ONE side of a chord split, relative to a side
region `s ⊆ M.Vertex` and side lists.  `Dₛ` is the side dart type (in the surgery,
`keptSideᵢ ⊕ Fin 2`).

The structure isolates the Jordan/Euler outputs that the combinatorial-map layer
cannot synthesize, exactly as `FanSurgeryReconstruction` does for the chordless
branch:

* `N` — the side as a near-triangulation (carries `IsSphereMap`/genus-0);
* `ι` — the side-vertex-to-`M` correspondence, injective and adjacency-reflecting
  *onto* the region `s` (`ι_surj`), so it is a graph isomorphism `N ≃ M⟦s⟧`;
* `ι_lists` — the side near-triangulation's lists are the pullback of `L` along
  `ι`, so a list coloring of `N` transports to a region coloring of `M`;
* `smaller` — strict vertex decrease, the recursion fuel.

`Lₛ` and the precolored data (`pₛ qₛ cpₛ cqₛ`) are the side's Thomassen inputs. -/
structure ChordSideReconstruction (hNT : NearTriangulation M)
    (s : Set M.Vertex) (L : M.Vertex → Finset α) where
  /-- The side dart type. -/
  Dₛ : Type u
  /-- Side dart type is a fintype. -/
  [fintypeDₛ : Fintype Dₛ]
  /-- Side dart type has decidable equality. -/
  [decEqDₛ : DecidableEq Dₛ]
  /-- The side combinatorial map. -/
  N : CombMap Dₛ
  /-- The side is a near-triangulation (carries `IsSphereMap`: genus-0/Euler-2). -/
  hN : NearTriangulation N
  /-- The side-vertex-to-`M`-vertex correspondence. -/
  ι : N.Vertex → M.Vertex
  /-- The correspondence is injective. -/
  ι_inj : Function.Injective ι
  /-- The correspondence lands in the region. -/
  ι_mem : ∀ x : N.Vertex, ι x ∈ s
  /-- The correspondence is *surjective onto the region* (the side-vertex
  classification: every region vertex is a side vertex). -/
  ι_surj : ∀ ⦃w : M.Vertex⦄, w ∈ s → ∃ x : N.Vertex, ι x = w
  /-- The correspondence carries side adjacency to `M`-adjacency (graph hom). -/
  ι_adj : ∀ ⦃x y : N.Vertex⦄, N.toSimpleGraph.Adj x y →
    M.toSimpleGraph.Adj (ι x) (ι y)
  /-- The correspondence *reflects* `M`-adjacency on the region (graph iso onto the
  induced subgraph): two side vertices adjacent in `M` are adjacent in `N`. -/
  ι_adj_reflect : ∀ ⦃x y : N.Vertex⦄, M.toSimpleGraph.Adj (ι x) (ι y) →
    N.toSimpleGraph.Adj x y
  /-- The side lists are the pullback of `L` along `ι`. -/
  Lₛ : N.Vertex → Finset α
  /-- The pullback identity for the side lists. -/
  Lₛ_eq : ∀ x : N.Vertex, Lₛ x = L (ι x)
  /-- The side's precolored boundary edge. -/
  pₛ : N.Vertex
  /-- The side's precolored boundary edge. -/
  qₛ : N.Vertex
  /-- The side's precolors. -/
  cpₛ : α
  /-- The side's precolors. -/
  cqₛ : α
  /-- The side near-triangulation carries the Thomassen list hypotheses, so the
  Thomassen induction can recurse on it.  (This is part of the list transport the
  classification produces alongside the correspondence.) -/
  hLₛ : ThomassenLists hN pₛ qₛ Lₛ cpₛ cqₛ
  /-- Strict vertex decrease (the recursion fuel). -/
  smaller : N.V < M.V

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

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def numCycles (p : Equiv.Perm D) : ℕ := by
  classical
  exact Fintype.card (Quotient (SameCycle.setoid p))

namespace PermTranspositionCycleCount

open scoped Finset

def mergeRel (p : Equiv.Perm D) (a b x y : D) : Prop :=
  p.SameCycle x y ∨
    (p.SameCycle x a ∧ p.SameCycle y b) ∨
      (p.SameCycle x b ∧ p.SameCycle y a)























noncomputable def orbitEquivFixedOrCycles (p : Equiv.Perm D) :
    Quotient (SameCycle.setoid p) ≃ Function.fixedPoints p ⊕ p.cycleFactorsFinset := by
  classical
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left
      right_inv := ?right }
  · refine Quotient.lift ?_ ?_
    · intro x
      by_cases hx : p x = x
      · exact Sum.inl ⟨x, by simpa [Function.mem_fixedPoints_iff] using hx⟩
      · exact Sum.inr ⟨p.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩
    · intro x y hxy
      change p.SameCycle x y at hxy
      by_cases hx : p x = x
      · have hy : p y = y := (hxy.apply_eq_self_iff).mp hx
        have hxy' : x = y := hxy.eq_of_left hx
        subst hxy'
        simp [hx, hy]
      · have hy : p y ≠ y := fun hy => hx ((hxy.apply_eq_self_iff).mpr hy)
        simp [hx, hy]
        exact hxy.cycleOf_eq
  · intro s
    rcases s with fp | c
    · exact Quotient.mk (SameCycle.setoid p) fp.1
    · let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      exact Quotient.mk (SameCycle.setoid p) y
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    by_cases hx : p x = x
    · simp [hx, Function.mem_fixedPoints_iff]
    · dsimp
      simp [hx]
      let c : p.cycleFactorsFinset :=
        ⟨p.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩
      let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hy : y ∈ (p.cycleOf x).support :=
        Classical.choose_spec
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hy' : p.SameCycle x y := by
        have := (mem_support_cycleOf_iff (f := p) (x := x) (y := y)).mp hy
        exact this.1
      exact Quotient.sound hy'.symm
  · intro s
    rcases s with fp | c
    · have hfp : p fp.1 = fp.1 := Function.mem_fixedPoints_iff.mp fp.2
      simp [hfp]
    · let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hyc : y ∈ (c : Equiv.Perm D).support :=
        Classical.choose_spec
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hyp : y ∈ p.support := mem_cycleFactorsFinset_support_le c.2 hyc
      have hy : p y ≠ y := mem_support.mp hyp
      have hcy : c.1 = p.cycleOf y := cycle_is_cycleOf hyc c.2
      dsimp
      rw [dif_neg hy]
      exact congrArg (fun e : p.cycleFactorsFinset => Sum.inr e) (Subtype.ext hcy.symm)















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

def compSetoid (r : V → V → Prop) : Setoid V :=
  ⟨Relation.EqvGen r, Relation.EqvGen.is_equivalence r⟩

noncomputable def numComp (r : V → V → Prop) : ℕ :=
  Nat.card (Quotient (compSetoid r))

def addEdge (r : V → V → Prop) (a b : V) : V → V → Prop :=
  fun x y => r x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

 def pairRel {α : Type u} (a b : α) (x y : α) : Prop :=
  x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

 theorem pairRel_refl {α : Type u} (a b : α) (x : α) :
    pairRel a b x x := by
  exact Or.inl rfl

 theorem pairRel_symm {α : Type u} (a b : α) {x y : α} :
    pairRel a b x y → pairRel a b y x := by
  intro h
  rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

 theorem pairRel_trans {α : Type u} (a b : α) {x y z : α} :
    pairRel a b x y → pairRel a b y z → pairRel a b x z := by
  intro hxy hyz
  rcases hxy with hEq | hAB | hBA
  · subst y
    exact hyz
  · rcases hAB with ⟨rfl, rfl⟩
    rcases hyz with hEq | hAB' | hBA'
    · subst z
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hAB' with ⟨_, hz⟩
      subst z
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hBA' with ⟨_, hz⟩
      subst z
      exact Or.inl rfl
  · rcases hBA with ⟨rfl, rfl⟩
    rcases hyz with hEq | hAB' | hBA'
    · subst z
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · rcases hAB' with ⟨_, hz⟩
      subst z
      exact Or.inl rfl
    · rcases hBA' with ⟨_, hz⟩
      subst z
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)

 def pairSetoid {α : Type u} (a b : α) : Setoid α where
  r := pairRel a b
  iseqv :=
    ⟨pairRel_refl a b, fun h => pairRel_symm a b h,
      fun h₁ h₂ => pairRel_trans a b h₁ h₂⟩























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











/-- The dart-incidence relation of a raw pair `(σ, α)`: two darts are adjacent if
they share a `σ`-orbit (same vertex) or are joined by the `α`-edge. -/
def dartStepRel (σ α : Equiv.Perm D) (a b : D) : Prop :=
  σ.SameCycle a b ∨ b = α a











/-- Number of `α`-transpositions. -/
noncomputable def Ehalf (α : Equiv.Perm D) : ℕ := (Equiv.Perm.support α).card / 2



























/-- Component count of the raw pair `(σ, α)`. -/
noncomputable def numComponents (σ α : Equiv.Perm D) : ℕ :=
  _root_.numComp (dartStepRel σ α)



/-- Genus slack `2c - V + Ehalf - F` of a raw involution pair.  It is `≥ 0`; for a
connected fixed-point-free map this yields `χ ≤ 2`. -/
noncomputable def genusSlack (σ α : Equiv.Perm D) : ℤ :=
  2 * (numComponents σ α : ℤ) - (numCycles σ : ℤ) + (Ehalf α : ℤ)
    - (numCycles (σ * α) : ℤ)























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







/-- `α'` is an **edge-deletion sub-involution** of `α`: an involution that agrees with `α` on
its own support (so its edge set is a subset of `α`'s edge set). -/
def SubInvolution (α α' : Equiv.Perm D) : Prop :=
  α' * α' = 1 ∧ ∀ x, α' x ≠ x → α' x = α x













section OrbitSplit

variable (p : Equiv.Perm D) (S : Finset D)

open scoped Classical

/-- A `p`-orbit is **deleted** if all its darts lie in `S`. -/
def DeletedOrbit (q : Quotient (cycleSetoid p)) : Prop :=
  ∀ x : D, Quotient.mk (cycleSetoid p) x = q → x ∈ S

/-- The kept subtype's filtered orbit quotient, as `p`-orbits via the `SameCycle` coincidence. -/
noncomputable def keptToFull :
    Quotient (cycleSetoid (Equiv.Perm.deleteSet p S)) → Quotient (cycleSetoid p) :=
  Quotient.lift (fun x => Quotient.mk (cycleSetoid p) (x.1 : D)) (by
    intro x y hxy
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_deleteSet_iff p S x y).1 hxy)







/-- The number of **deleted** `p`-orbits (orbits entirely inside `S`). -/
noncomputable def numDeletedOrbits : ℕ :=
  Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q}



end OrbitSplit





section RawRestrict

variable (M : CombMap D) (Del : Finset D)

open scoped Classical

/-- The raw restricted function: identity on deleted darts, `M.α` elsewhere. -/
noncomputable def rawAlphaFun : D → D := fun d => if d ∈ Del then d else M.α d

/-- `rawAlphaFun` is an involution (uses `α`-closedness of `Del`). -/
lemma rawAlphaFun_involutive (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) :
    Function.Involutive (rawAlphaFun M Del) := by
  classical
  intro d
  unfold rawAlphaFun
  by_cases hd : d ∈ Del
  · simp [hd]
  · have hαd : M.α d ∉ Del := by
      intro h
      apply hd
      have := hclosed _ h
      rwa [M.alpha_alpha] at this
    simp [hd, hαd, M.alpha_alpha]

/-- The **raw restricted involution**: fixes every deleted dart, equals `M.α` on kept darts. -/
noncomputable def rawAlpha (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) : Equiv.Perm D :=
  Function.Involutive.toPerm (rawAlphaFun M Del) (rawAlphaFun_involutive M Del hclosed)

@[simp] lemma rawAlpha_apply (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) (d : D) :
    rawAlpha M Del hclosed d = if d ∈ Del then d else M.α d := rfl





/-- `rawAlpha` equals `M.α` on kept darts. -/
lemma rawAlpha_eq_alpha_of_notMem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {d : D}
    (hd : d ∉ Del) : rawAlpha M Del hclosed d = M.α d := by simp [rawAlpha_apply, hd]





/-- Abbreviation: the kept combinatorial map's face permutation is
`(deleteSet M.σ Del) * (M.α.subtypePerm)`. -/
noncomputable def keptFacePerm (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) : Equiv.Perm {d : D // d ∉ Del} :=
  (Equiv.Perm.deleteSet M.σ Del) * (M.α.subtypePerm (fun d => by
    rw [← hsub d]))

















variable (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
  (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)

open scoped Classical

/-- The kept edge involution: `M.α` restricted to the kept subtype. -/
noncomputable def keptAlpha : Equiv.Perm {d : D // d ∉ Del} :=
  M.α.subtypePerm (p := fun d => d ∉ Del) (fun d => by
    constructor
    · intro hd hc; exact hd ((hsub d).1 hc)
    · intro hd hc; exact hd ((hsub d).2 hc))

@[simp] lemma keptAlpha_apply_coe (d : {d : D // d ∉ Del}) :
    (keptAlpha M Del hsub d : D) = M.α d.1 := rfl

lemma keptAlpha_invol : keptAlpha M Del hsub * keptAlpha M Del hsub = 1 := by
  ext z
  simp only [Equiv.Perm.coe_mul, Equiv.Perm.coe_one, Function.comp_apply, id_eq,
    keptAlpha_apply_coe]
  exact M.alpha_alpha z.1

/-- The kept combinatorial map's dart-step relation, on the kept subtype. -/
noncomputable def keptStepRel : {d : D // d ∉ Del} → {d : D // d ∉ Del} → Prop :=
  dartStepRel (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub)

/-- **A kept dart-step lifts to a raw dart-step on the underlying darts.** -/
lemma keptStepRel_imp_raw {x y : {d : D // d ∉ Del}}
    (h : keptStepRel M Del hsub x y) :
    dartStepRel M.σ (rawAlpha M Del hclosed) x.1 y.1 := by
  classical
  rcases h with hσ | hα
  · -- same `deleteSet M.σ`-cycle ⇒ same `M.σ`-cycle on coercions.
    exact Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del x y).1 hσ)
  · -- α-edge: `y = (M.α.subtypePerm) x`, so `y.1 = M.α x.1 = rawAlpha x.1` (x kept).
    refine Or.inr ?_
    have hxval : (rawAlpha M Del hclosed) x.1 = M.α x.1 :=
      rawAlpha_eq_alpha_of_notMem M Del hclosed x.2
    rw [hxval]
    have := congrArg Subtype.val hα
    simpa using this



/-- `EqvGen` of the kept dart-step relation lifts to `EqvGen` of the raw relation. -/
lemma eqvGen_keptStepRel_imp_raw {x y : {d : D // d ∉ Del}}
    (h : Relation.EqvGen (keptStepRel M Del hsub) x y) :
    Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1 := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (keptStepRel_imp_raw M Del hclosed hsub hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2







/-- The lifted map `⟦x⟧_kept ↦ ⟦x.1⟧_raw` of component quotients. -/
noncomputable def keptCompToRaw :
    Quotient (_root_.compSetoid (keptStepRel M Del hsub))
      → Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) :=
  Quotient.lift (fun x => Quotient.mk _ (x.1 : D)) (by
    intro x y hxy
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1
    exact eqvGen_keptStepRel_imp_raw M Del hclosed hsub hxy)







/-- A raw component is **deleted** if all its darts lie in `Del`. -/
def DeletedComp (q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :
    Prop :=
  ∀ x : D, Quotient.mk _ x = q → x ∈ Del



/-- The number of deleted raw components. -/
noncomputable def numDeletedComp : ℕ :=
  Fintype.card {q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))
    // DeletedComp M Del hclosed q}











































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

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Embed a strict sign into `EdgeSign`. -/
def strictToEdge : StrictEdgeSign → EdgeSign
  | StrictEdgeSign.plus => EdgeSign.plus
  | StrictEdgeSign.minus => EdgeSign.minus









end StrictBridge



section ActiveComponent

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The degree of a face (`φ`-orbit): the number of darts on its boundary walk. -/
def faceDeg (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) : ℕ :=
  (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card











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

/-- The kept (active sub-)combinatorial map on the surviving darts `{d ∉ Del}`. -/
noncomputable def keptMap (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) : CombMap {d : D // d ∉ Del} where
  α := keptAlpha M Del hsub
  σ := Equiv.Perm.deleteSet M.σ Del
  α_invol := keptAlpha_invol M Del hsub
  α_no_fixed := by
    intro d hd
    apply M.α_no_fixed d.1
    have := congrArg Subtype.val hd
    rwa [keptAlpha_apply_coe] at this











/-- A nonzero edge sign as a strict sign. -/
def edgeToStrict : EdgeSign → StrictEdgeSign
  | EdgeSign.plus => StrictEdgeSign.plus
  | EdgeSign.minus => StrictEdgeSign.minus
  | EdgeSign.zero => StrictEdgeSign.plus  -- unreachable on active darts



/-- The strict signing on kept darts: `es` read as a `±`-sign (zeros, absent on active darts,
are sent to `plus` and never arise). -/
def keptSign (M : CombMap D) (es : D → EdgeSign) (Del : Finset D) :
    {d : D // d ∉ Del} → StrictEdgeSign :=
  fun d => edgeToStrict (es d.1)



















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

/-- The underlying dart of the `n`-th iterate of `deleteSet p S` from `x` is a `p`-power of `x.1`,
recorded with its explicit exponent `gOffset`.  `gOffset p S x n` is the cumulative sum of the
`firstOutside` steps along the first `n` `deleteSet`-iterates. -/
noncomputable def gOffset (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) : ℕ → ℕ
  | 0 => 0
  | n + 1 => gOffset p S x n + Equiv.Perm.DeleteSet.firstOutside p S (((deleteSet p S) ^ n) x)







































































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























/-- The active step relation: a vertex- or edge-step between two **active** darts. -/
def activeStep (M : CombMap D) (es : D → EdgeSign) (d e : D) : Prop :=
  (M.σ.SameCycle d e ∨ e = M.α d) ∧ es d ≠ EdgeSign.zero ∧ es e ≠ EdgeSign.zero



open scoped Classical in
/-- The active-component deletion: everything **not** `EqvGen activeStep`-related to the seed `d₀`. -/
noncomputable def compDel (M : CombMap D) (es : D → EdgeSign) (d₀ : D) : Finset D :=
  Finset.univ.filter (fun d => ¬ Relation.EqvGen (activeStep M es) d₀ d)

@[simp] theorem mem_compDel (M : CombMap D) (es : D → EdgeSign) (d₀ d : D) :
    d ∈ compDel M es d₀ ↔ ¬ Relation.EqvGen (activeStep M es) d₀ d := by
  classical
  rw [compDel, Finset.mem_filter]
  simp



/-- Any `EqvGen activeStep` pair is either equal or both active. -/
theorem eqvGen_activeStep_active (M : CombMap D) (es : D → EdgeSign) {a b : D}
    (h : Relation.EqvGen (activeStep M es) a b) :
    (es a ≠ EdgeSign.zero ∧ es b ≠ EdgeSign.zero) ∨ a = b := by
  induction h with
  | rel x y hxy => exact Or.inl ⟨hxy.2.1, hxy.2.2⟩
  | refl x => exact Or.inr rfl
  | symm x y _ ih =>
      rcases ih with ⟨hx, hy⟩ | hxy
      · exact Or.inl ⟨hy, hx⟩
      · exact Or.inr hxy.symm
  | trans x y z _ _ ih1 ih2 =>
      rcases ih1 with ⟨hx, hy⟩ | hxy
      · rcases ih2 with ⟨_, hz⟩ | hyz
        · exact Or.inl ⟨hx, hz⟩
        · subst hyz; exact Or.inl ⟨hx, hy⟩
      · subst hxy; exact ih2

/-- Every dart `EqvGen`-reached from the active seed `d₀` is itself active. -/
theorem reached_active (M : CombMap D) (es : D → EdgeSign) {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    {d : D} (h : Relation.EqvGen (activeStep M es) d₀ d) : es d ≠ EdgeSign.zero := by
  rcases eqvGen_activeStep_active M es h with ⟨_, hd⟩ | hd
  · exact hd
  · exact hd ▸ hd₀

/-- The seed `d₀` is reached from itself. -/
theorem reached_refl (M : CombMap D) (es : D → EdgeSign) (d₀ : D) :
    Relation.EqvGen (activeStep M es) d₀ d₀ := Relation.EqvGen.refl _











variable (M : CombMap D) (es : D → EdgeSign)

/-- `compDel` is `α`-closed (the `hsub` input) when `es` is edge-invariant: a dart and its edge
partner are reachable together (both active, or both inactive hence both deleted). -/
theorem compDel_hsub (hes : ∀ d, es (M.α d) = es d) {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero) :
    ∀ d, d ∈ compDel M es d₀ ↔ M.α d ∈ compDel M es d₀ := by
  intro d
  rw [mem_compDel, mem_compDel, not_iff_not]
  constructor
  · intro h
    have hda : es d ≠ EdgeSign.zero := reached_active M es hd₀ h
    have hαa : es (M.α d) ≠ EdgeSign.zero := by rw [hes d]; exact hda
    refine Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ ?_)
    exact ⟨Or.inr rfl, hda, hαa⟩
  · intro h
    have hαa : es (M.α d) ≠ EdgeSign.zero := reached_active M es hd₀ h
    have hda : es d ≠ EdgeSign.zero := by rw [← hes d]; exact hαa
    refine Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ ?_)
    refine ⟨Or.inr ?_, hαa, hda⟩
    rw [M.alpha_alpha]









































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

/-- **The faithful geometric input** for Cauchy rigidity (ChatGPT's Q5 replacement for the unfaithful
`CauchyRigidityCertificate`).  A triangulated-sphere combinatorial map with a ±/0 edge signing, carrying
the GENUINE per-active-vertex arm data: at each active vertex the spherical-link `CauchyArmVertex` (whose
`four_le_signChanges` ≥4 is real), bridged to the skip-zeros σ-cycle count.  It does NOT carry any
Euler/`3F=2E`/face-count field — those live inside the combinatorial lemma. -/
structure CauchyMarkedTriangulatedSphere (M : CombMap D) where
  /-- The surface is a triangulated sphere. -/
  isSphere : M.IsSphereMap
  triangleFaces : M.FaceRegular 3
  /-- The edge graph is simple (no loops / no parallel edges).  This is a GENUINE property of every
  convex 3-polytope's boundary graph (Steinitz: the graph of a convex polytope is simple and
  3-connected), supplied by the ℝ³ realization — not a combinatorial convenience.  It is what rules
  out the digon degeneracy in the combinatorial lemma. -/
  isSimple : M.IsSimpleGraph
  /-- The dihedral-difference signing (±/0). -/
  edgeSign : D → EdgeSign
  /-- The signing is edge-invariant (`α`-stable): both darts of an edge carry the same sign. -/
  edgeSign_inv : ∀ d, edgeSign (M.α d) = edgeSign d
  /-- The GENUINE vertex-link arm datum at each active vertex (from real spherical links). -/
  vertexArm : ∀ d, ActiveVertex M edgeSign d → CauchyArmVertex
  /-- The bridge: the arm-datum's sign-change count is exactly the skip-zeros σ-cycle count at the vertex
  (the geometric σ-order = the link rotational order). -/
  vertexArm_signChanges_eq :
    ∀ d (hd : ActiveVertex M edgeSign d),
      (vertexArm d hd).signChanges = vertexFlipCountSkipZeros M edgeSign d





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









/-- **Cauchy's Lemma II, the `signChanges = 2` case — the two-arc contradiction.**

`Arc1 : Fin (m₁+1) → S2` and `Arc2 : Fin (m₂+1) → S2` are the two sub-arcs of `A` cut at the two
sign-change vertices; `Brc1`, `Brc2` the corresponding sub-arcs of `B`.  Both arcs are strictly convex
spherical arms (`harc1A …`).  The arcs share the chord endpoints: arc 1's endpoint chord and arc 2's
endpoint chord are the SAME spherical distance in `A` (`hshareA`) and in `B` (`hshareB`) — both equal
the diagonal `sDist (A s) (A t)` resp. `sDist (B s) (B t)`.  On each arc the arm sides match between
the `A`-side and `B`-side (`hsides1`, `hsides2`).  On arc 1 the joints are nondecreasing `A → B`
(`hmono1`) with one strictly opened (`hstrict1`); on arc 2 they are nonincreasing `A → B` (i.e.
nondecreasing `B → A`, `hmono2`).  This is impossible.

The proof: the `≤` arm lemma on arc 2 (applied `Brc2 → Arc2`) gives `chord(Brc2) ≤ chord(Arc2)`,
i.e. via the shared-chord identities `chord_B ≤ chord_A`; the **strict** arm lemma on arc 1 gives
`chord_A < chord_B`; chaining contradicts `<`. -/
theorem cauchy_two_signchange_split
    {m₁ m₂ : ℕ} (hm₁ : 2 ≤ m₁) (hm₂ : 2 ≤ m₂)
    (Arc1 Brc1 : Fin (m₁ + 1) → S2) (Arc2 Brc2 : Fin (m₂ + 1) → S2)
    (harc1A : StrictConvexSphArm Arc1) (harc1B : StrictConvexSphArm Brc1)
    (harc2A : StrictConvexSphArm Arc2) (harc2B : StrictConvexSphArm Brc2)
    -- arm sides match across A/B on each arc (both arcs inherit `hsides` of the closed polygons)
    (hsides1 : ∀ i : Fin m₁, sideLen Arc1 i = sideLen Brc1 i)
    (hsides2 : ∀ i : Fin m₂, sideLen Arc2 i = sideLen Brc2 i)
    -- the two arcs share the SAME chord (the diagonal `A s → A t`, resp. `B s → B t`)
    (hshareA : sDist (Arc1 0) (Arc1 (Fin.last m₁)) = sDist (Arc2 0) (Arc2 (Fin.last m₂)))
    (hshareB : sDist (Brc1 0) (Brc1 (Fin.last m₁)) = sDist (Brc2 0) (Brc2 (Fin.last m₂)))
    -- arc 1: joints open A → B with one strictly open; arc 2: joints close A → B
    (hmono1 : ∀ i : Fin (m₁ - 1), jointAngle Arc1 i ≤ jointAngle Brc1 i)
    (hstrict1 : ∃ i : Fin (m₁ - 1), jointAngle Arc1 i < jointAngle Brc1 i)
    (hmono2 : ∀ i : Fin (m₂ - 1), jointAngle Brc2 i ≤ jointAngle Arc2 i) :
    False := by
  -- strict arm lemma on arc 1:  chord(Arc1) < chord(Brc1)
  have h1 : sDist (Arc1 0) (Arc1 (Fin.last m₁)) < sDist (Brc1 0) (Brc1 (Fin.last m₁)) :=
    spherical_arm_mono_strict_uncond hm₁ Arc1 Brc1 harc1A harc1B hsides1 hmono1 hstrict1
  -- ≤ arm lemma on arc 2, applied Brc2 → Arc2:  chord(Brc2) ≤ chord(Arc2)
  have h2 : sDist (Brc2 0) (Brc2 (Fin.last m₂)) ≤ sDist (Arc2 0) (Arc2 (Fin.last m₂)) :=
    ProofsInTheBook.ZinanFFCT111.spherical_arm_mono_final_ch13 hm₂ Brc2 Arc2 harc2B harc2A
      (fun i => (hsides2 i).symm) hmono2
  -- chain through the shared-chord identities:
  --   chord_A := chord(Arc1) = chord(Arc2);  chord_B := chord(Brc1) = chord(Brc2)
  -- h1 : chord(Arc1) < chord(Brc1)
  -- h2 : chord(Brc2) ≤ chord(Arc2)
  -- hshareA : chord(Arc1) = chord(Arc2);  hshareB : chord(Brc1) = chord(Brc2)
  rw [hshareA] at h1            -- h1 : chord(Arc2) < chord(Brc1)
  rw [hshareB] at h1            -- h1 : chord(Arc2) < chord(Brc2)
  exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

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



/-- The contiguous sub-arc: keep `A s, A (s+1), …, A t`, re-indexed by `i ↦ A (s + i)`. -/
def subArc {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    Fin ((t - s) + 1) → S2 :=
  fun i => A ⟨s + i.val, by have := i.isLt; omega⟩

@[simp] theorem subArc_apply {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n)
    (i : Fin ((t - s) + 1)) :
    subArc A s t hst htn i = A ⟨s + i.val, by have := i.isLt; omega⟩ := rfl

@[simp] theorem subArc_zero {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    subArc A s t hst htn 0 = A ⟨s, by omega⟩ := by
  simp only [subArc, Fin.val_zero, Nat.add_zero]

/-- The last vertex of the sub-arc is `A t` (`= A ⟨s + (t - s)⟩`). -/
@[simp] theorem subArc_last {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    subArc A s t hst htn (Fin.last (t - s)) = A ⟨t, by omega⟩ := by
  simp only [subArc, Fin.val_last]
  congr 1
  apply Fin.ext
  show s + (t - s) = t
  omega



/-- The value of `1 : Fin ((t-s)+1)` is `1` (since `1 ≤ t - s`, so `(t-s)+1 ≥ 2 > 1`). -/
theorem one_val_subArc {t s : ℕ} (hm : 1 ≤ t - s) : ((1 : Fin ((t - s) + 1)) : ℕ) = 1 := by
  rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)

/-- `i ≠ Fin.last (t - s)` forces `i.val < t - s`. -/
theorem subArc_lt_of_ne_last {m : ℕ} {i : Fin (m + 1)} (hi : i ≠ Fin.last m) :
    i.val < m := by
  rcases Nat.lt_or_ge i.val m with h | h
  · exact h
  · exact absurd (Fin.ext (by simp only [Fin.val_last]; omega)) hi

/-- At a NON-last index `i ≠ Fin.last m` the cyclic successor of the sub-arc is `A ⟨s + i.val + 1⟩`
(no wraparound). -/
theorem subArc_succ_of_ne_last {n : ℕ} (A : Fin (n + 1) → S2) {s t : ℕ}
    (hst : s < t) (htn : t ≤ n) {i : Fin ((t - s) + 1)} (hi : i ≠ Fin.last (t - s)) :
    subArc A s t hst htn (i + 1) = A ⟨s + i.val + 1, by
      have := subArc_lt_of_ne_last hi; omega⟩ := by
  have hiv : i.val < t - s := subArc_lt_of_ne_last hi
  show A ⟨s + (i + 1).val, _⟩ = A ⟨s + i.val + 1, _⟩
  congr 1
  apply Fin.ext
  show s + (i + 1).val = s + i.val + 1
  have hsucc : (i + 1 : Fin ((t - s) + 1)).val = i.val + 1 := by
    rw [Fin.val_add, one_val_subArc (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hsucc]; omega

/-- At the last index the cyclic successor wraps to `A s`: `subArc A (Fin.last m + 1) = A s`. -/
theorem subArc_succ_last {n : ℕ} (A : Fin (n + 1) → S2) {s t : ℕ}
    (hst : s < t) (htn : t ≤ n) :
    subArc A s t hst htn (Fin.last (t - s) + 1) = A ⟨s, by omega⟩ := by
  have hzero : (Fin.last (t - s) + 1 : Fin ((t - s) + 1)) = 0 := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_last, Fin.val_zero, one_val_subArc (show 1 ≤ t - s by omega)]
    rw [Nat.mod_self]
  rw [hzero, subArc_zero]



/-- The diagonal `A s → A t` strictly supports the predecessor `A s`'s next interior vertex via an
interior witness.  Direct instance of `cut_diagonal_supports`: for `s < k < t` (in `Fin (n+1)`),
`0 < sOrient (A s) (A k) (A t)`. -/
theorem subArc_diag_support {n : ℕ} {A : Fin (n + 1) → S2}
    (hP : StrictConvexSphPolygon A) {s t : ℕ} (hst : s < t) (htn : t ≤ n)
    {k : ℕ} (hsk : s < k) (hkt : k < t) :
    0 < sOrient (A ⟨s, by omega⟩) (A ⟨k, by omega⟩) (A ⟨t, by omega⟩) := by
  have hab : (⟨s, by omega⟩ : Fin (n + 1)) < ⟨k, by omega⟩ := by
    rw [Fin.lt_def]; exact hsk
  have hbk : (⟨k, by omega⟩ : Fin (n + 1)) < ⟨t, by omega⟩ := by
    rw [Fin.lt_def]; exact hkt
  exact cut_diagonal_supports hP hab hbk

/-- The closing diagonal edge `A t → A s` is a short arc, when the range has an interior vertex
(`2 ≤ t - s`): pick the interior witness `A (s+1)` strictly supported by the diagonal `A s → A t`,
which forces `A s ≠ A t` and `A s` non-antipodal to `A t`. -/
theorem subArc_shortArc_closing {n : ℕ} {A : Fin (n + 1) → S2}
    (hP : StrictConvexSphPolygon A) {s t : ℕ} (hst : s < t) (htn : t ≤ n) (hm : 2 ≤ t - s) :
    ShortArc (A ⟨t, by omega⟩) (A ⟨s, by omega⟩) := by
  -- interior witness `k = s + 1` (exists since `2 ≤ t - s` makes `s + 1 < t`).
  have hsk : s < s + 1 := by omega
  have hkt : s + 1 < t := by omega
  have hpos := subArc_diag_support hP hst htn hsk hkt
  -- `0 < sOrient (A s)(A (s+1))(A t)` ⟹ `A s ≠ A t`, non-antipodal; symmetrise to the edge order.
  have hne : A ⟨s, by omega⟩ ≠ A ⟨t, by omega⟩ := ne_of_sOrient_pos_ac hpos
  have hnanti : (A ⟨s, by omega⟩ : E3) ≠ -(A ⟨t, by omega⟩ : E3) :=
    not_antipodal_of_sOrient_pos_ac hpos
  refine ⟨?_, ?_⟩
  · exact fun he => hne he.symm
  · intro he
    apply hnanti
    rw [he, neg_neg]



/-- The parent-index of a sub-arc vertex: `gidx i = ⟨s + i.val⟩`. -/
def gidx {n : ℕ} (s t : ℕ) (hst : s < t) (htn : t ≤ n) (i : Fin ((t - s) + 1)) : Fin (n + 1) :=
  ⟨s + i.val, by have := i.isLt; omega⟩

theorem subArc_eq_gidx {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n)
    (i : Fin ((t - s) + 1)) :
    subArc A s t hst htn i = A (gidx s t hst htn i) := rfl

theorem gidx_val {n : ℕ} (s t : ℕ) (hst : s < t) (htn : t ≤ n) (i : Fin ((t - s) + 1)) :
    (gidx s t hst htn i).val = s + i.val := rfl

/-- `gidx` is injective. -/
theorem gidx_injective {n : ℕ} (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    Function.Injective (gidx (n := n) s t hst htn) := by
  intro a b hab
  have hv : (gidx s t hst htn a).val = (gidx s t hst htn b).val := by rw [hab]
  rw [gidx_val, gidx_val] at hv
  exact Fin.ext (by omega)



/-- **The sub-arc polygon is strictly convex.**  The contiguous range `A s, …, A t` of a strictly
convex spherical arm `A`, with `2 ≤ t - s`, is a strictly convex polygon. -/
theorem subArc_strictConvexPolygon {n : ℕ} (A : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (s t : ℕ) (hst : s < t) (htn : t ≤ n) (hm : 2 ≤ t - s) :
    StrictConvexSphPolygon (subArc A s t hst htn) := by
  have hP := hA.closed_convex
  have hinj : Function.Injective (gidx (n := n) s t hst htn) := gidx_injective s t hst htn
  refine
    { three_le := by omega
      edge_short := ?_
      edge_support := ?_
      strict_nonincident := ?_
      open_hemisphere := ?_ }
  · -- edge_short
    intro i
    by_cases hi : i = Fin.last (t - s)
    · -- closing edge: A t → A s
      subst hi
      rw [subArc_last, subArc_succ_last]
      exact subArc_shortArc_closing hP hst htn hm
    · -- interior edge: A ⟨s+i⟩ → A ⟨s+i+1⟩, a parent edge
      rw [subArc_apply, subArc_succ_of_ne_last A hst htn hi]
      have hiv : i.val < t - s := subArc_lt_of_ne_last hi
      have := hP.edge_short ⟨s + i.val, by omega⟩
      rwa [show (⟨s + i.val, by omega⟩ + 1 : Fin (n + 1)) = ⟨s + i.val + 1, by omega⟩ by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
          Nat.mod_eq_of_lt (show s + i.val + 1 < n + 1 by omega)]] at this
  · -- edge_support
    intro i j
    rw [subArc_eq_gidx A s t hst htn j]
    by_cases hi : i = Fin.last (t - s)
    · -- closing edge: A t → A s
      subst hi
      rw [subArc_last, subArc_succ_last]
      -- closing-edge support: `0 ≤ sOrient (A t)(A s)(A (gidx j))`.
      have hjv : (gidx s t hst htn j).val = s + j.val := gidx_val s t hst htn j
      have hjlt : j.val ≤ t - s := by have := j.isLt; omega
      rcases Nat.lt_trichotomy (gidx s t hst htn j).val s with hlt | heq | hgt
      · -- impossible: gidx j ≥ s
        omega
      · -- gidx j = s: repeated column (third = second)
        have hjs : gidx s t hst htn j = ⟨s, by omega⟩ := Fin.ext (by rw [heq])
        rw [hjs]; simp only [sOrient]; rw [det3_self_mid]
      · -- gidx j > s: either gidx j = t (repeated first/third) or s < gidx j < t (strict, via cyclic)
        by_cases hjt : (gidx s t hst htn j).val = t
        · have hjeqt : gidx s t hst htn j = ⟨t, by omega⟩ := Fin.ext (by rw [hjt])
          rw [hjeqt]; simp only [sOrient]; rw [det3_self_right]
        · -- interior j: strict via cyclic re-indexing of the diagonal support
          have hsk : s < (gidx s t hst htn j).val := hgt
          have hkt : (gidx s t hst htn j).val < t := by
            rw [hjv] at hjt ⊢; have := j.isLt; omega
          have hpos := subArc_diag_support hP hst htn hsk hkt
          -- `sOrient (A t)(A s)(A k) = sOrient (A s)(A k)(A t)`
          have hcyc : sOrient (A ⟨t, by omega⟩) (A ⟨s, by omega⟩) (A (gidx s t hst htn j))
              = sOrient (A ⟨s, by omega⟩) (A (gidx s t hst htn j)) (A ⟨t, by omega⟩) :=
            (sOrient_cyclic _ _ _).1
          rw [hcyc]
          rw [show (A (gidx s t hst htn j)) = A ⟨(gidx s t hst htn j).val, by have := j.isLt; omega⟩ from rfl]
          exact le_of_lt hpos
    · -- interior edge: A's edge at index ⟨s+i⟩
      rw [subArc_apply, subArc_succ_of_ne_last A hst htn hi]
      have hiv : i.val < t - s := subArc_lt_of_ne_last hi
      have hsucc : (⟨s + i.val, by omega⟩ + 1 : Fin (n + 1)) = ⟨s + i.val + 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
          Nat.mod_eq_of_lt (show s + i.val + 1 < n + 1 by omega)]
      have := hP.edge_support ⟨s + i.val, by omega⟩ (gidx s t hst htn j)
      rwa [hsucc] at this
  · -- strict_nonincident
    intro i j hji hji1
    rw [subArc_eq_gidx A s t hst htn j]
    by_cases hi : i = Fin.last (t - s)
    · -- closing edge: A t → A s; non-incident means gidx j ∉ {t, s}, so s < gidx j < t.
      subst hi
      rw [subArc_last, subArc_succ_last]
      have hjv : (gidx s t hst htn j).val = s + j.val := gidx_val s t hst htn j
      -- j ≠ last ⟹ gidx j ≠ t; the wraparound successor of last is 0 ⟹ j ≠ 0 ⟹ gidx j ≠ s.
      have hjne_last : j ≠ Fin.last (t - s) := hji
      have hjval_lt : j.val < t - s := subArc_lt_of_ne_last hjne_last
      have hjne_zero : j ≠ 0 := by
        intro h; apply hji1; rw [h]
        symm
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_last, Fin.val_zero,
          one_val_subArc (show 1 ≤ t - s by omega)]
        rw [Nat.mod_self]
      have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun hc => hjne_zero (Fin.ext (by simp [hc])))
      have hsk : s < (gidx s t hst htn j).val := by rw [hjv]; omega
      have hkt : (gidx s t hst htn j).val < t := by rw [hjv]; omega
      have hpos := subArc_diag_support hP hst htn hsk hkt
      have hcyc : sOrient (A ⟨t, by omega⟩) (A ⟨s, by omega⟩) (A (gidx s t hst htn j))
          = sOrient (A ⟨s, by omega⟩) (A (gidx s t hst htn j)) (A ⟨t, by omega⟩) :=
        (sOrient_cyclic _ _ _).1
      rw [hcyc]
      rw [show (A (gidx s t hst htn j)) = A ⟨(gidx s t hst htn j).val, by have := j.isLt; omega⟩ from rfl]
      exact hpos
    · -- interior edge: A's edge at index ⟨s+i⟩; transport non-incidence via gidx injectivity.
      rw [subArc_apply, subArc_succ_of_ne_last A hst htn hi]
      have hiv : i.val < t - s := subArc_lt_of_ne_last hi
      have hsucc : (⟨s + i.val, by omega⟩ + 1 : Fin (n + 1)) = ⟨s + i.val + 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
          Nat.mod_eq_of_lt (show s + i.val + 1 < n + 1 by omega)]
      -- non-incidence: gidx j ≠ gidx i = ⟨s+i⟩ and gidx j ≠ ⟨s+i+1⟩
      have hne1 : gidx s t hst htn j ≠ (⟨s + i.val, by omega⟩ : Fin (n + 1)) := by
        intro h
        apply hji
        have hgi : gidx s t hst htn i = (⟨s + i.val, by omega⟩ : Fin (n + 1)) := rfl
        have : gidx s t hst htn j = gidx s t hst htn i := by rw [h, hgi]
        exact hinj this
      have hne2 : gidx s t hst htn j ≠ (⟨s + i.val + 1, by omega⟩ : Fin (n + 1)) := by
        intro h
        apply hji1
        have hi1ne : (i + 1 : Fin ((t - s) + 1)) ≠ 0 := by
          intro hc
          have : ((i + 1 : Fin ((t - s) + 1)) : ℕ) = 0 := by rw [hc]; rfl
          rw [Fin.val_add, one_val_subArc (show 1 ≤ t - s by omega),
            Nat.mod_eq_of_lt (show i.val + 1 < t - s + 1 by omega)] at this
          omega
        have hgi1 : gidx s t hst htn (i + 1) = (⟨s + i.val + 1, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rw [gidx_val]
          simp only [Fin.val_add, one_val_subArc (show 1 ≤ t - s by omega),
            Nat.mod_eq_of_lt (show i.val + 1 < t - s + 1 by omega)]
          omega
        have : gidx s t hst htn j = gidx s t hst htn (i + 1) := by rw [h, hgi1]
        exact hinj this
      have hsupp := hP.strict_nonincident ⟨s + i.val, by omega⟩ (gidx s t hst htn j) hne1
        (by rwa [hsucc])
      rwa [hsucc] at hsupp
  · -- open_hemisphere: subArc A = A ∘ gidx, so reindex
    obtain ⟨hh, hhn, hhpos⟩ := open_hemisphere_reindex hP (gidx (n := n) s t hst htn)
    refine ⟨hh, hhn, ?_⟩
    intro j
    rw [show ((subArc A s t hst htn j : S2) : E3) = ((A (gidx s t hst htn j) : S2) : E3) by
      rw [subArc_eq_gidx]]
    exact hhpos j

/-- **The sub-arc is a strictly convex arm.**  The contiguous range `A s, …, A t` of a strictly
convex spherical arm `A`, with `2 ≤ t - s`, is again a `StrictConvexSphArm` (parameter `m = t - s`,
closing diagonal `A s → A t`). -/
theorem subArc_strictConvexArm {n : ℕ} (A : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (s t : ℕ) (hst : s < t) (htn : t ≤ n) (hm : 2 ≤ t - s) :
    StrictConvexSphArm (subArc A s t hst htn) :=
  { two_le := hm
    closed_convex := subArc_strictConvexPolygon A hA s t hst htn hm }



/-- **Interior arm sides = parent sides.**  The `i`-th side of `subArc A s t` is the parent side
`sideLen A ⟨s + i.val⟩` (the edge `A(s+i) → A(s+i+1)`). -/
theorem subArc_sideLen {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n)
    (i : Fin (t - s)) :
    sideLen (subArc A s t hst htn) i = sideLen A ⟨s + i.val, by have := i.isLt; omega⟩ := by
  unfold sideLen
  have hc : (subArc A s t hst htn) i.castSucc = A ⟨s + i.val, by have := i.isLt; omega⟩ := rfl
  have hs : (subArc A s t hst htn) i.succ = A ⟨s + i.val + 1, by have := i.isLt; omega⟩ := rfl
  have hrc : (⟨s + i.val, by have := i.isLt; omega⟩ : Fin n).castSucc
      = (⟨s + i.val, by have := i.isLt; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext; simp
  have hrs : (⟨s + i.val, by have := i.isLt; omega⟩ : Fin n).succ
      = (⟨s + i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext; simp
  rw [hc, hs, hrc, hrs]

/-- **Interior arm joints = parent joints.**  The `i`-th joint of `subArc A s t` is the parent joint
`jointAngle A ⟨s + i.val⟩` (the spherical angle at `A(s+i+1)`).  The new closing diagonal contributes
no interior joint. -/
theorem subArc_jointAngle {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n)
    (i : Fin (t - s - 1)) :
    jointAngle (subArc A s t hst htn) i = jointAngle A ⟨s + i.val, by have := i.isLt; omega⟩ := by
  unfold jointAngle
  have hb : i.val < t - s - 1 := i.isLt
  have e0 : (subArc A s t hst htn) ⟨i.val, by omega⟩ = A ⟨s + i.val, by omega⟩ := rfl
  have e1 : (subArc A s t hst htn) ⟨i.val + 1, by omega⟩ = A ⟨s + i.val + 1, by omega⟩ := rfl
  have e2 : (subArc A s t hst htn) ⟨i.val + 2, by omega⟩ = A ⟨s + i.val + 2, by omega⟩ := rfl
  rw [e0, e1, e2]

/-- **The arm endpoint chord is the diagonal `A s → A t`.**  `sDist (subArc A 0) (subArc A (last m)) =
sDist (A s) (A t)`. -/
theorem subArc_endpt {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    sDist (subArc A s t hst htn 0) (subArc A s t hst htn (Fin.last (t - s)))
      = sDist (A ⟨s, by omega⟩) (A ⟨t, by omega⟩) := by
  rw [subArc_zero, subArc_last]

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



/-- Number of adjacent-differing pairs in a boolean list (a "linear" sign-change count). -/
def flips : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a ≠ b then 1 else 0) + flips (b :: rest)

/-- The cyclic flip count: close the cycle by appending the head, then count linear flips. -/
def cyclicFlips (l : List Bool) : ℕ :=
  match l with
  | [] => 0
  | h :: t => flips ((h :: t) ++ [h])

/-- **The parity engine.**  `flips (a :: rest)` is even iff the first and last entries agree. -/
theorem flips_even_iff_first_eq_last :
    ∀ (a : Bool) (rest : List Bool), Even (flips (a :: rest)) ↔ a = (a :: rest).getLast (by simp)
  | a, [] => by simp [flips]
  | a, b :: rest => by
    rw [show flips (a :: b :: rest) = (if a ≠ b then 1 else 0) + flips (b :: rest) from rfl]
    rw [List.getLast_cons (by simp)]
    have ih := flips_even_iff_first_eq_last b rest
    by_cases hab : a = b
    · subst hab; simp only [ne_eq, not_true_eq_false, if_false, Nat.zero_add]; rw [ih]
    · simp only [ne_eq, hab, not_false_eq_true, if_true]
      rw [Nat.add_comm, Nat.even_add_one, ih]
      revert hab; cases a <;> cases (b :: rest).getLast (by simp) <;> cases b <;> simp

/-- **Cyclic parity.**  The number of cyclic sign flips around any boolean cycle is even. -/
theorem cyclicFlips_even (l : List Bool) : Even (cyclicFlips l) := by
  cases l with
  | nil => simp [cyclicFlips]
  | cons h t =>
    show Even (flips ((h :: t) ++ [h]))
    rw [show (h :: t) ++ [h] = h :: (t ++ [h]) by simp, flips_even_iff_first_eq_last]
    rw [List.getLast_cons (by simp)]
    simp

/-- `flips l = 0` exactly when all entries of `l` are equal. -/
theorem flips_eq_zero_iff_all_eq :
    ∀ (l : List Bool), flips l = 0 ↔ ∀ x ∈ l, ∀ y ∈ l, x = y
  | [] => by simp [flips]
  | [a] => by simp [flips]
  | a :: b :: rest => by
    rw [show flips (a :: b :: rest) = (if a ≠ b then 1 else 0) + flips (b :: rest) from rfl]
    have ih := flips_eq_zero_iff_all_eq (b :: rest)
    constructor
    · intro h
      have hab : a = b := by by_contra hne; simp [hne] at h
      have hrest : flips (b :: rest) = 0 := by omega
      have hall := ih.mp hrest
      intro x hx y hy
      simp only [List.mem_cons] at hx hy
      have hxb : x = b := by
        rcases hx with h' | h'
        · rw [h', hab]
        · exact hall x (by simp [List.mem_cons, h']) b (by simp)
      have hyb : y = b := by
        rcases hy with h' | h'
        · rw [h', hab]
        · exact hall y (by simp [List.mem_cons, h']) b (by simp)
      rw [hxb, hyb]
    · intro h
      have hab : a = b := h a (by simp) b (by simp)
      have hrest : flips (b :: rest) = 0 := by
        rw [ih]; intro x hx y hy; exact h x (by simp [hx]) y (by simp [hy])
      rw [hrest]; simp [hab]

/-- `cyclicFlips l = 0` forces all entries of `l` equal (the closed cycle has no flip). -/
theorem cyclicFlips_eq_zero_iff_all_eq (l : List Bool) :
    cyclicFlips l = 0 ↔ ∀ x ∈ l, ∀ y ∈ l, x = y := by
  cases l with
  | nil => simp [cyclicFlips]
  | cons h t =>
    show flips ((h :: t) ++ [h]) = 0 ↔ _
    rw [flips_eq_zero_iff_all_eq]
    constructor
    · intro hall x hx y hy
      exact hall x (List.mem_append_left _ hx) y (List.mem_append_left _ hy)
    · intro hall x hx y hy
      -- every element of (h::t)++[h] lies in h::t (the trailing [h] is just h again)
      have hxl : x ∈ h :: t := by
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hx'
        · rw [List.mem_singleton.mp hx']; exact List.mem_cons_self
      have hyl : y ∈ h :: t := by
        rcases List.mem_append.mp hy with hy' | hy'
        · exact hy'
        · rw [List.mem_singleton.mp hy']; exact List.mem_cons_self
      exact hall x hxl y hyl



open scoped Classical

/-- The signed dihedral change at joint `i`. -/
noncomputable def jointDiff {n : ℕ} (A B : Fin (n + 1) → S2) (i : Fin (n - 1)) : ℝ :=
  jointAngle B i - jointAngle A i

/-- The nonzero-sign boolean list of a real-valued sequence, in index order
(`true` = positive, `false` = negative; zeros skipped). -/
noncomputable def nzSigns {m : ℕ} (d : Fin m → ℝ) : List Bool :=
  ((List.finRange m).filter (fun i => decide (d i ≠ 0))).map (fun i => decide (0 < d i))

theorem mem_nzSigns {m : ℕ} (d : Fin m → ℝ) (b : Bool) :
    b ∈ nzSigns d ↔ ∃ i, d i ≠ 0 ∧ b = decide (0 < d i) := by
  simp only [nzSigns, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem nzSigns_ne_nil {m : ℕ} (d : Fin m → ℝ) (h : ∃ i, d i ≠ 0) : nzSigns d ≠ [] := by
  obtain ⟨i, hi⟩ := h
  intro hnil
  have : decide (0 < d i) ∈ nzSigns d := (mem_nzSigns d _).mpr ⟨i, hi, rfl⟩
  rw [hnil] at this; simp at this

/-- **All nonzero signs equal ⟹ monotone in one direction.**  If `nzSigns d` is nonempty and all its
entries agree, then either every `d i ≥ 0` or every `d i ≤ 0`. -/
theorem all_same_sign {m : ℕ} (d : Fin m → ℝ)
    (hne : nzSigns d ≠ [])
    (hall : ∀ x ∈ nzSigns d, ∀ y ∈ nzSigns d, x = y) :
    (∀ i, 0 ≤ d i) ∨ (∀ i, d i ≤ 0) := by
  obtain ⟨head, ht, hhead⟩ := List.exists_cons_of_ne_nil hne
  have hb : head ∈ nzSigns d := by rw [hhead]; exact List.mem_cons_self
  by_cases hcase : head = true
  · left
    intro i
    by_cases hzi : d i = 0
    · rw [hzi]
    · have hmem : decide (0 < d i) ∈ nzSigns d := (mem_nzSigns d _).mpr ⟨i, hzi, rfl⟩
      have heq := hall _ hmem _ hb
      rw [hcase] at heq
      have : (0 : ℝ) < d i := by simpa using heq
      linarith
  · right
    intro i
    have hcase' : head = false := by cases head with | false => rfl | true => exact absurd rfl hcase
    by_cases hzi : d i = 0
    · rw [hzi]
    · have hmem : decide (0 < d i) ∈ nzSigns d := (mem_nzSigns d _).mpr ⟨i, hzi, rfl⟩
      have heq := hall _ hmem _ hb
      rw [hcase'] at heq
      have hnpos : ¬ (0 < d i) := by simpa using heq
      linarith [lt_of_le_of_ne (not_lt.mp hnpos) hzi]











/-- Cyclic rotation of a closed arm: `rotPoly A k i = A (i + k)`. -/
def rotPoly {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) : Fin (n + 1) → S2 :=
  fun i => A (i + k)

/-- **Cyclic rotation preserves strict convexity (`rotateArm`).**  The four geometric fields of
`StrictConvexSphPolygon` are cyclic, so relabelling the vertices by a fixed shift preserves them; the
arm bound `two_le` is index-free. -/
theorem rotPoly_strictConvexArm {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (k : Fin (n + 1)) :
    StrictConvexSphArm (rotPoly A k) := by
  refine { two_le := hA.two_le, closed_convex := ?_ }
  have hP := hA.closed_convex
  have key : ∀ i : Fin (n + 1), (i + 1) + k = (i + k) + 1 := fun i => by rw [add_right_comm]
  refine { three_le := hP.three_le, edge_short := ?_, edge_support := ?_,
           strict_nonincident := ?_, open_hemisphere := ?_ }
  · intro i
    show ShortArc (A (i + k)) (A ((i + 1) + k))
    rw [key i]; exact hP.edge_short (i + k)
  · intro i j
    show 0 ≤ sOrient (A (i + k)) (A ((i + 1) + k)) (A (j + k))
    rw [key i]; exact hP.edge_support (i + k) (j + k)
  · intro i j hji hji1
    show 0 < sOrient (A (i + k)) (A ((i + 1) + k)) (A (j + k))
    rw [key i]
    apply hP.strict_nonincident (i + k) (j + k)
    · intro h; exact hji (add_right_cancel h)
    · intro h; apply hji1
      have h2 : j + k = (i + 1) + k := by rw [key i]; exact h
      exact add_right_cancel h2
  · obtain ⟨h, hn, hpos⟩ := hP.open_hemisphere
    exact ⟨h, hn, fun i => hpos (i + k)⟩



/-- **Every cyclic edge of `A` equals the corresponding edge of `B`.**  The `n` interior edges are
equal by `hsides`; the closing edge `A n → A 0` is equal by `hclose`. -/
theorem all_cyclic_edges_eq {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n + 1) → S2)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))) :
    ∀ k : Fin (n + 1), sDist (A k) (A (k + 1)) = sDist (B k) (B (k + 1)) := by
  intro k
  rcases Nat.lt_or_ge k.val n with hk | hk
  · have hkk := hsides ⟨k.val, hk⟩
    unfold sideLen at hkk
    have e1 : (⟨k.val, hk⟩ : Fin n).castSucc = k := by apply Fin.ext; simp
    have hk1v : (k + 1 : Fin (n + 1)).val = k.val + 1 := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
        Nat.mod_eq_of_lt (show k.val + 1 < n + 1 by omega)]
    have e2 : (⟨k.val, hk⟩ : Fin n).succ = k + 1 := by
      apply Fin.ext; rw [Fin.val_succ, hk1v]
    rw [e1, e2] at hkk; exact hkk
  · have hkn : k.val = n := by have := k.isLt; omega
    have hklast : k = Fin.last n := Fin.ext (by simp [hkn])
    have hk1 : k + 1 = 0 := by
      apply Fin.ext
      show (k.val + (1 : Fin (n + 1)).val) % (n + 1) = 0
      rw [hkn, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega), Nat.mod_self]
    rw [hk1, hklast]
    rw [sDist_comm (A (Fin.last n)) (A 0), sDist_comm (B (Fin.last n)) (B 0)]
    exact hclose

/-- **The rotated arms have equal corresponding sides.**  `rotPoly A k` and `rotPoly B k` agree on
every arm side, because every cyclic edge of `A` equals the corresponding edge of `B`. -/
theorem rotPoly_sideLen_eq {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n + 1) → S2)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (k : Fin (n + 1)) :
    ∀ i : Fin n, sideLen (rotPoly A k) i = sideLen (rotPoly B k) i := by
  intro i
  unfold sideLen rotPoly
  -- side i of rotPoly A k = sDist (A (i.castSucc + k)) (A (i.succ + k)); and i.succ = i.castSucc + 1.
  have key := all_cyclic_edges_eq hn A B hsides hclose (i.castSucc + k)
  have hcast : (i.succ : Fin (n + 1)) = i.castSucc + 1 := by
    apply Fin.ext
    rw [Fin.val_succ, Fin.val_add, Fin.val_castSucc, Fin.val_one',
      Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
      Nat.mod_eq_of_lt (show i.val + 1 < n + 1 by have := i.isLt; omega)]
  have heq : (i.succ : Fin (n + 1)) + k = (i.castSucc + k) + 1 := by
    rw [hcast, add_right_comm]
  rw [heq]; exact key


structure TwoArcSplitData {n : ℕ} (A B : Fin (n + 1) → S2) where
  /-- arc-1 parameter. -/
  m₁ : ℕ
  /-- arc-2 parameter. -/
  m₂ : ℕ
  hm₁ : 2 ≤ m₁
  hm₂ : 2 ≤ m₂
  Arc1 : Fin (m₁ + 1) → S2
  Brc1 : Fin (m₁ + 1) → S2
  Arc2 : Fin (m₂ + 1) → S2
  Brc2 : Fin (m₂ + 1) → S2
  harc1A : StrictConvexSphArm Arc1
  harc1B : StrictConvexSphArm Brc1
  harc2A : StrictConvexSphArm Arc2
  harc2B : StrictConvexSphArm Brc2
  hsides1 : ∀ i : Fin m₁, sideLen Arc1 i = sideLen Brc1 i
  hsides2 : ∀ i : Fin m₂, sideLen Arc2 i = sideLen Brc2 i
  hshareA : sDist (Arc1 0) (Arc1 (Fin.last m₁)) = sDist (Arc2 0) (Arc2 (Fin.last m₂))
  hshareB : sDist (Brc1 0) (Brc1 (Fin.last m₁)) = sDist (Brc2 0) (Brc2 (Fin.last m₂))
  hmono1 : ∀ i : Fin (m₁ - 1), jointAngle Arc1 i ≤ jointAngle Brc1 i
  hstrict1 : ∃ i : Fin (m₁ - 1), jointAngle Arc1 i < jointAngle Brc1 i
  hmono2 : ∀ i : Fin (m₂ - 1), jointAngle Brc2 i ≤ jointAngle Arc2 i

/-- **The two-arc cut yields `False`.**  Genuine two-arc split data is refuted by the proven Cauchy
Lemma II two-arc contradiction. -/
theorem TwoArcSplitData.contradiction {n : ℕ} {A B : Fin (n + 1) → S2}
    (d : TwoArcSplitData A B) : False :=
  cauchy_two_signchange_split d.hm₁ d.hm₂ d.Arc1 d.Brc1 d.Arc2 d.Brc2
    d.harc1A d.harc1B d.harc2A d.harc2B d.hsides1 d.hsides2 d.hshareA d.hshareB
    d.hmono1 d.hstrict1 d.hmono2

/-- **The `signChanges = 2` fixed-chord obstruction.**  From genuine two-arc split data the two-arc
argument gives `False`; any `CauchyArmFixedChordObstruction` then follows (its only use is its
`.contradiction`, which is exactly this `False`). -/
noncomputable def twoSignChanges_obstruction {n : ℕ} {A B : Fin (n + 1) → S2}
    (d : TwoArcSplitData A B) : CauchyArmFixedChordObstruction :=
  (d.contradiction).elim




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



/-- The spherical angle of the closed link polygon at vertex `i : Fin (n+1)`, taken between its two
**cyclic** neighbours `A (i-1)` and `A (i+1)`. -/
noncomputable def linkAngle {n : ℕ} (A : Fin (n + 1) → S2) (i : Fin (n + 1)) : ℝ :=
  sphAngle (A (i - 1)) (A i) (A (i + 1))

/-- **Interior link angles ARE arm joints.**  For an interior joint index `i : Fin (n-1)`, the link
angle at vertex `i+1` equals the arm joint angle `jointAngle A i`.  (No wraparound: `1 ≤ i+1 ≤ n-1`.) -/
theorem linkAngle_interior {n : ℕ} (A : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    linkAngle A ⟨i.val + 1, by have := i.isLt; omega⟩ = jointAngle A i := by
  have hi := i.isLt
  unfold linkAngle jointAngle
  -- the three cyclic indices i+1-1, i+1, i+1+1 are ⟨i⟩, ⟨i+1⟩, ⟨i+2⟩ (no wrap)
  have e0 : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) - 1 = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rw [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
    show (n + 1 - 1 + (i.val + 1)) % (n + 1) = i.val
    rw [show n + 1 - 1 + (i.val + 1) = i.val + (n + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have e2 : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) + 1 = ⟨i.val + 2, by omega⟩ := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
      Nat.mod_eq_of_lt (show i.val + 1 + 1 < n + 1 by omega)]
  rw [e0, e2]

/-- The closing angle at link vertex `0`: between the closing edge `n → 0` and edge `0 → 1`. -/
theorem linkAngle_zero {n : ℕ} (A : Fin (n + 1) → S2) :
    linkAngle A 0 = sphAngle (A (Fin.last n)) (A 0) (A 1) := by
  unfold linkAngle
  have em1 : (0 : Fin (n + 1)) - 1 = Fin.last n :=
    sub_eq_of_eq_add (Fin.last_add_one n).symm
  have ep1 : (0 : Fin (n + 1)) + 1 = 1 := by simp
  rw [em1, ep1]

/-- The closing angle at link vertex `n` (= `Fin.last n`): between edge `n-1 → n` and the closing
edge `n → 0`. -/
theorem linkAngle_last {n : ℕ} (A : Fin (n + 1) → S2) :
    linkAngle A (Fin.last n) = sphAngle (A (Fin.last n - 1)) (A (Fin.last n)) (A 0) := by
  unfold linkAngle
  rw [Fin.last_add_one]



/-- The signed change of the link angle at vertex `i : Fin (n+1)`. -/
noncomputable def linkDiff {n : ℕ} (A B : Fin (n + 1) → S2) (i : Fin (n + 1)) : ℝ :=
  linkAngle B i - linkAngle A i

/-- **The FULL closed-link cyclic sign-change count.**  The genuine cyclic flip count of the nonzero
dihedral-change signs around ALL `n+1` link vertices (the closing angles included). -/
noncomputable def signChangesFull {n : ℕ} (A B : Fin (n + 1) → S2) : ℕ :=
  cyclicFlips (nzSigns (linkDiff A B))

/-- `signChangesFull` is even (cyclic parity), a genuine theorem. -/
theorem signChangesFull_even {n : ℕ} (A B : Fin (n + 1) → S2) : Even (signChangesFull A B) :=
  cyclicFlips_even _

/-- **The full link-diff restricts to the arm joint-diff.**  At the interior link vertex `i+1`, the
full `linkDiff` equals the arm `jointDiff` (`Ch13ArmVertex.jointDiff`). -/
theorem linkDiff_interior {n : ℕ} (A B : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    linkDiff A B ⟨i.val + 1, by have := i.isLt; omega⟩ = jointDiff A B i := by
  unfold linkDiff jointDiff
  rw [linkAngle_interior, linkAngle_interior]



/-- **The `signChangesFull = 0` fixed-chord obstruction.**  Same conclusion as
`Ch13ArmVertex.zeroSignChanges_obstruction`, but the hypothesis is now `0` changes over the FULL
`n+1`-cycle (closing angles included), which is *stronger* and so still yields the obstruction. -/
noncomputable def zeroSignChangesFull_obstruction {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (hactive : ∃ i : Fin (n - 1), jointAngle A i ≠ jointAngle B i)
    (hzero : signChangesFull A B = 0) :
    CauchyArmFixedChordObstruction := by
  -- Some interior arm joint differs ⟹ the corresponding FULL link-diff is nonzero.
  have hactive' : ∃ k, linkDiff A B k ≠ 0 := by
    obtain ⟨i, hi⟩ := hactive
    refine ⟨⟨i.val + 1, by have := i.isLt; omega⟩, ?_⟩
    rw [linkDiff_interior]
    exact sub_ne_zero.mpr (Ne.symm hi)
  have hne : nzSigns (linkDiff A B) ≠ [] := nzSigns_ne_nil _ hactive'
  have hall : ∀ x ∈ nzSigns (linkDiff A B), ∀ y ∈ nzSigns (linkDiff A B), x = y :=
    (cyclicFlips_eq_zero_iff_all_eq _).mp hzero
  have hdir := all_same_sign (linkDiff A B) hne hall
  by_cases hpos : ∀ k, 0 ≤ linkDiff A B k
  · -- opening: every interior joint A ≤ B (read off from the full diff at vertex i+1)
    refine CauchyArmFixedChordObstruction.opening
      { n := n, hn := hn, A := A, B := B, hA := hA, hB := hB,
        equal_sides := hsides
        opened := fun i => ?_
        some_angle_strictly_opened := ?_
        fixed_chord := hclose }
    · have hk := hpos ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [linkDiff_interior] at hk
      simp only [jointDiff] at hk; linarith
    · obtain ⟨i, hi⟩ := hactive
      refine ⟨i, ?_⟩
      have hk := hpos ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [linkDiff_interior] at hk
      simp only [jointDiff] at hk
      have hne' : jointAngle B i - jointAngle A i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
      linarith [lt_of_le_of_ne hk (Ne.symm hne')]
  · -- closing: every interior joint B ≤ A
    have hneg : ∀ k, linkDiff A B k ≤ 0 := hdir.resolve_left hpos
    refine CauchyArmFixedChordObstruction.closing
      { n := n, hn := hn, A := A, B := B, hA := hA, hB := hB,
        equal_sides := hsides
        closed := fun i => ?_
        some_angle_strictly_closed := ?_
        fixed_chord := hclose }
    · have hk := hneg ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [linkDiff_interior] at hk
      simp only [jointDiff] at hk; linarith
    · obtain ⟨i, hi⟩ := hactive
      refine ⟨i, ?_⟩
      have hk := hneg ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [linkDiff_interior] at hk
      simp only [jointDiff] at hk
      have hne' : jointAngle B i - jointAngle A i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
      linarith [lt_of_le_of_ne hk hne']


noncomputable def cauchyArmVertexFull_of_links (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (hactive : ∃ i : Fin (n - 1), jointAngle A i ≠ jointAngle B i)
    (htwoArc : signChangesFull A B = 2 → TwoArcSplitData A B) :
    Chapter13.CauchyArmVertex where
  signChanges := signChangesFull A B
  signChanges_even := signChangesFull_even A B
  zero_sign_changes_obstruction :=
    fun hzero => zeroSignChangesFull_obstruction hn A B hA hB hsides hclose hactive hzero
  two_sign_changes_obstruction :=
    fun htwo => twoSignChanges_obstruction (htwoArc htwo)




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



/-- The **local ℝ³ data of one convex-polytope vertex**.

`n + 1` neighbours `p 0, …, p n` are arranged cyclically around the apex `o`.  The convexity data is
phrased entirely on the **raw** edge vectors `p i - o` (no posited spherical structure):

* `apex_ne` — every neighbour differs from the apex (so the edge direction is well defined);
* `open_hemi` — the raw edge vectors all lie strictly on the positive side of a common unit
  functional `h` (one open hemisphere);
* `turn_support` — each oriented raw edge `(p i - o, p (i+1) - o)` keeps **every** other raw
  direction on the nonnegative side of the plane it spans through the apex;
* `turn_strict` — the same, strictly, for the non-incident directions.

These are exactly the predicates `vertexLink_strictArm` consumes, and they are satisfiable
(see `cubeCornerStar`). -/
structure VertexStar where
  /-- Arm parameter: there are `n + 1` neighbours / edges, with `n ≥ 2`. -/
  n : ℕ
  /-- At least three edges (`n + 1 ≥ 3`): a convex-polytope vertex has `≥ 3` incident edges. -/
  hn : 2 ≤ n
  /-- The apex of the star. -/
  o : E3
  /-- The cyclically ordered neighbours. -/
  p : Fin (n + 1) → E3
  /-- Each neighbour differs from the apex. -/
  apex_ne : ∀ i : Fin (n + 1), p i ≠ o
  /-- The raw edge vectors lie in one open hemisphere. -/
  open_hemi : ∃ h : E3, ‖h‖ = 1 ∧ ∀ i : Fin (n + 1), 0 < ⟪h, p i - o⟫
  /-- Each oriented raw edge supports every raw direction on the nonnegative side. -/
  turn_support : ∀ i j : Fin (n + 1), 0 ≤ det3 (p i - o) (p (i + 1) - o) (p j - o)
  /-- Non-incident raw directions are strictly on the positive side. -/
  turn_strict : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < det3 (p i - o) (p (i + 1) - o) (p j - o)

namespace VertexStar

variable (S : VertexStar)

/-- The raw edge vector `p i - o`. -/
def rawDir (i : Fin (S.n + 1)) : E3 := S.p i - S.o

theorem rawDir_ne_zero (i : Fin (S.n + 1)) : S.rawDir i ≠ 0 := by
  simp only [rawDir, sub_ne_zero]
  exact S.apex_ne i

theorem norm_rawDir_pos (i : Fin (S.n + 1)) : 0 < ‖S.rawDir i‖ :=
  norm_pos_iff.mpr (S.rawDir_ne_zero i)

/-- The unit edge direction at the apex toward `p i`, a point of `S²`. -/
def edgeDir (i : Fin (S.n + 1)) : S2 :=
  ⟨‖S.rawDir i‖⁻¹ • S.rawDir i, by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt (S.norm_rawDir_pos i))⟩

/-- `edgeDir i` is the positive multiple `‖rawDir i‖⁻¹` of the raw direction. -/
theorem edgeDir_coe (i : Fin (S.n + 1)) :
    (S.edgeDir i : E3) = ‖S.rawDir i‖⁻¹ • S.rawDir i := rfl

theorem inv_norm_pos (i : Fin (S.n + 1)) : 0 < ‖S.rawDir i‖⁻¹ :=
  inv_pos.mpr (S.norm_rawDir_pos i)

/-- The **vertex link**: the cyclic edge-direction family, presented as a `Fin (n+1) → S²` tuple in
the `StrictConvexSphArm` convention. -/
def vertexLink : Fin (S.n + 1) → S2 := S.edgeDir

@[simp] theorem vertexLink_apply (i : Fin (S.n + 1)) : S.vertexLink i = S.edgeDir i := rfl



/-- `det3` is multilinear: scaling each argument multiplies the determinant by the product. -/
theorem det3_smul (ca cb cc : ℝ) (a b c : E3) :
    det3 (ca • a) (cb • b) (cc • c) = (ca * cb * cc) * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

/-- The signed volume of three link directions is a positive multiple of the raw `det3`. -/
theorem sOrient_edgeDir (a b c : Fin (S.n + 1)) :
    sOrient (S.edgeDir a) (S.edgeDir b) (S.edgeDir c)
      = (‖S.rawDir a‖⁻¹ * ‖S.rawDir b‖⁻¹ * ‖S.rawDir c‖⁻¹)
        * det3 (S.rawDir a) (S.rawDir b) (S.rawDir c) := by
  rw [sOrient, edgeDir_coe, edgeDir_coe, edgeDir_coe, det3_smul]

/-- The product of the three inverse norms is positive. -/
theorem inv_norm_prod_pos (a b c : Fin (S.n + 1)) :
    0 < ‖S.rawDir a‖⁻¹ * ‖S.rawDir b‖⁻¹ * ‖S.rawDir c‖⁻¹ :=
  mul_pos (mul_pos (S.inv_norm_pos a) (S.inv_norm_pos b)) (S.inv_norm_pos c)

/-- Sign transfer (nonnegative): the raw support hypothesis gives nonnegative link orientation. -/
theorem sOrient_edgeDir_nonneg (a b c : Fin (S.n + 1))
    (h : 0 ≤ det3 (S.rawDir a) (S.rawDir b) (S.rawDir c)) :
    0 ≤ sOrient (S.edgeDir a) (S.edgeDir b) (S.edgeDir c) := by
  rw [sOrient_edgeDir]
  exact mul_nonneg (le_of_lt (S.inv_norm_prod_pos a b c)) h

/-- Sign transfer (strict). -/
theorem sOrient_edgeDir_pos (a b c : Fin (S.n + 1))
    (h : 0 < det3 (S.rawDir a) (S.rawDir b) (S.rawDir c)) :
    0 < sOrient (S.edgeDir a) (S.edgeDir b) (S.edgeDir c) := by
  rw [sOrient_edgeDir]
  exact mul_pos (S.inv_norm_prod_pos a b c) h



/-- Since `n ≥ 2`, every edge index `i` admits a non-incident index `j` (`j ≠ i`, `j ≠ i+1`). -/
theorem exists_noninc (i : Fin (S.n + 1)) : ∃ j : Fin (S.n + 1), j ≠ i ∧ j ≠ i + 1 := by
  -- The set `{i, i+1}` has at most 2 elements; with `≥ 3` total there is a third.
  by_contra hcon
  push_neg at hcon
  -- every j is i or i+1
  have hsub : (Finset.univ : Finset (Fin (S.n + 1))) ⊆ {i, i + 1} := by
    intro j _
    rcases eq_or_ne j i with hji | hji
    · simp [hji]
    · have := hcon j hji
      simp [this]
  have hle := Finset.card_le_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hle2 : ({i, i + 1} : Finset (Fin (S.n + 1))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have := S.hn
  omega

/-- If `det3 a b c > 0` for some `c`, then `b` is not a scalar multiple of `a`. -/
theorem not_smul_of_det3_pos {a b : E3} (c : E3) (h : 0 < det3 a b c)
    (t : ℝ) : b ≠ t • a := by
  intro hb
  rw [hb] at h
  have : det3 a (t • a) c = 0 := by
    simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this] at h; exact lt_irrefl _ h

/-- Consecutive link directions are not equal. -/
theorem edgeDir_ne (i : Fin (S.n + 1)) : S.edgeDir i ≠ S.edgeDir (i + 1) := by
  obtain ⟨j, hji, hjip⟩ := S.exists_noninc i
  intro heq
  -- edgeDir i = edgeDir (i+1) ⟹ rawDir (i+1) = (‖raw(i+1)‖/‖raw i‖) • rawDir i
  have hcoe : (S.edgeDir i : E3) = (S.edgeDir (i + 1) : E3) := by rw [heq]
  rw [edgeDir_coe, edgeDir_coe] at hcoe
  -- rawDir (i+1) = (‖raw(i+1)‖ * ‖raw i‖⁻¹) • rawDir i
  have hraw : S.rawDir (i + 1) = (‖S.rawDir (i + 1)‖ * ‖S.rawDir i‖⁻¹) • S.rawDir i := by
    have h1 : ‖S.rawDir (i + 1)‖ • (‖S.rawDir i‖⁻¹ • S.rawDir i)
        = ‖S.rawDir (i + 1)‖ • (‖S.rawDir (i + 1)‖⁻¹ • S.rawDir (i + 1)) := by
      rw [hcoe]
    rw [smul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt (S.norm_rawDir_pos (i + 1))),
      one_smul] at h1
    exact h1.symm
  have hpos := S.turn_strict i j hji hjip
  exact (not_smul_of_det3_pos (S.rawDir j) hpos (‖S.rawDir (i + 1)‖ * ‖S.rawDir i‖⁻¹)) hraw

/-- Consecutive link directions are not antipodal. -/
theorem edgeDir_not_antipodal (i : Fin (S.n + 1)) :
    (S.edgeDir i : E3) ≠ -(S.edgeDir (i + 1) : E3) := by
  obtain ⟨j, hji, hjip⟩ := S.exists_noninc i
  intro heq
  rw [edgeDir_coe, edgeDir_coe] at heq
  -- ‖raw i‖⁻¹ • raw i = -(‖raw(i+1)‖⁻¹ • raw(i+1)) ⟹ raw(i+1) = (-(‖raw(i+1)‖ * ‖raw i‖⁻¹)) • raw i
  have hraw : S.rawDir (i + 1) = (-(‖S.rawDir (i + 1)‖ * ‖S.rawDir i‖⁻¹)) • S.rawDir i := by
    have h1 := congrArg (fun z : E3 => ‖S.rawDir (i + 1)‖ • z) heq
    simp only [smul_neg, smul_smul] at h1
    rw [mul_inv_cancel₀ (ne_of_gt (S.norm_rawDir_pos (i + 1))), one_smul] at h1
    -- h1 : (‖r(i+1)‖ * ‖r i‖⁻¹) • r i = -r(i+1)
    rw [neg_smul, h1, neg_neg]
  have hpos := S.turn_strict i j hji hjip
  exact (not_smul_of_det3_pos (S.rawDir j) hpos (-(‖S.rawDir (i + 1)‖ * ‖S.rawDir i‖⁻¹))) hraw

/-- The consecutive link edge is a short arc. -/
theorem edgeDir_shortArc (i : Fin (S.n + 1)) : ShortArc (S.edgeDir i) (S.edgeDir (i + 1)) :=
  ⟨S.edgeDir_ne i, S.edgeDir_not_antipodal i⟩



theorem inner_h_edgeDir_pos {h : E3} (i : Fin (S.n + 1))
    (hraw : 0 < ⟪h, S.rawDir i⟫) : 0 < ⟪h, (S.edgeDir i : E3)⟫ := by
  rw [edgeDir_coe, real_inner_smul_right]
  exact mul_pos (S.inv_norm_pos i) hraw



/-- **The vertex link is a strictly convex spherical arm.**

Each of the five `StrictConvexSphPolygon` fields is derived from the ℝ³ convexity fields of `S`:
`edge_short` from `turn_strict` (via `edgeDir_shortArc`); `edge_support`/`strict_nonincident` from
`turn_support`/`turn_strict` (via the `det3` sign-transfer lemmas); `open_hemisphere` from
`open_hemi`; `three_le` from `hn`. -/
theorem vertexLink_strictArm : StrictConvexSphArm S.vertexLink where
  two_le := S.hn
  closed_convex :=
    { three_le := by have := S.hn; omega
      edge_short := fun i => by
        simpa only [vertexLink_apply] using S.edgeDir_shortArc i
      edge_support := fun i j => by
        simp only [vertexLink_apply]
        exact S.sOrient_edgeDir_nonneg i (i + 1) j (S.turn_support i j)
      strict_nonincident := fun i j hji hjip => by
        simp only [vertexLink_apply]
        exact S.sOrient_edgeDir_pos i (i + 1) j (S.turn_strict i j hji hjip)
      open_hemisphere := by
        obtain ⟨h, hh, hpos⟩ := S.open_hemi
        exact ⟨h, hh, fun i => by
          simpa only [vertexLink_apply] using S.inner_h_edgeDir_pos i (hpos i)⟩ }



/-- The spherical side length of the link equals `arccos` of the inner product of the two link unit
directions. -/
theorem sideLen_vertexLink_eq_iAngle (i : Fin S.n) :
    sideLen S.vertexLink i
      = InnerProductGeometry.angle (S.edgeDir i.castSucc : E3) (S.edgeDir i.succ : E3) := by
  -- sideLen = sDist (edgeDir castSucc) (edgeDir succ) = arccos (sInner …)
  unfold sideLen
  rw [vertexLink_apply, vertexLink_apply]
  rw [sDist, InnerProductGeometry.angle]
  congr 1
  -- sInner = ⟪·,·⟫ ; and ‖edgeDir‖ = 1 so the denominator is 1
  rw [sInner]
  rw [S2.norm_coe, S2.norm_coe, mul_one, div_one]

/-- **Bridge A.**  The link side length is the Euclidean angle at the apex between the two incident
neighbours.  Here `i.castSucc` and `i.succ = i.castSucc + 1` are consecutive neighbour indices. -/
theorem sideLen_vertexLink (i : Fin S.n) :
    sideLen S.vertexLink i
      = EuclideanGeometry.angle (S.p i.castSucc) S.o (S.p i.succ) := by
  rw [sideLen_vertexLink_eq_iAngle]
  -- edgeDir = (positive scalar) • rawDir, and rawDir k = p k - o = p k -ᵥ o
  rw [edgeDir_coe, edgeDir_coe]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (S.inv_norm_pos _),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (S.inv_norm_pos _)]
  -- rawDir k = p k - o = p k -ᵥ o
  show InnerProductGeometry.angle (S.rawDir i.castSucc) (S.rawDir i.succ) = _
  rw [EuclideanGeometry.angle]
  rfl

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







/-- The lower index `⟨i.val, _⟩ : Fin (S.n + 1)` of the consecutive triple at internal joint `i`. -/
def jIdx0 (i : Fin (S.n - 1)) : Fin (S.n + 1) := ⟨i.val, by have := i.isLt; omega⟩
/-- The middle index `⟨i.val + 1, _⟩ : Fin (S.n + 1)` (the dihedral edge). -/
def jIdx1 (i : Fin (S.n - 1)) : Fin (S.n + 1) := ⟨i.val + 1, by have := i.isLt; omega⟩
/-- The upper index `⟨i.val + 2, _⟩ : Fin (S.n + 1)`. -/
def jIdx2 (i : Fin (S.n - 1)) : Fin (S.n + 1) := ⟨i.val + 2, by have := i.isLt; omega⟩

/-- **The extrinsic dihedral angle** of the star `S` along the middle edge `o → p ⟨i+1⟩` of the
consecutive triple `⟨i⟩, ⟨i+1⟩, ⟨i+2⟩`.  Defined directly from the ℝ³ data, mirroring
`TetDihedral.dihedralAngle`: project the two outer raw edge vectors `p ⟨i⟩ - o` and `p ⟨i+2⟩ - o`
onto the plane perpendicular to the middle raw edge direction `p ⟨i+1⟩ - o`, and take the angle.

This is *independent* of the spherical link `vertexLink`; Bridge B (`jointAngle_vertexLink_eq_dihedral`)
identifies it with the link's `jointAngle`. -/
def dihedral (i : Fin (S.n - 1)) : ℝ :=
  InnerProductGeometry.angle
    (projOut (S.rawDir (S.jIdx1 i)) (S.rawDir (S.jIdx0 i)))
    (projOut (S.rawDir (S.jIdx1 i)) (S.rawDir (S.jIdx2 i)))







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

/-- Cyclic list agreement up to orientation reversal. -/
def DihedralRotated {α : Type*} (l m : List α) : Prop :=
  l ~r m ∨ l.reverse ~r m

end List



/-- The two-valued bijection `true ↦ plus`, `false ↦ minus`. -/
def boolToStrict : Bool → StrictEdgeSign
  | true => StrictEdgeSign.plus
  | false => StrictEdgeSign.minus

theorem boolToStrict_inj : Function.Injective boolToStrict := by
  intro a b h; cases a <;> cases b <;> simp_all [boolToStrict]

/-- The real-sign map into `EdgeSign`, matching `nzSigns`' `0 < d ↦ plus`, `d < 0 ↦ minus`,
`d = 0 ↦ zero` convention. -/
def realSignToEdgeSign (x : ℝ) : EdgeSign :=
  if 0 < x then EdgeSign.plus else if x < 0 then EdgeSign.minus else EdgeSign.zero

theorem realSignToEdgeSign_eq_zero_iff (x : ℝ) : realSignToEdgeSign x = EdgeSign.zero ↔ x = 0 := by
  unfold realSignToEdgeSign
  rcases lt_trichotomy x 0 with h | h | h
  · simp only [not_lt.mpr h.le, if_false, h, if_true]
    constructor <;> intro h' <;> first | exact absurd h' (by decide) | (rw [h'] at h; exact absurd h (lt_irrefl 0))
  · simp [h]
  · simp only [h, if_true]
    constructor <;> intro h' <;> first | exact absurd h' (by decide) | (rw [h'] at h; exact absurd h (lt_irrefl 0))

theorem toStrict_realSign_of_ne (x : ℝ) (hx : x ≠ 0) :
    (realSignToEdgeSign x).toStrict = some (boolToStrict (decide (0 < x))) := by
  unfold realSignToEdgeSign
  rcases lt_trichotomy x 0 with h | h | h
  · have hnp : ¬ (0 < x) := not_lt.mpr h.le
    simp only [hnp, if_false, h, if_true]
    simp [EdgeSign.toStrict, boolToStrict]
  · exact absurd h hx
  · simp only [h, if_true]
    simp [EdgeSign.toStrict, boolToStrict]

theorem toStrict_realSign_of_zero {x : ℝ} (hx : x = 0) :
    (realSignToEdgeSign x).toStrict = none := by
  subst hx; simp [realSignToEdgeSign, EdgeSign.toStrict]

/-- `flips` of a Bool list with its cyclic closer `[first]` appended equals `flipAux` of the mapped
list (single structural induction). -/
theorem flips_append_eq_flipAux (first : Bool) :
    ∀ (prev : Bool) (t : List Bool),
      flips ((prev :: t) ++ [first])
        = flipAux (boolToStrict first) (boolToStrict prev) (t.map boolToStrict)
  | prev, [] => by
      simp only [List.nil_append, List.cons_append, List.map_nil, flips, flipAux]
      by_cases h : prev = first
      · simp [h]
      · simp only [ne_eq, h, not_false_eq_true, if_pos]
        rw [if_pos]
        intro hc; exact h (boolToStrict_inj hc)
  | prev, x :: t => by
      have ih := flips_append_eq_flipAux first x t
      simp only [List.cons_append, List.map_cons, flips, flipAux] at *
      rw [ih]
      by_cases h : prev = x
      · simp [h]
      · rw [if_pos h, if_pos]
        intro hc; exact h (boolToStrict_inj hc)

/-- The Bool-based cyclic flip count equals the `StrictEdgeSign`-based one under `boolToStrict`. -/
theorem cyclicFlips_eq_cyclicFlipCount_map (bs : List Bool) :
    cyclicFlips bs = cyclicFlipCount (bs.map boolToStrict) := by
  cases bs with
  | nil => simp [cyclicFlips, cyclicFlipCount]
  | cons h t =>
      show flips ((h :: t) ++ [h]) = cyclicFlipCount ((h :: t).map boolToStrict)
      rw [flips_append_eq_flipAux h h t]
      simp only [List.map_cons, cyclicFlipCount]

theorem filter_map_eq_filterMap {β γ : Type*} (p : β → Bool) (g : β → γ) :
    ∀ (L : List β),
      (L.filter p).map g = L.filterMap (fun a => if p a then some (g a) else none)
  | [] => by simp
  | a :: L => by
      simp only [List.filter_cons, List.filterMap_cons]
      by_cases h : p a
      · simp [h, filter_map_eq_filterMap p g L]
      · simp [h, filter_map_eq_filterMap p g L]

/-- Both machineries skip zeros identically: `(nzSigns d).map boolToStrict` is the strict
sub-sequence of `(List.ofFn d).map realSignToEdgeSign`. -/
theorem nzSigns_map_boolToStrict {m : ℕ} (d : Fin m → ℝ) :
    (nzSigns d).map boolToStrict
      = ((List.ofFn d).map realSignToEdgeSign).filterMap EdgeSign.toStrict := by
  rw [List.ofFn_eq_map, List.map_map, List.filterMap_map]
  unfold nzSigns
  rw [List.map_map, filter_map_eq_filterMap]
  apply List.filterMap_congr
  intro i _
  simp only [Function.comp_apply]
  by_cases hi : d i = 0
  · rw [if_neg (by simp [hi]), toStrict_realSign_of_zero hi]
  · rw [if_pos (by simp [hi]), toStrict_realSign_of_ne (d i) hi]

/-- **The count-reconciliation identity (local copy).** -/
theorem cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros {m : ℕ} (d : Fin m → ℝ) :
    cyclicFlips (nzSigns d)
      = cyclicFlipCountSkipZeros ((List.ofFn d).map realSignToEdgeSign) := by
  rw [cyclicFlips_eq_cyclicFlipCount_map, cyclicFlipCountSkipZeros_eq_strict,
    nzSigns_map_boolToStrict]



/-- The cyclic adjacency indicator sum: `1` for each cyclically adjacent unequal pair. -/
def cyclicSum {α : Type*} [DecidableEq α] (l : List α) : ℕ :=
  (List.zipWith (fun a b => if a ≠ b then 1 else 0) l (l.rotate 1)).sum

/-- `cyclicFlipCount` equals the cyclic adjacency sum (`flipAux` telescopes into the zipWith sum). -/
theorem cyclicFlipCount_eq_cyclicSum {α : Type*} [DecidableEq α] (l : List α) :
    cyclicFlipCount l = cyclicSum l := by
  cases l with
  | nil => simp [cyclicFlipCount, cyclicSum]
  | cons h t =>
    simp only [cyclicSum, List.rotate_cons_succ, List.rotate_zero, cyclicFlipCount]
    -- General: flipAux h p xs = sum (zipWith f (p::xs) (xs ++ [h]))
    have key : ∀ (p : α) (xs : List α),
        flipAux h p xs
          = (List.zipWith (fun a b => if a ≠ b then 1 else 0) (p :: xs) (xs ++ [h])).sum := by
      intro p xs
      induction xs generalizing p with
      | nil => simp [flipAux]
      | cons a xs ih =>
        simp only [flipAux, List.cons_append, List.zipWith_cons_cons, List.sum_cons]
        rw [ih a]
    rw [key h t]

/-- `List.sum` is invariant under rotation (rotation is a permutation). -/
theorem sum_rotate {α : Type*} [AddCommMonoid α] (l : List α) (n : ℕ) :
    (l.rotate n).sum = l.sum :=
  (List.rotate_perm l n).sum_eq

/-- The cyclic adjacency sum is invariant under one rotation. -/
theorem cyclicSum_rotate_one {α : Type*} [DecidableEq α] (l : List α) :
    cyclicSum (l.rotate 1) = cyclicSum l := by
  unfold cyclicSum
  rw [← List.zipWith_rotate_distrib (fun a b => if a ≠ b then 1 else 0) l (l.rotate 1) 1
      (List.length_rotate l 1).symm, sum_rotate]

/-- `cyclicFlipCount` is invariant under one rotation. -/
theorem cyclicFlipCount_rotate_one {α : Type*} [DecidableEq α] (l : List α) :
    cyclicFlipCount (l.rotate 1) = cyclicFlipCount l := by
  rw [cyclicFlipCount_eq_cyclicSum, cyclicFlipCount_eq_cyclicSum, cyclicSum_rotate_one]

/-- `cyclicFlipCount` is invariant under any rotation. -/
theorem cyclicFlipCount_rotate {α : Type*} [DecidableEq α] (l : List α) (k : ℕ) :
    cyclicFlipCount (l.rotate k) = cyclicFlipCount l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show l.rotate (k + 1) = (l.rotate k).rotate 1 by rw [List.rotate_rotate]]
    rw [cyclicFlipCount_rotate_one, ih]

/-- `cyclicFlipCount` is invariant under `IsRotated`. -/
theorem cyclicFlipCount_of_isRotated {α : Type*} [DecidableEq α] {l l' : List α}
    (h : l ~r l') : cyclicFlipCount l = cyclicFlipCount l' := by
  obtain ⟨k, rfl⟩ := h
  exact (cyclicFlipCount_rotate l k).symm

/-- `filterMap` of a singly-rotated list is a rotation of `filterMap` of the list. -/
theorem filterMap_rotate_one_isRotated {α β : Type*} (f : α → Option β) (l : List α) :
    (l.rotate 1).filterMap f ~r l.filterMap f := by
  cases l with
  | nil => simp
  | cons h t =>
    rw [List.rotate_cons_succ, List.rotate_zero, List.filterMap_append, List.filterMap_cons]
    -- (t.filterMap f) ++ (f h).toList? vs (f h).toList? ++ t.filterMap f  — a rotation
    rw [List.filterMap_cons]
    -- goal: (t.filterMap f ++ Option.toList' (f h)) ~r (match f h with ... )
    cases hf : f h with
    | none => simp [List.IsRotated.refl]
    | some b =>
      simp only [List.filterMap_nil]
      have := List.isRotated_append (l := t.filterMap f) (l' := [b])
      simpa using this

/-- `filterMap` is invariant-up-to-rotation under rotation of its source. -/
theorem filterMap_rotate_isRotated {α β : Type*} (f : α → Option β) (l : List α) (k : ℕ) :
    (l.rotate k).filterMap f ~r l.filterMap f := by
  induction k with
  | zero => simp [List.IsRotated.refl]
  | succ k ih =>
    rw [show l.rotate (k + 1) = (l.rotate k).rotate 1 by rw [List.rotate_rotate]]
    exact (filterMap_rotate_one_isRotated f (l.rotate k)).trans ih

/-- `filterMap` carries `IsRotated` to `IsRotated`. -/
theorem filterMap_isRotated {α β : Type*} {l l' : List α} (f : α → Option β) (h : l ~r l') :
    l.filterMap f ~r l'.filterMap f := by
  obtain ⟨k, rfl⟩ := h
  exact (filterMap_rotate_isRotated f l k).symm

/-- **`cyclicFlipCountSkipZeros` is invariant under `IsRotated`.**  Rotating the cyclic sign list
leaves the skip-zeros cyclic flip count unchanged. -/
theorem cyclicFlipCountSkipZeros_of_isRotated {l l' : List EdgeSign} (h : l ~r l') :
    cyclicFlipCountSkipZeros l = cyclicFlipCountSkipZeros l' := by
  unfold cyclicFlipCountSkipZeros
  exact cyclicFlipCount_of_isRotated (filterMap_isRotated EdgeSign.toStrict h)

theorem filterMap_reverse {α β : Type*} (f : α → Option β) :
    ∀ l : List α, l.reverse.filterMap f = (l.filterMap f).reverse
  | [] => by simp
  | a :: t => by
      simp only [List.reverse_cons, List.filterMap_append, filterMap_reverse f t,
        List.filterMap_cons, List.filterMap_nil]
      cases f a <;> simp

 theorem zipWith_append_eq {α β γ : Type*} (f : α → β → γ) :
    ∀ {l₁ : List α} {l₂ : List β} (r₁ : List α) (r₂ : List β),
      l₁.length = l₂.length →
        List.zipWith f (l₁ ++ r₁) (l₂ ++ r₂) =
          List.zipWith f l₁ l₂ ++ List.zipWith f r₁ r₂
  | [], [], r₁, r₂, _ => by rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, r₁, r₂, h => by
      have ht : as.length = bs.length := Nat.succ.inj h
      simp only [List.cons_append, List.zipWith_cons_cons, List.cons.injEq, true_and]
      exact zipWith_append_eq f r₁ r₂ ht

 theorem zipWith_reverse_eq {α β γ : Type*} (f : α → β → γ) :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (List.zipWith f l₁ l₂).reverse = List.zipWith f l₁.reverse l₂.reverse
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
      have ht : as.length = bs.length := Nat.succ.inj h
      simp only [List.zipWith_cons_cons, List.reverse_cons]
      rw [zipWith_reverse_eq f ht]
      rw [zipWith_append_eq f [a] [b] (by simpa [List.length_reverse] using ht)]
      simp

 theorem zipWith_comm_of_comm_eq {α γ : Type*} (f : α → α → γ)
    (hf : ∀ a b, f a b = f b a) :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length →
      List.zipWith f l₁ l₂ = List.zipWith f l₂ l₁
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
      have ht : as.length = bs.length := Nat.succ.inj h
      simp [hf a b, zipWith_comm_of_comm_eq f hf ht]

theorem cyclicFlipCount_reverse {α : Type*} [DecidableEq α] (l : List α) :
    cyclicFlipCount l.reverse = cyclicFlipCount l := by
  rw [cyclicFlipCount_eq_cyclicSum, cyclicFlipCount_eq_cyclicSum]
  unfold cyclicSum
  let f : α → α → ℕ := fun a b => if a ≠ b then 1 else 0
  have hfcomm : ∀ a b, f a b = f b a := by
    intro a b
    by_cases h : a = b
    · simp [f, h]
    · have hba : b ≠ a := fun hb => h hb.symm
      simp [f, h, hba]
  let k := l.length - 1 % l.length
  rw [List.rotate_reverse]
  change (List.zipWith f l.reverse ((l.rotate k).reverse)).sum =
    (List.zipWith f l (l.rotate 1)).sum
  rw [← zipWith_reverse_eq f (by rw [List.length_rotate]), List.sum_reverse,
    zipWith_comm_of_comm_eq f hfcomm (by rw [List.length_rotate])]
  have hlen : (l.rotate k).length = l.length := List.length_rotate l k
  have hzip := List.zipWith_rotate_distrib f l (l.rotate 1) k
    (by rw [List.length_rotate])
  have hrot : (l.rotate 1).rotate k = l := by
    by_cases hnil : l = []
    · subst hnil
      simp [k]
    · have hlenpos : 0 < l.length := Nat.pos_of_ne_zero (by
        intro hlen0
        exact hnil (List.eq_nil_of_length_eq_zero hlen0))
      rw [List.rotate_rotate]
      unfold k
      by_cases hlen1 : l.length = 1
      · have hmod : 1 % l.length = 0 := by simp [hlen1]
        rw [hmod]
        have hsum : 1 + (l.length - 0) = l.length * 2 := by omega
        rw [hsum, List.rotate_length_mul]
      · have hlt : 1 < l.length := by omega
        have hmod : 1 % l.length = 1 := Nat.mod_eq_of_lt hlt
        rw [hmod]
        have hsum : 1 + (l.length - 1) = l.length := by omega
        rw [hsum, List.rotate_length]
  calc
    (List.zipWith f (l.rotate k) l).sum
        = (List.zipWith f (l.rotate k) ((l.rotate 1).rotate k)).sum := by rw [hrot]
    _ = ((List.zipWith f l (l.rotate 1)).rotate k).sum := by rw [hzip]
    _ = (List.zipWith f l (l.rotate 1)).sum := sum_rotate _ _

theorem cyclicFlipCountSkipZeros_reverse (l : List EdgeSign) :
    cyclicFlipCountSkipZeros l.reverse = cyclicFlipCountSkipZeros l := by
  unfold cyclicFlipCountSkipZeros
  rw [filterMap_reverse]
  exact cyclicFlipCount_reverse _

theorem cyclicFlipCountSkipZeros_of_dihedralRotated {l m : List EdgeSign}
    (h : List.DihedralRotated l m) :
    cyclicFlipCountSkipZeros l = cyclicFlipCountSkipZeros m := by
  rcases h with hrot | hrev
  · exact cyclicFlipCountSkipZeros_of_isRotated hrot
  · calc
      cyclicFlipCountSkipZeros l
          = cyclicFlipCountSkipZeros l.reverse := (cyclicFlipCountSkipZeros_reverse l).symm
      _ = cyclicFlipCountSkipZeros m := cyclicFlipCountSkipZeros_of_isRotated hrev



/-- **σ-orbit invariance of the per-vertex flip count.**  Two darts in the same `σ`-orbit have the
same `vertexFlipCountSkipZeros`, because their `σ`-`toList`s are rotations of each other. -/
theorem vertexFlipCountSkipZeros_sameCycle (M : CombMap D) (es : D → EdgeSign) {d d' : D}
    (h : M.σ.SameCycle d d') :
    vertexFlipCountSkipZeros M es d = vertexFlipCountSkipZeros M es d' := by
  unfold vertexFlipCountSkipZeros vertexSignList
  exact cyclicFlipCountSkipZeros_of_isRotated
    ((h.toList_isRotated).map es)



/-- The `Q`-realization link at vertex `Q`, reindexed onto `Fin ((starP Q).n + 1)` via the
degree-match `deg_eq`.  (Both links have the same number of edges, `vertexDeg`.) -/
@[reducible] def linkQcast (M : CombMap D) (starP starQ : M.Vertex → VertexStar)
    (hnn : ∀ Q, (starQ Q).n = (starP Q).n) (Q : M.Vertex) :
    Fin ((starP Q).n + 1) → S2 :=
  fun i => (starQ Q).vertexLink (Fin.cast (by rw [hnn Q]) i)

/-- **The faithful convex-polytope realization interface.**

Two congruent-faced convex-vertex realizations `P, Q` of the same triangulated-sphere combinatorial map
`M`, presented as a per-vertex family of vertex stars whose links agree on side lengths (congruent
faces) and closing chord, together with the **order bridge** `linkOrder` (the σ-dart order carries the
geometric link order) and the per-vertex two-arc datum `twoArc` (the single isolated geometric residual,
exactly as in `Ch13ArmVertexFull`).

There is **no `active` field**: rigidity is unconditional. -/
structure ConvexPolytopeRealization (M : CombMap D) where
  /-- `M` is a triangulated sphere. -/
  isSphere : M.IsSphereMap
  triangle : M.FaceRegular 3
  /-- The edge graph is simple (no loops / no parallel edges) — a genuine property of every convex
  3-polytope's boundary graph (Steinitz), supplied by the ℝ³ realization.  It is what rules out the
  digon degeneracy in the combinatorial low-active-vertex lemma. -/
  isSimple : M.IsSimpleGraph
  /-- The `P`-realization vertex star at each vertex. -/
  starP : M.Vertex → VertexStar
  /-- The `Q`-realization vertex star at each vertex. -/
  starQ : M.Vertex → VertexStar
  /-- Both realizations have the same incident-edge count at each vertex (degree match). -/
  hnn : ∀ (Q : M.Vertex), (starQ Q).n = (starP Q).n
  /-- The per-edge dihedral-difference signing: `edgeSign d = sign(dihedral_Q − dihedral_P)` at the
  edge of `d`.  Edge-invariant (`α`-stable): both darts of an edge carry the same sign. -/
  edgeSign : D → EdgeSign
  edgeSign_inv : ∀ d, edgeSign (M.α d) = edgeSign d
  /-- Congruent faces: corresponding link side lengths agree. -/
  sides_eq : ∀ (Q : M.Vertex) (i : Fin (starP Q).n),
      sideLen (starP Q).vertexLink i = sideLen (linkQcast M starP starQ hnn Q) i
  /-- Shared closing chord at each vertex. -/
  close_eq : ∀ (Q : M.Vertex),
      sDist ((starP Q).vertexLink 0) ((starP Q).vertexLink (Fin.last (starP Q).n))
        = sDist ((linkQcast M starP starQ hnn Q) 0)
            ((linkQcast M starP starQ hnn Q) (Fin.last (starP Q).n))
  /-- A representative dart at each vertex (`tail = Q`). -/
  dartRep : M.Vertex → D
  dartRep_tail : ∀ (Q : M.Vertex), M.tail (dartRep Q) = Q
  /-- **Interior activeness bridge.**  When some incident edge at `Q` carries a nonzero dihedral-change
  sign, some *interior* joint of the link genuinely differs.  This is the geometric input feeding the
  arm lemma's strict witness (closing angles are determined by the equal sides/chord; only the interior
  joints are the free Cauchy variables).  It is an interface field exactly like `twoArc`; it does **not**
  make rigidity conditional (the conclusion of `realization_rigid` is unconditional). -/
  interiorActive : ∀ (Q : M.Vertex),
      ActiveVertex M edgeSign (dartRep Q) →
        ∃ i : Fin ((starP Q).n - 1),
          jointAngle (starP Q).vertexLink i ≠ jointAngle (linkQcast M starP starQ hnn Q) i
  /-- The per-vertex two-arc split datum for the `signChangesFull = 2` case (the single isolated
  geometric residual, exactly as `Ch13ArmVertexFull.cauchyArmVertexFull_of_links` takes). -/
  twoArc : ∀ (Q : M.Vertex),
      signChangesFull (starP Q).vertexLink (linkQcast M starP starQ hnn Q) = 2 →
        TwoArcSplitData (starP Q).vertexLink (linkQcast M starP starQ hnn Q)
  /-- **The order bridge (`linkOrder`).**  The `σ`-ordered list of edge signs around vertex `Q` (read
  from `dartRep Q`) agrees with the link-ordered real-sign list of the dihedral differences up to
  cyclic rotation and reversal.  This is the honest unoriented cyclic-order bridge; positing
  `vertexArm_signChanges_eq` directly instead is the §3.3 trap. -/
  linkOrder : ∀ (Q : M.Vertex),
      List.DihedralRotated
        ((M.σ.toList (dartRep Q)).map edgeSign)
        ((List.ofFn
          (linkDiff (starP Q).vertexLink (linkQcast M starP starQ hnn Q))).map realSignToEdgeSign)









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








namespace ConvexEuclideanPolyhedron











end ConvexEuclideanPolyhedron



































































































































































namespace ListCyclicOrder



















end ListCyclicOrder

















































































































namespace RotTwoBlockCert




























end RotTwoBlockCert








































































































































end ProofsInTheBook.Ch13Cauchy3D

end
end


