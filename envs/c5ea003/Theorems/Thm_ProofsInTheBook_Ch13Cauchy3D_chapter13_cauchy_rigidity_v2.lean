-- Prove2me | Theorems.Thm_ProofsInTheBook_Ch13Cauchy3D_chapter13_cauchy_rigidity_v2
-- name    : ProofsInTheBook.Ch13Cauchy3D.chapter13_cauchy_rigidity_v2
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T21:08:29.902742+00:00
-- url     : https://prove2.me/theorems/b6d37a4e-dbc4-4c15-b8f3-2dd42ee7f1af
-- title:
--   Dihedral-angle equality for congruent-faced convex triangulated realizations
-- statement:
--   Let D be a finite dart type with decidable equality and let M be a combinatorial map, with permutations alpha and sigma, where alpha is a fixed-point-free involution and the face permutation is $\varphi=\sigma\circ\alpha$. Vertices, edges and faces are the respective sigma-, alpha- and phi-orbits. Assume M is connected in the dart-step sense and its integer Euler characteristic is 2. Assume all face orbits have length 3, there are no loops or parallel edges, and every vertex has at least three incident darts.
--
--   Let P and Q be two realizations on this same map. Each assigns a point $x_v\in\mathbb R^3$ to every vertex, a representative dart for each face, and the three face vertices in phi-order from that representative. Every edge has distinct endpoint positions and every face triple is affinely independent. Each realization also supplies a point $a_f$ and a normal $N_f$ for each face, satisfying
--   $$\langle N_f,x_{f,i}-a_f\rangle=0,\qquad\langle N_f,x_v-a_f\rangle\leq0$$
--   for every face corner and every vertex, respectively, with strict inequality for every vertex not among that face's three combinatorial corners. For every dart d there must be a positive real lambda such that
--   $$N_{[d]_\varphi}=\lambda\bigl(x_{\mathrm{tail}(\varphi^2d)}-x_{\mathrm{tail}(d)}\bigr)\times\bigl(x_{\mathrm{tail}(\varphi d)}-x_{\mathrm{tail}(d)}\bigr).$$
--   All of these data and conditions are supplied by each ConvexEuclideanPolyhedron input. Suppose the lengths of corresponding edges agree in P and Q for every dart.
--
--   At any vertex v, construct the two vertex stars from the reverse-sigma cyclic order of neighboring vertices and rotate both by the common adaptive offset specified in the source. This offset is chosen using a dart with nonzero dihedral-difference sign when one exists, and a representative dart otherwise. Write the resulting stars as $S_P,S_Q$, with the same number $n_v+1$ of neighbors and $n_v\geq2$. Then for every $i\in\{0,\ldots,n_v-2\}$,
--   $$\operatorname{dihedral}(S_P,i)=\operatorname{dihedral}(S_Q,i).$$
--   Here the angle at index i is the ordinary unoriented angle between the projections of the raw neighbor vectors at indices i and i+2 onto the plane perpendicular to the raw vector at index i+1. The equality uses the natural identification of the two finite index sets.
--
--   This is the stated equality of the internal angles of the adaptively rerooted vertex stars. The declaration does not conclude the existence of a global Euclidean isometry taking P to Q, and does not take arbitrary polygon-faced polyhedra as input. Face congruence is encoded by corresponding dart-edge lengths; no separate two-arc cut or vertex-link certificate is an argument of this endpoint.
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
import Definitions.Def_P2MAssembly_Chapter13V2

set_option autoImplicit true
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

theorem ProofsInTheBook.Ch13Cauchy3D.chapter13_cauchy_rigidity_v2
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
              (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w) v).symm) i) := by sorry
