-- Prove2me | Theorems.Thm_Hirsch_row_circuit_step_adj_of_common_face_dim_le_one
-- name    : Hirsch.row_circuit_step_adj_of_common_face_dim_le_one
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T23:25:43.661111+00:00
-- url     : https://prove2.me/theorems/f8d8878c-aaf0-4b1e-8b93-904e25be3871
-- title:
--   A one-dimensional common face makes a maximal circuit step an edge
-- statement:
--   A maximal row-circuit step leaving a vertex is an ordinary graph edge whenever the common face of its endpoints has dimension at most one.
--
--   Let $P\subseteq\mathbb{R}^d$ be an H-polytope cut out by $n$ linear inequalities, and let $x$ be a vertex of $P$. Suppose $y\in P$ is obtained from $x$ by a maximal feasible row-circuit augmentation: the displacement $y-x$ has inclusion-minimal row support among nonzero directions, and no strictly longer step in that direction remains feasible. Write $F(x,y)$ for the face of $P$ cut out by every nonzero describing row tight at both $x$ and $y$, and write $h$ for the dimension of the corresponding common-direction space. If
--
--   $$
--   h\le 1,
--   $$
--
--   then the segment $[x,y]$ is a one-dimensional face of $P$, so $x$ and $y$ are adjacent in the vertex-edge graph.
--
--   The destination $y$ is not assumed to be a vertex in advance: adjacency itself produces an extreme segment, so both endpoints are vertices. The hypothesis $h\le 1$ forces $F(x,y)$ to lie on the affine line through $x$ and $y$; maximality of the circuit step then cuts that line down to the segment. This is a local sufficient criterion. It does not assert that every circuit step has a one-dimensional carrier, and it does not bound the graph diameter of a higher-dimensional common face.
--
--   **Formalization Note** The Lean statement uses the public common-face vocabulary `HirschCommonFace.commonFaceDim` together with `RowCircuitStep` from the circuit model. No irredundancy, strict feasibility, or boundedness hypothesis is required.
-- source:
--   Verified carrier-to-edge geometry for the Polynomial Hirsch mission; kernel-checked source Solutions/PolynomialCircuitCarrierEdge.lean at commit 71efbbcb66528871c0ff0508fe6b31b6c1b7b646, GitHub Actions run 34533747844. Integrated on main by PR #63 (merge 0e0ab59507f4508ee5001ead7f65a97fff875db6). Standard polyhedral fact: a one-dimensional face is an edge. No literature-priority claim.

import Definitions.Def_Hirsch_circuit_model
import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem row_circuit_step_adj_of_common_face_dim_le_one
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Set.extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hdim : HirschCommonFace.commonFaceDim a b x y ≤ 1) :
    Adj (Hpoly a b) x y := by sorry

end Hirsch
