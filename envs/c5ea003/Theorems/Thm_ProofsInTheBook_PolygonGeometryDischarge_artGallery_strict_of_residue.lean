-- Prove2me | Theorems.Thm_ProofsInTheBook_PolygonGeometryDischarge_artGallery_strict_of_residue
-- name    : ProofsInTheBook.PolygonGeometryDischarge.artGallery_strict_of_residue
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T18:32:04.485326+00:00
-- url     : https://prove2.me/theorems/5c7565f2-6ed2-4100-a4b8-c71001e15cd2
-- title:
--   Conditional vertex-guard bound from uniform geometry and attachment data
-- statement:
--   Let $n\in\mathbb N$ and $P=(q_0,\ldots,q_{n-1})$ be a strict simple polygon in $\mathbb R^2$: $n\ge3$, the vertices are distinct, consecutive triples are noncollinear, adjacent closed edges meet only at their common endpoint, and nonadjacent edges are disjoint. Indices are cyclic. Let $r\in\mathbb R^2$ be nonzero and not parallel to any edge. For $x\in\mathbb R^2$, put $s_i=\det(r,q_i-x)$. Count an edge in $c_{P,r}(x)$ when its endpoints satisfy $(s_i\le0<s_{i+1})\lor(s_{i+1}\le0<s_i)$ and its intersection with the line $x+\mathbb Rr$ has nonnegative ray parameter. Define the closed region $K(P,r)$ to be the polygon boundary together with points for which $c_{P,r}(x)$ is odd. A point $g$ sees $x$ when the entire closed segment $[g,x]$ lies in $K(P,r)$.
--
--   Assume a uniform geometric-data assignment $\mathcal R$ with the following content for every strict simple polygon $Q$ of every order and every admissible ray direction $s$. It supplies a vertex $v$ whose closed adjacent triangle lies in $K(Q,s)$. It also supplies the following transversality conditions at $v$: if the adjacent triangle contains no other polygon vertices, the open segment joining the neighbors of $v$ avoids the polygon boundary; for each enclosed vertex maximizing the affine height $h(z)=\operatorname{orient}(q_{v-1},q_{v+1},z)/\operatorname{orient}(q_{v-1},q_{v+1},q_v)$ toward $v$, the open segment from $v$ to that vertex avoids the boundary. For every diagonal of $Q$ (a segment between distinct nonadjacent vertices, contained in $K(Q,s)$ and meeting the boundary only at its endpoints), $\mathcal R$ supplies strict-polygon noncollinearity and edge-intersection conditions for both cyclic-arc subpolygons, and admissible ray directions on both subpolygons whose vectors equal $s$. Write $K_L,K_R$ for their closed regions and $D$ for the diagonal. These data must satisfy: off all three polygon boundaries, $K_L$ and $K_R$ are disjoint; at every point on any of the three boundaries, membership in $K(Q,s)$ is equivalent to membership in $K_L\cup K_R$; and $K_L\cap K_R=D$. This is the full universally quantified input named PolygonGeomResidue, not a conclusion about an individual polygon.
--
--   Assume in addition the universal attachment condition $\mathcal M$, named DiagonalAttachInput for the fixed base-triangle certificate $B$ used in the declaration. For every order, strict polygon, admissible ray, local-cut-data package, and valid diagonal, and for every pair of child ear-triangulations with every pair of compatible combinatorial-glue certificates based on $B$, remap the child vertex indices into the parent. Let $A$ and $V_A$ be the left triangle family and its vertices. The supplied right inductive triangulation must satisfy AttachesTo: its initial triangle has an edge shared with a triangle of $A$ and a third vertex outside $V_A$; every later attachment vertex is also outside $V_A$. This condition applies to the supplied inductive triangulation itself; it does not merely assert that some reordering exists. The certificate $B$ is the fixed expression baseTriangleFacts_of_leaf(baseTriangleLeaf_of_atoms(triangleConvexLeaf_holds, triangleExteriorEven_unconditional)); it is not an additional freely quantified hypothesis.  Then there exists $G\subseteq\{0,\ldots,n-1\}$ such that
--   $$|G|\le\lfloor n/3\rfloor,\qquad\forall x\in K(P,r),\ \exists v\in G,\quad[q_v,x]\subseteq K(P,r).$$
--   This is a conditional art-gallery implication from the two uniform inputs. It neither constructs those inputs nor establishes that they are jointly satisfiable.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonGeometryDischarge.lean#L251 (headline); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonGeomInput.lean#L266 (uniform residue); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonOracleClose.lean#L270 (residual fields); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonLast.lean#L340 (universal attachment premise); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonLast.lean#L104 (attachment predicate); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonSubstrate.lean#L151 (strict polygon); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonSubstrate.lean#L205 (ray direction); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonSideCrossing.lean#L276 (closed region); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PolygonRayIndep.lean#L676 (visibility). Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 40, “How to guard a museum”, pp. 281–284 (https://doi.org/10.1007/978-3-662-57265-8_40).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter36Geometry
set_option autoImplicit true
open ProofsInTheBook.PolygonGeometryDischarge
open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)


open ProofsInTheBook.PolygonCutGeometry
  (PolygonGeometryInput  )
open ProofsInTheBook.PolygonFinish (UnconditionalRayIndepInput)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonRayIndep (Sees)
variable {n : ℕ}

theorem ProofsInTheBook.PolygonGeometryDischarge.artGallery_strict_of_residue {n : ℕ}
    (R : ProofsInTheBook.PolygonGeomInput.PolygonGeomResidue)
    (M : DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x := by sorry
