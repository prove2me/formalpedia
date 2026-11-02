-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edgeCount__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
-- name    : WilliamsonShmoys.maximalPlanarDrawingOn_edgeCount__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:46.835297+00:00
-- url     : https://prove2.me/theorems/6ad3e488-df98-4029-b402-def6549b4337
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A planar graph on at least three vertices that is maximal under planar edge inclusion has exactly 3|V|−6 edges. This isolates the topological work from the finite maximization in the first child. A proof route is to use a planar embedding, show maximality forces connectedness and triangular faces (including the three-vertex boundary case), then combine Euler’s formula with the face-edge incidence count. The remaining core obligation is to connect the target’s arc-based drawing witness to this triangulation argument while preserving the maximality and vertex-count hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarDrawingOn_edgeCount__p2m_e8d3fd6d_990f_43df_873b_df1b4f477345_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      HasPlanarDrawingOn L →
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel L.Adj := dL
       K.edgeFinset ⊆ L.edgeFinset → L.edgeFinset ⊆ K.edgeFinset)) :
    (letI : DecidableRel K.Adj := dK
     K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
