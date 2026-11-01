-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_bridge_iteration__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a2
-- name    : WilliamsonShmoys.finite_planar_bridge_iteration__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:11.319086+00:00
-- url     : https://prove2.me/theorems/5d530b65-2a84-4113-95c6-4b4a03a3063e
-- title:
--   Iterate planar bridges to connect a finite graph
-- statement:
--   For a finite vertex type of size at least three, if every disconnected planar supergraph of G can be extended to a planar supergraph by adding an edge between previously unreachable vertices, then G has a connected planar supergraph containing G. The cardinality hypothesis is retained for the bridge step; the iteration itself terminates because each such edge strictly increases the finite edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_planar_bridge_iteration__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hstep : ∀ (K : SimpleGraph V),
      G.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet ∧
        (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
        HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
