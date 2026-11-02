-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a2
-- name    : WilliamsonShmoys.exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:54:02.445205+00:00
-- url     : https://prove2.me/theorems/711af4b4-5214-45eb-bc71-e82c24cc238b
-- title:
--   A finite planar drawing with at least three vertices has a connected planar supergraph
-- statement:
--   Every graph on a finite ordered vertex type with at least three vertices that has a crossing-free drawing has a connected planar supergraph on the same vertex type. The lower bound ensures the vertex type is nonempty and excludes the empty-type counterexample to the earlier child. To prove the lemma, join components by arcs in the complement of the drawing, preserving the stated endpoint and intersection conditions, until the graph is connected. The substantive remaining obligation is formalizing this construction for the exact `HasPlanarDrawingOn` definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_planar_supergraph__p2m_5587bd77_cdbe_4d4a_9ac4_bb8e9f059500_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    Exists fun P : SimpleGraph V =>
      N <= P /\ P.Connected /\ WilliamsonShmoys.HasPlanarDrawingOn P := by sorry
