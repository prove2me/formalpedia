-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_strict_supergraph_of_disconnected__p2m_0d71806b_1bff_4247_911b_0bb3ff02c978_a1
-- name    : WilliamsonShmoys.exists_planar_strict_supergraph_of_disconnected__p2m_0d71806b_1bff_4247_911b_0bb3ff02c978_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T11:59:19.538121+00:00
-- url     : https://prove2.me/theorems/7126cecb-c28a-4db7-af93-ede0b0cbea72
-- title:
--   A disconnected planar drawing admits a strict planar supergraph
-- statement:
--   Any disconnected graph on a finite linearly ordered vertex type with at least three vertices, if it has a crossing-free drawing, has a planar supergraph with strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_strict_supergraph_of_disconnected__p2m_0d71806b_1bff_4247_911b_0bb3ff02c978_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : LE.le 3 (Fintype.card V))
    (hdis : Not H.Connected) :
    Exists fun K : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (Set.Subset H.edgeSet K.edgeSet)
          (Not (K.edgeSet = H.edgeSet))) := by sorry
