-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:02:23.487292+00:00
-- url     : https://prove2.me/theorems/81a66f1a-c43a-4a7b-acaa-fb78b3cc2417
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite planar graph on at least three vertices has a same-vertex-type planar supergraph maximal under graph inclusion. This removes the finite-choice obligation from the parent: maximize the edge count in the nonempty finite family of planar supergraphs containing N, so any strict planar extension would contradict that maximum. The hcard boundary is harmless, and the proof route also works at three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6467164a_4ac7_4202_bbd8_0cd7677d3ce4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      And (N <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H)
          (forall K : SimpleGraph V,
            H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)) := by sorry
