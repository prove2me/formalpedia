-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_edge_augmentation__p2m_5d6c09bb_0ad5_47bc_b88e_37408079b780_a1
-- name    : WilliamsonShmoys.planar_disconnected_edge_augmentation__p2m_5d6c09bb_0ad5_47bc_b88e_37408079b780_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:50:33.275811+00:00
-- url     : https://prove2.me/theorems/1efa1232-6c19-4874-b61b-a7d00db43bc9
-- title:
--   A disconnected planar graph admits a drawable edge augmentation
-- statement:
--   For a finite ordered vertex type with at least two vertices, any disconnected graph with a planar drawing has a planar drawing on the same vertex set with strictly more edges. The child packages the topological step of joining components by a new noncrossing edge; the parent then contradicts edge-count maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_edge_augmentation__p2m_5d6c09bb_0ad5_47bc_b88e_37408079b780_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj)
    (hcard : 2 ≤ Fintype.card V)
    (hQ : HasPlanarDrawingOn Q)
    (hdis : ¬ Q.Connected) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K ∧
      (letI : DecidableRel Q.Adj := dQ
       letI : DecidableRel K.Adj := dK
       Q.edgeFinset.card < K.edgeFinset.card) := by sorry
