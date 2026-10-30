-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:37.893835+00:00
-- url     : https://prove2.me/theorems/ecf2311e-b31c-4b92-8561-385ce369da7c
-- title:
--   A maximal planar supergraph exists
-- statement:
--   Every planar graph on a finite vertex type is contained in a planar supergraph that is maximal under inclusion among planar supergraphs on the same vertex type. Finiteness makes this a finite maximization problem over all simple graphs on V; maximality is the property used by the parent to force connectivity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph__p2m_24141c0a_e101_43b3_b89f_9504b9363753_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
        ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L → L = H := by sorry
