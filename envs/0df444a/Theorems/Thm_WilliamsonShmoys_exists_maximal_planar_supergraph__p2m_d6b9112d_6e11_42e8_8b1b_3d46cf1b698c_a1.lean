-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:40.313067+00:00
-- url     : https://prove2.me/theorems/c0ec6b8f-fcbf-4b2c-8dba-71231ff2f6b6
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every drawable graph on the given finite vertex set has an inclusion-maximal drawable supergraph on that same vertex set. This isolates the finite extension construction from the edge-count argument. The vertex-count hypothesis is retained from the parent; the finite-maximization argument itself works for any finite vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry
