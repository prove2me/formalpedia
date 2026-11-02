-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
-- name    : WilliamsonShmoys.maximal_drawable_connected__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:49:17.594282+00:00
-- url     : https://prove2.me/theorems/34e3c7ce-8936-45db-894d-7bc025c10cb3
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing and at least three vertices is connected. If it were disconnected, an edge could be added between vertices in different components while preserving drawability, contradicting maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_connected__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.Connected := by sorry
