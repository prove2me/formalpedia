-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:53:19.516515+00:00
-- url     : https://prove2.me/theorems/9251ca56-2f13-4506-a97b-c72b0a41465a
-- title:
--   Maximal planar extension on the same vertex set
-- statement:
--   Extend the given drawable graph to a drawable graph on the same vertices that is maximal among drawable simple supergraphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_1345f058_46fd_4b3f_bd68_5a032464e223_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ u v, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ∀ u v, K.Adj u v → H.Adj u v) := by sorry
