-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_extension__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:13.509836+00:00
-- url     : https://prove2.me/theorems/93dc1d00-38eb-4c68-8175-9bf4a2bde746
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_extension__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (forall N : SimpleGraph V, M <= N ->
        WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) := by sorry
