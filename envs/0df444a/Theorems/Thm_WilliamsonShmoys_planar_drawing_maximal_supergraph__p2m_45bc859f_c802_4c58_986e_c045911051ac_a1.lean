-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:00.425623+00:00
-- url     : https://prove2.me/theorems/407cedf5-8faa-4a1f-b011-cc5bdf645c63
-- title:
--   Maximal drawable supergraph exists
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ J : SimpleGraph V, G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J := by sorry
