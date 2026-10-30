-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:33:09.486019+00:00
-- url     : https://prove2.me/theorems/c9fc3f38-cd2a-4e85-9567-ad68f211d82b
-- title:
--   Extend a planar drawing to an inclusion-maximal planar supergraph
-- statement:
--   Every finite planar drawing on the fixed vertex type extends to a planar graph that is maximal among planar supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1 {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
