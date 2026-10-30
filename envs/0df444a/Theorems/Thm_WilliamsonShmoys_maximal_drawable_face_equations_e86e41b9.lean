-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_face_equations_e86e41b9
-- name    : WilliamsonShmoys.maximal_drawable_face_equations_e86e41b9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:58:17.855207+00:00
-- url     : https://prove2.me/theorems/d47f3ab2-10a3-4179-9975-a34de0f049a7
-- title:
--   Euler and face-incidence equations for a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has a face count satisfying Euler’s vertex-face-edge equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_face_equations_e86e41b9
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = L.edgeSet.ncard + 2 /\
        3 * f = 2 * L.edgeSet.ncard := by sorry
