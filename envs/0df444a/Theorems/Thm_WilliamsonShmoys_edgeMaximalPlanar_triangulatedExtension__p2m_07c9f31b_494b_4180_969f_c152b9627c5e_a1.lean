-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_triangulatedExtension__p2m_07c9f31b_494b_4180_969f_c152b9627c5e_a1
-- name    : WilliamsonShmoys.edgeMaximalPlanar_triangulatedExtension__p2m_07c9f31b_494b_4180_969f_c152b9627c5e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:48:02.311189+00:00
-- url     : https://prove2.me/theorems/541725ce-ba0e-4ec7-9bf8-a3e758b67715
-- title:
--   Connected planar graphs extend to a triangulation
-- statement:
--   Every connected drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edgeMaximalPlanar_triangulatedExtension__p2m_07c9f31b_494b_4180_969f_c152b9627c5e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        3 * Fintype.card V - 6 = H.edgeFinset.card := by sorry
