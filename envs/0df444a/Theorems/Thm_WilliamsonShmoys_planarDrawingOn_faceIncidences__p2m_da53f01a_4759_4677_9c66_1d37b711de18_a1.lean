-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_faceIncidences__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
-- name    : WilliamsonShmoys.planarDrawingOn_faceIncidences__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:36.488763+00:00
-- url     : https://prove2.me/theorems/35c7c587-264a-42e7-8ae7-e5b47b6a2d0c
-- title:
--   Face-boundary incidence bounds
-- statement:
--   For a finite connected simple planar graph with at least three vertices, any face count satisfying Euler’s equation admits a total boundary-incidence count that counts two sides per edge and at least three per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_faceIncidences__p2m_da53f01a_4759_4677_9c66_1d37b711de18_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hn : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f =
      (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) + 2) :
    ∃ i : ℕ,
      2 * (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ≤ i ∧
      3 * f ≤ i := by
  sorry
