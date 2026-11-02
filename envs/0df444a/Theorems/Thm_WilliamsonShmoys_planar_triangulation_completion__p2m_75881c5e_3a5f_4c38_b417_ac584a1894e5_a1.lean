-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_75881c5e_3a5f_4c38_b417_ac584a1894e5_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_75881c5e_3a5f_4c38_b417_ac584a1894e5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:23:47.599451+00:00
-- url     : https://prove2.me/theorems/dc89fabe-6e93-4cfa-857f-8e50eb25e826
-- title:
--   Planar triangulation completion on the same vertex set
-- statement:
--   Every drawable finite simple graph with at least three vertices is a subgraph of a drawable graph on the same vertex set having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_75881c5e_3a5f_4c38_b417_ac584a1894e5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∃ (d : DecidableRel K.Adj),
        (letI : DecidableRel K.Adj := d;
          K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
