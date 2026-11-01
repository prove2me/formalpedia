-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b554ef36_a96a_42de_b297_4474260662ac_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_b554ef36_a96a_42de_b297_4474260662ac_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:24.425228+00:00
-- url     : https://prove2.me/theorems/aebf59bd-f6b5-46a8-a852-f6c4896d39c8
-- title:
--   Every drawable graph extends to a planar triangulation
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, every graph admitting the specified crossing-free drawing is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6. This isolates the extension-to-triangulation and Euler-counting obligation used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_b554ef36_a96a_42de_b297_4474260662ac_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
