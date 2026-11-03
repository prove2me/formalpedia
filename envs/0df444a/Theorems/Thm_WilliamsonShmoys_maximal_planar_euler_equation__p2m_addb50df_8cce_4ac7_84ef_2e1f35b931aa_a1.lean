-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_equation__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1
-- name    : WilliamsonShmoys.maximal_planar_euler_equation__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:50.391493+00:00
-- url     : https://prove2.me/theorems/e64c3b00-d89d-475f-af94-6800f223904e
-- title:
--   Euler equation for a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has a face count satisfying Euler’s equation, with the unbounded face included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_euler_equation__p2m_addb50df_8cce_4ac7_84ef_2e1f35b931aa_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → H ≤ L → L = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2) := by sorry
