-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_19232441_686a_4272_ba92_bbecb802c741_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_19232441_686a_4272_ba92_bbecb802c741_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:58:03.037819+00:00
-- url     : https://prove2.me/theorems/cef71128-5f51-4c32-b585-a6c07850dc7b
-- title:
--   Finite maximal extension for an arbitrary graph property
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, every graph satisfying that predicate has a supergraph that is inclusion-maximal among graphs satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_extension__p2m_19232441_686a_4272_ba92_bbecb802c741_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      ∀ L : SimpleGraph V, H ≤ L → L ≠ H → ¬ P L := by sorry
