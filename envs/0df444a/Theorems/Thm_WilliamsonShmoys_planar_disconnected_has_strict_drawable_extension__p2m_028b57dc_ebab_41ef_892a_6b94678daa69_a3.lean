-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_strict_drawable_extension__p2m_028b57dc_ebab_41ef_892a_6b94678daa69_a3
-- name    : WilliamsonShmoys.planar_disconnected_has_strict_drawable_extension__p2m_028b57dc_ebab_41ef_892a_6b94678daa69_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:32.795203+00:00
-- url     : https://prove2.me/theorems/46cfe7ce-b627-4e5a-9d08-1eab5cbb77ec
-- title:
--   A disconnected drawable graph has a strict drawable extension
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, a disconnected graph with the specified planar drawing has a strictly larger drawable supergraph on the same vertices. This isolates the planar extension step needed by maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_has_strict_drawable_extension__p2m_028b57dc_ebab_41ef_892a_6b94678daa69_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hdis : ¬ M.Connected) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ¬ H ≤ M := by sorry
