-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_property_supergraph__p2m_8cd0804a_f792_4057_bb92_319536b24856_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_property_supergraph__p2m_8cd0804a_f792_4057_bb92_319536b24856_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:24:26.728311+00:00
-- url     : https://prove2.me/theorems/8dafb58d-fd78-48d8-8d4d-72b91407a235
-- title:
--   Finite maximal supergraph for an arbitrary property
-- statement:
--   For any property P on simple graphs over a fixed finite linearly ordered vertex type, every graph satisfying P is contained in a P-satisfying graph that is maximal under graph inclusion among P-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_property_supergraph__p2m_8cd0804a_f792_4057_bb92_319536b24856_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ P M ∧
        ∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M := by sorry
