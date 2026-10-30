-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
-- name    : WilliamsonShmoys.planar_connected_extension__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:00.489016+00:00
-- url     : https://prove2.me/theorems/ea88c89d-48b3-414b-a3f4-04bcb156f9eb
-- title:
--   Connect a nonempty planar graph by adding edges
-- statement:
--   Every nonempty finite planar graph has a connected planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_extension__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 1 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Connected := by sorry
