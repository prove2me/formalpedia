-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
-- name    : WilliamsonShmoys.exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:28:37.982149+00:00
-- url     : https://prove2.me/theorems/7c460f00-ed2c-4147-a9e0-5f6b683848ab
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   Any finite graph with at least three vertices and a crossing-free drawing has a connected supergraph on the same vertices with a crossing-free drawing. This removes the disconnected-components issue while preserving the original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
