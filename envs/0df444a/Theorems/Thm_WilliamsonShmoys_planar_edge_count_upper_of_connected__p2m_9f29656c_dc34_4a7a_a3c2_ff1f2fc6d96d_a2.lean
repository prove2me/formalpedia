-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_of_connected__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_of_connected__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:18:43.456484+00:00
-- url     : https://prove2.me/theorems/5598e679-4b8f-483d-bd76-05b90ab9d984
-- title:
--   Lift the connected planar edge bound to arbitrary graphs
-- statement:
--   If the connected edge bound holds for every finite linearly ordered vertex type, then it holds for any drawable finite graph with at least three vertices. Prove this by decomposing into connected components, restricting the drawing to each component, applying the connected bound to components of size at least three, and bounding components of size one or two directly using simplicity; then sum the component bounds. This removes the disconnected-component bookkeeping from the parent while leaving the connected topological argument in the first child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_of_connected__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (K : SimpleGraph W),
        HasPlanarDrawingOn K → K.Connected →
        3 ≤ Fintype.card W →
        K.edgeSet.ncard + 6 ≤ 3 * Fintype.card W) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
