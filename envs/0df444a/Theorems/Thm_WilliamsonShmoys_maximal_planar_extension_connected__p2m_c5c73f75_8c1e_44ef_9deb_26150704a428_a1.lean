-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_connected__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_connected__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:19:57.663707+00:00
-- url     : https://prove2.me/theorems/28f50d30-117d-4a63-8d20-afb26b4b003d
-- title:
--   Maximal drawable extension is connected
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_connected__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> H = J) :
    H.Connected := by sorry
