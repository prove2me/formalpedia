-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected
-- name    : WilliamsonShmoys.maximal_drawable_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:45:32.093884+00:00
-- url     : https://prove2.me/theorems/40bc06c5-ba1c-40a5-af8f-0371cc5f2c2d
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   A drawable simple graph on at least three vertices that admits no drawable strict supergraph on the same vertex set is connected. If it were disconnected, the components could be joined by an additional noncrossing edge in the plane, contradicting maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall H : SimpleGraph V, G <= H ->
      WilliamsonShmoys.HasPlanarDrawingOn H -> H <= G)
    (hV : 3 <= Fintype.card V) :
    G.Connected := by sorry
