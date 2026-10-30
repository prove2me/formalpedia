-- Prove2me | Theorems.Thm_planar_drawing_maximal_extension__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1
-- name    : planar_drawing_maximal_extension__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:37:23.915985+00:00
-- url     : https://prove2.me/theorems/c3da99fd-473e-47a0-bb34-87152b85482e
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem planar_drawing_maximal_extension__p2m_6bcbc754_6431_43a3_bb11_f771114284ff_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : LE.le 3 (Fintype.card V)) : Exists fun L : SimpleGraph V => And (LE.le K L) (And (HasPlanarDrawingOn L) (∀ M : SimpleGraph V, LE.le L M → HasPlanarDrawingOn M → M = L)) := by sorry
