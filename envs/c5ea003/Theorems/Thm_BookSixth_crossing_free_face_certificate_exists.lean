-- Prove2me | Theorems.Thm_BookSixth_crossing_free_face_certificate_exists
-- name    : BookSixth.crossing_free_face_certificate_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T21:59:49.856661+00:00
-- url     : https://prove2.me/theorems/8f7e04b5-1428-4b20-9ef2-23e650928b10
-- title:
--   Existence of bounded-face data for a crossing-free drawing subset
-- statement:
--   Let $D$ be a good continuous drawing of a finite simple graph, let $V$ be a set of vertices, and let $E$ be a set of edges whose endpoints lie in $V$. Suppose distinct selected edges have disjoint interiors. Then the actual bounded complementary components of the selected drawing support form a finite face certificate: the weak Euler count relates the numbers of selected edges and bounded faces, every bounded face meets at least three selected edge interiors, and every selected edge interior meets at most two bounded faces. This isolates the continuous-plane geometry needed by the planar edge estimate; it does not assume Euler's formula or the face-incidence inequalities.
-- source:
--   Geometric reduction component for the planar edge estimate in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45, using the canonical drawing interface b1fcef2b-61fb-4326-bde6-cb6070d37c77. The bounded complementary-component construction and the incidence formulation are the standard continuous-arc face certificate; existence of the certificate is the remaining planar-separation obligation.

import Mathlib
import Definitions.Def_BookSixth
import Definitions.Def_BookSixthCrossingFreeFaceData
open BookSixth

theorem BookSixth.crossing_free_face_certificate_exists {N M : ℕ} (D : PlaneDrawing N M)
    (V : Finset (Fin N)) (E : Finset (Fin M))
    (hend : ∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V)
    (hfree : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ t s : EdgeParameter,
      0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 →
      D.arc e t ≠ D.arc f s) :
    CrossingFreeFaceCertificate D V E := by sorry
