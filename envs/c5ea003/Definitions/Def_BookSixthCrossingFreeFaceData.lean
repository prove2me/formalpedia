-- Prove2me | Definitions.Def_BookSixthCrossingFreeFaceData
-- name    : BookSixthCrossingFreeFaceData
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-23T21:56:54.090988+00:00
-- url     : https://prove2.me/theorems/18f5d0e4-dc74-4720-9d75-70386a48f305
-- title:
--   Face data for a crossing-free drawing subset
-- statement:
--   This definition records the geometric data needed for the planar edge estimate. For a selected vertex set $V$ and a selected crossing-free edge set $E$, the support is the union of the selected vertices and selected continuous edge arcs. Its bounded complementary components are the candidate bounded faces. The certificate consists of the finite collection of those components together with four properties: the weak Euler relation $|E| \le |V|+|F|$, at least three selected edge labels meet the frontier of each bounded face, and at most two bounded faces meet the interior of each selected edge. The definition does not assert that the certificate exists; that is the separate geometric child theorem.
-- source:
--   Derived interface for the planar edge estimate in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 4, p. 317, https://doi.org/10.1007/978-3-662-57265-8_45, using the canonical Prove2Me definition b1fcef2b-61fb-4326-bde6-cb6070d37c77. The certificate packages the standard Euler and face-incidence obligations without adding them as hypotheses to the parent theorem.

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

namespace BookSixth

abbrev CrossingFreePlane := Fin 2 → ℝ

def crossingFreeSupport {N M : ℕ} (D : PlaneDrawing N M)
    (V : Finset (Fin N)) (E : Finset (Fin M)) : Set CrossingFreePlane :=
  {x | (∃ v ∈ V, D.vertex v = x) ∨ ∃ e ∈ E, ∃ t, D.arc e t = x}

def crossingFreeBoundedFaces {N M : ℕ} (D : PlaneDrawing N M)
    (V : Finset (Fin N)) (E : Finset (Fin M)) : Set (Set CrossingFreePlane) :=
  {U | Bornology.IsBounded U ∧ ∃ x ∈ (crossingFreeSupport D V E)ᶜ,
    U = connectedComponentIn (crossingFreeSupport D V E)ᶜ x}

def crossingFreeFaceIncident {N M : ℕ} (D : PlaneDrawing N M)
    (U : Set CrossingFreePlane) (e : Fin M) : Prop :=
  ∀ t : EdgeParameter, 0 < t.val → t.val < 1 → D.arc e t ∈ frontier U

def CrossingFreeFaceCertificate {N M : ℕ} (D : PlaneDrawing N M)
    (V : Finset (Fin N)) (E : Finset (Fin M)) : Prop := by
  classical
  exact ∃ F : Finset (Set CrossingFreePlane),
    (∀ U, U ∈ F ↔ U ∈ crossingFreeBoundedFaces D V E) ∧
    E.card ≤ V.card + F.card ∧
    (∀ U ∈ F, 3 ≤ (E.filter (crossingFreeFaceIncident D U)).card) ∧
    (∀ e ∈ E, (F.filter (fun U => crossingFreeFaceIncident D U e)).card ≤ 2)

end BookSixth


