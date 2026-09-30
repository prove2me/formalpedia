-- Prove2me | Theorems.Thm_Hirsch_zonotope_regular_objective_original_routes
-- name    : Hirsch.zonotope_regular_objective_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-19T22:31:08.707684+00:00
-- url     : https://prove2.me/theorems/58ae59bf-f663-4bbb-ba6b-1858d7a64009
-- title:
--   Construct a generator-bounded original zonotope edge walk between regular exposed vertices
-- statement:
--   For any finite collection of m real vectors in R^d and two linear objectives nonzero on every nonzero generator, construct a vertex walk of at most m nondegenerate original exposed/extreme edges in the actual segment sum. Its endpoints are exactly the singleton whole maximizing faces of the two objectives, and every visited point is an actual extreme point. The finite crossing set, its sorted order, the chamber samples, vertex identities and original adjacency are derived, not assumed. Repeated, opposite, parallel, zero and rank-deficient generators, dimension zero and zero-crossing cases are retained. Regular endpoint objectives are explicit hypotheses. No claim that arbitrary specified vertices come with such objectives, no generator bound in terms of original H facets, no shortestness or unrestricted Polynomial Hirsch conclusion. The result is a noncomputable real theorem, not a verified Python parser or runtime algorithm.
-- source:
--   Concrete ordered-walk assembly following ACCEPTED #313, Hirsch.zonotope_regular_sweep_original_edges (4713ca26-d458-47e6-9ae0-4654b0322f39). Its complete namespace prefix, including accepted #312 original edge faces, is copied byte-for-byte from proof7dbeccc586323fb67ce565dec401306304bfeb9d, excluding only the old public theorem and print suffix. New work derives the finite event mesh, adjacent chamber face limits and distinct endpoint identification. This is a formalization of classical zonotope geometry, not a historical novelty or new best diameter bound.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.zonotope_regular_objective_original_routes (d m : ℕ) (w : Fin m → (Fin d → ℝ))
    (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : ∀ i, w i ≠ 0 → f (w i) ≠ 0)
    (hg : ∀ i, w i ≠ 0 → g (w i) ≠ 0) :
    let Z : Set (Fin d → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    let F : ((Fin d → ℝ) →ₗ[ℝ] ℝ) → Set (Fin d → ℝ) :=
      fun h => {x | x ∈ Z ∧ h x = ∑ i : Fin m, max 0 (h (w i))}
    ∃ L : ℕ, L ≤ m ∧ ∃ p : Fin (L+1) → (Fin d → ℝ),
      F f = {p 0} ∧ F g = {p (Fin.last L)} ∧
      (∀ i, p i ∈ Z.extremePoints ℝ) ∧
      ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
        IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ)) ∧
        IsExtreme ℝ Z (segment ℝ (p i.castSucc) (p i.succ)) := by sorry
