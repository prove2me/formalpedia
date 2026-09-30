-- Prove2me | Theorems.Thm_Hirsch_target_two_level_original_hirsch_routes
-- name    : Hirsch.target_two_level_original_hirsch_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-21T22:54:37.872628+00:00
-- url     : https://prove2.me/theorems/1af3403d-78a5-4897-888c-f212df868057
-- title:
--   Target-only two-level original rows give target-locking Hirsch routes
-- statement:
--   Let the convex hull of a supplied finite real generator set C in ambient dimension d equal exactly the original m linear halfspaces A_i(x)<=b_i. Let u,v be actual extreme points. Assume ONLY each original row tight at target v has at most its boundary value and one other value on the actual vertices. Construct an indexed route from u to v through actual vertices, with distinct consecutive endpoints and entire IsExtreme segments of the original polytope. Every step preserves all already tight target rows and acquires at least one new target row. Its length is bounded both by the initially missing target-row count and by m-d. Original active-row rank and target uniqueness are derived, not supplied. Non-target rows need not have two levels; redundant/interior generators, redundant inequalities, nonsimple vertices, lower-dimensional bodies, zero dimension and equal endpoints are allowed. The exact finite-hull/H equality and target-only two-level condition remain structural hypotheses. This is a restricted class theorem in displayed original inequalities, not a universal Polynomial Hirsch result, shortest-route claim, all-facet nonrevisiting theorem or efficient H-to-V algorithm.
-- source:
--   Direct target-face locking and active-row rank argument, using the accepted actual finite-hull improving-edge and support-face proofs from PR #322. The retained Route and HullCoordinate proof bodies are byte-identical subranges of its accepted source; earlier public roots are omitted, not resubmitted. The active-kernel proof generalizes the finite-margin argument present in the moment-vertex work. Two-level polytope and original-face geometry are classical; no historical-priority or best-known-bound claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.target_two_level_original_hirsch_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (htwo : ∀ i, A i v=b i → ∃ lo : ℝ,
      ∀ x ∈ ({x | ∀ j, A j x ≤ b j} : Set (Fin d → ℝ)).extremePoints ℝ,
        A i x=lo ∨ A i x=b i) :
    ∃ L : ℕ, L ≤ m-d ∧
      L ≤ (@Finset.filter (Fin m) (fun i => A i v=b i ∧ A i u ≠ b i)
        (fun _ => Classical.propDecidable _) Finset.univ).card ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
        ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
          IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
            (segment ℝ (p t.castSucc) (p t.succ)) ∧
          (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) ∧
          ∃ i, A i v=b i ∧ A i (p t.castSucc) ≠ b i ∧ A i (p t.succ)=b i := by sorry
