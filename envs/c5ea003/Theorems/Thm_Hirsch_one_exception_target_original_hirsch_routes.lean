-- Prove2me | Theorems.Thm_Hirsch_one_exception_target_original_hirsch_routes
-- name    : Hirsch.one_exception_target_original_hirsch_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-21T23:32:13.345327+00:00
-- url     : https://prove2.me/theorems/c1dc3a15-302a-4063-b3ca-e9ac669d7c48
-- title:
--   One unrestricted target row still permits original m-d edge routes
-- statement:
--   Let P be exactly both the convex hull of a finite real generator set C in ambient dimension d and the original m linear halfspaces. For actual vertices u,v and a set B of at most one original row label, assume every row tight at v outside B takes its boundary value and at most one other value on all actual vertices. No condition is imposed on the vertex values of the exceptional row or non-target rows. Construct a finite walk through actual vertices of the same original P, of length at most both m-d and the number of target-tight original rows initially missing at u. Every step is a nondegenerate whole IsExtreme original segment, preserves each previously acquired target row and acquires a new target row. The proof derives one-step completion when only one target row remains, rather than assuming a low-dimensional face or a short route. Empty B, dimension zero, equal endpoints, redundant rows/generators and nonsimple/lower-dimensional hulls remain covered. These are restricted-class assumptions, not a solution of Polynomial Hirsch.
-- source:
--   Extends accepted PR #323, Hirsch.target_two_level_original_hirsch_routes, using its exact namespace prefix with the old public root omitted. New work removes the two-level requirement for one target row: active-kernel triviality identifies any would-be intermediate improving vertex as a strict convex combination of the current and target vertices, contradicting extremality. General one-step improvement and original-label induction then retain the same bound. Classical polyhedral face/rank geometry is used; no historical-priority or best-known-bound claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.one_exception_target_original_hirsch_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (B : Finset (Fin m)) (hB : B.card ≤ 1)
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (htwo : ∀ i, i ∉ B → A i v=b i → ∃ lo : ℝ,
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
