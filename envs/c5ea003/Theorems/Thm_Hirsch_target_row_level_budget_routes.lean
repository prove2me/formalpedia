-- Prove2me | Theorems.Thm_Hirsch_target_row_level_budget_routes
-- name    : Hirsch.target_row_level_budget_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T03:21:20.950646+00:00
-- url     : https://prove2.me/theorems/bf3ff04d-50b5-4999-a1e4-5f6fd973f8a3
-- title:
--   One charge per original target row with a bounded-level route corollary
-- statement:
--   Let the convex hull of a finite real family C in ambient dimension d equal exactly the original m halfspaces A_i x <= b_i. For actual extreme endpoints u,v, derive the actual vertex set V and let T be the original rows tight at target v but not at u. Construct a route through actual original extreme points, each consecutive segment nondegenerate and IsExtreme in the original body, preserving every target row already acquired. The same route has length at most sum over i in T of (the number of distinct values of A_i on actual vertices minus one). For every natural K such that each target-tight row has at most K+1 actual vertex values, the same length is at most K*(m-d). There is no restriction on the number of target rows with more than two values. No neighbor graph, active basis, bounded phase, rank, vertex catalogue or short route is assumed. The general weighted level sum need not be polynomial in original m; the bounded-level implication retains its structural antecedent and is not a uniform Polynomial Hirsch conclusion. Exact H/hull equality, actual endpoint extremality, redundant rows/generators, nonsimple/lower-dimensional hulls, dimension zero and equal endpoints are covered.
-- source:
--   Composition of classical finite linear-objective ascent and target-face locking with accepted original improving-edge and active-row geometry from #322/#323/#325, reused through #328. New work derives an entire row-acquisition phase by counting distinct higher values, proves that a completed phase removes its charged original label, and sums heterogeneous costs over initially missing target labels. Retained helper bodies are byte-identical; unused later accepted blocks and public roots are omitted. This is not a claim of historical priority, a best-known general k-level diameter bound, or a solution of Polynomial Hirsch. The separately owned affine-roof #326 and reserved #282/#210 are unchanged.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.target_row_level_budget_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
      (fun _ => Classical.propDecidable _) C
    let T := @Finset.filter (Fin m) (fun i => A i v=b i ∧ A i u ≠ b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    ∃ L : ℕ, L ≤ ∑ i ∈ T, ((V.image (fun x => A i x)).card-1) ∧
      (∀ K : ℕ, (∀ i, A i v=b i → (V.image (fun x => A i x)).card ≤ K+1) →
        L ≤ K*(m-d)) ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
        ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
          IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
            (segment ℝ (p t.castSucc) (p t.succ)) ∧
          (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
