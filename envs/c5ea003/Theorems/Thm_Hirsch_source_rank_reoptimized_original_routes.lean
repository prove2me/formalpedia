-- Prove2me | Theorems.Thm_Hirsch_source_rank_reoptimized_original_routes
-- name    : Hirsch.source_rank_reoptimized_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T23:48:42.343903+00:00
-- url     : https://prove2.me/theorems/0953784a-17e7-4bbd-a3d7-29d1f96b3925
-- title:
--   Source-sensitive reoptimized-rank descent on original polytope edges
-- statement:
--   Given exact finite H/hull equality and actual extreme endpoints, derive a strictly target-exposing linear numerator, positive affine normalizers on every current common target face, and source-sensitive minima counting only distinct normalized values strictly below the current value. Construct whole original edges preserving all acquired target equations, with the optimized integer rank decreasing at every step, including nonacquiring steps. The complete route length is at most the initial optimum and therefore at most the initial source rank for every positive affine competitor. Target rank is zero. No normalizer, selected graph, short phase, pre-existing path or small rank is an input. A uniform polynomial upper bound on this attained rank is not asserted.
-- source:
--   Reuse accepted original-hull geometry from #335/#333 without resubmitting it. The new proof combines strict old-ratio decrease, current-face inclusion and pointwise reoptimization into a single globally decreasing source-sensitive rank, then constructs the original-edge route by strong induction. Mathematical attainment uses natural-number well-ordering, not an extracted linear-programming routine. Exact order-cell search and original-H tests are separate supporting computations. No historical-priority, shortestness or unconditional polynomial diameter claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.source_rank_reoptimized_original_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
      (fun _ => Classical.propDecidable _) C
    let F := fun x : Fin d → ℝ => @Finset.filter (Fin d → ℝ)
      (fun z => ∀ i, A i v=b i → A i x=b i → A i z=b i)
      (fun _ => Classical.propDecidable _) V
    ∃ h : (Fin d → ℝ) →ₗ[ℝ] ℝ, (∀ z ∈ C, z ≠ v → 0<h (z-v)) ∧
      ∃ E : (Fin d → ℝ) → (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ V, ∀ z ∈ F x, 0<1+E x (z-v)) ∧
        let R := fun (x : Fin d → ℝ) (D : (Fin d → ℝ) →ₗ[ℝ] ℝ) =>
          @Finset.filter ℝ (fun a => a<h (x-v)/(1+D (x-v)))
            (fun _ => Classical.propDecidable _)
            ((F x).image (fun z => h (z-v)/(1+D (z-v))))
        (∀ x ∈ V, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
          (∀ z ∈ F x, 0<1+D (z-v)) → (R x (E x)).card ≤ (R x D).card) ∧
        (R v (E v)).card=0 ∧
        ∃ L : ℕ, L ≤ (R u (E u)).card ∧
          (∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
            (∀ z ∈ F u, 0<1+D (z-v)) → L ≤ (R u D).card) ∧
          ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
            (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
            ∀ t : Fin L,
              (p t.castSucc ≠ p t.succ ∧
                IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
                  (segment ℝ (p t.castSucc) (p t.succ)) ∧
                (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i)) ∧
              (R (p t.succ) (E (p t.succ))).card <
                (R (p t.castSucc) (E (p t.castSucc))).card := by sorry
