-- Prove2me | Theorems.Thm_Hirsch_synthesized_face_normalizer_original_routes
-- name    : Hirsch.synthesized_face_normalizer_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T20:12:27.367836+00:00
-- url     : https://prove2.me/theorems/ae38bf3e-aa8c-4ae9-886e-8088c3c0a107
-- title:
--   Synthesized face-local affine normalizers and optimal original-edge target routes
-- statement:
--   For a finite real hull equal to its original m halfspaces in ambient dimension d and actual extreme endpoints u,v, derive for every original target-prefix face and every row an anchored affine denominator positive on that face and attaining the minimum normalized-slack spectrum over ALL real positive affine competitors on that face. Derive a nonrepeating ordered determining completion of the shared target equations, of length at most min(d,m-d), minimizing the sum of these conditional spectra minus one. Construct a route through actual original vertices with whole nondegenerate IsExtreme original segments preserving every acquired target row, of length at most this minimum budget. The same route satisfies K*min(d,m-d) when its computed local charges are at most K. Denominators, local positivity, spectral optima, flags and complete phases are outputs, not inputs. Exact finite H/hull equality and endpoint extremality remain. No uniformly small optimum, efficient enumeration, shortestness, or unrestricted Polynomial Hirsch conclusion is asserted.
-- source:
--   Compose accepted #334 finite affine-normalizer catalogue with original-edge geometry and target-row completion retained from #333/#332; adapt normalized acquisition to positivity only on a planned prefix face and re-synthesize before every selected phase. Neither accepted target is resubmitted. Classical linear-fractional linearization, finite-dimensional tie compression, finite choice and well-founded route assembly; no historical-priority claim. Exact tests compare both optimized predecessor budgets and preserve nonshortest/zero-edge phases. Other-owned #326/#282 and reserved #210 remain untouched.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.synthesized_face_normalizer_original_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hP : convexHull ℝ (C : Set (Fin d → ℝ))={x | ∀ i, A i x ≤ b i})
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) :
    let V := @Finset.filter (Fin d → ℝ)
      (fun x => x ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
      (fun _ => Classical.propDecidable _) C
    let F := fun H : Finset (Fin m) => @Finset.filter (Fin d → ℝ)
      (fun x => ∀ i ∈ H, A i x=b i) (fun _ => Classical.propDecidable _) V
    let T := @Finset.filter (Fin m) (fun i => A i v=b i ∧ A i u ≠ b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let G := @Finset.filter (Fin m) (fun i => A i u=b i ∧ A i v=b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    ∃ E : Finset (Fin m) → Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ H, (∀ i ∈ H, A i v=b i) → ∀ j, ∀ x ∈ F H, 0<1+E H j (x-v)) ∧
      (∀ H, (∀ i ∈ H, A i v=b i) → ∀ j, ∀ a : ℝ, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ F H, 0<a+D x) →
          ((F H).image (fun x => (b j-A j x)/(1+E H j (x-v)))).card ≤
            ((F H).image (fun x => (b j-A j x)/(a+D x))).card) ∧
      let q : List (Fin m) → Finset (Fin m) → List ℕ :=
        List.rec (fun _ => []) (fun j _ tailCharges H =>
          (((F H).image (fun x => (b j-A j x)/(1+E H j (x-v)))).card-1) ::
            tailCharges (insert j H))
      ∃ J : List (Fin m), J.Nodup ∧ J.length ≤ min d (m-d) ∧
        (∀ i ∈ J, i ∈ T) ∧
        (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ J, A i z=0) → z=0) ∧
        ∃ L : ℕ, L ≤ (q J G).sum ∧
          (∀ R : List (Fin m), R.Nodup → R.length ≤ min d (m-d) →
            (∀ i ∈ R, i ∈ T) →
            (∀ z : Fin d → ℝ, (∀ i ∈ G, A i z=0) → (∀ i ∈ R, A i z=0) → z=0) →
            (q J G).sum ≤ (q R G).sum) ∧
          (∀ K : ℕ, (∀ k ∈ q J G, k ≤ K) → L ≤ K*min d (m-d)) ∧
          ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
            (∀ t, p t ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ) ∧
            ∀ t : Fin L, p t.castSucc ≠ p t.succ ∧
              IsExtreme ℝ {x : Fin d → ℝ | ∀ i, A i x ≤ b i}
                (segment ℝ (p t.castSucc) (p t.succ)) ∧
              (∀ i, A i v=b i → A i (p t.castSucc)=b i → A i (p t.succ)=b i) := by sorry
