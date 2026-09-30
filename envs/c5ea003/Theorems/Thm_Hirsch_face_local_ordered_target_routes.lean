-- Prove2me | Theorems.Thm_Hirsch_face_local_ordered_target_routes
-- name    : Hirsch.face_local_ordered_target_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-22T15:38:35.387494+00:00
-- url     : https://prove2.me/theorems/98a47ad2-122d-4507-928a-27acca8a8c1e
-- title:
--   Optimal face-local ordered target-row budgets for original-edge routes
-- statement:
--   For a finite real hull equal to its original m halfspaces in ambient dimension d, and actual extreme endpoints u,v, derive a nonrepeating ordered list J of initially missing target rows of length at most min(d,m-d) completing the initially shared target equations. For each row in J, count its distinct values on actual ORIGINAL vertices satisfying the shared equations and all earlier selected equations; charge that cardinality minus one. Derive an order minimizing the total conditional charge over every eligible small determining order, then construct a route of genuine original edges with length at most that minimum. Every visited point is an actual original vertex, every consecutive segment is whole nondegenerate IsExtreme in the original body, and every acquired target row remains tight. For the SAME route, local charges bounded by K imply length at most K*min(d,m-d). The determining order, local vertex sets, complete acquisition phases and route are not premises. No uniform small charge is assumed or concluded, and the optimal conditional total may still be exponential. Redundant rows/generators, nonsimple/lower-dimensional hulls, dimension zero and equal endpoints remain included. This is not uniform Polynomial Hirsch, shortest-path optimality or a polynomial-time flag search.
-- source:
--   Reuse the original-hull improving-edge, target-locking, active-kernel and small-completion proof bodies accepted in #325/#329/#330. New work constructs whole phases using values only on their planned prefix face, recursively changes that face after each selected row, derives a small eligible flag, and uses natural-number well-ordering to minimize conditional cost. Existing #250/#251 constant-face obstructions remain; neither face-drop count alone nor a small-phase oracle is asserted. The known triangular family from #276 is a written/exact stress test only; #282 owns its separate Lean all-vertex classification/routes and is not modified. No historical-priority or best-known diameter claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.face_local_ordered_target_routes (d m : ℕ) (C : Finset (Fin d → ℝ))
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
    let G := @Finset.filter (Fin m) (fun i => A i u=b i ∧ A i v=b i)
      (fun _ => Classical.propDecidable _) Finset.univ
    let q : List (Fin m) → Finset (Fin m) → List ℕ :=
      List.rec (fun _ => []) (fun j _ tailCharges H =>
        (((@Finset.filter (Fin d → ℝ) (fun x => ∀ i ∈ H, A i x=b i)
          (fun _ => Classical.propDecidable _) V).image (fun x => A j x)).card-1) :: tailCharges (insert j H))
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
