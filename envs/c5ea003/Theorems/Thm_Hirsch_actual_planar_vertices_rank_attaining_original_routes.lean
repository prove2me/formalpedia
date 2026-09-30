-- Prove2me | Theorems.Thm_Hirsch_actual_planar_vertices_rank_attaining_original_routes
-- name    : Hirsch.actual_planar_vertices_rank_attaining_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-23T21:46:37.86681+00:00
-- url     : https://prove2.me/theorems/461b1bee-2db8-4db3-acc4-5eeac1f9e0b6
-- title:
--   Actual planar vertices yield strict radial chains and rank-attaining original exposed-edge routes
-- statement:
--   For a planar convex set P exactly the finite hull of target v and an ordered list p of its other actual extreme points, fix a linear h strictly positive on p_i-v and a second linear coordinate e jointly injective with h. Order p by the strictly increasing ratios e(p_i-v)/h(p_i-v). Derive, rather than assume, strict convexity of the inverse-height chart. Construct every consecutive original exposed segment and both original target edges, and for each source construct a finite original-vertex walk to v of exactly min(k,n-k)+1 edges. The same length is one plus the all-real minimum distinct upper chart-height count and is attained by two derived source-independent extreme tilts; a positive height shift and reciprocal count realize it. Twice this length is at most n+2, the supplied complete original-vertex count. Finite-hull completeness, actual extremality, chosen strict exposure, jointly injective coordinates and the sorted order are explicit. This is a planar original-edge construction, not a facet-count or arbitrary-dimensional Polynomial Hirsch result, and shortestness among arbitrary original walks is not asserted.
-- source:
--   Formal geometric bridge left written in accepted PR338. Reuses its exact ConvexChainRank namespace prefix and the accepted PR336 hull_support helper. New proof derives radial strict convexity from original extremality, constructs original support functionals, and assembles finite walks. No historical novelty claim for the classical planar geometry.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.actual_planar_vertices_rank_attaining_original_routes (n : ℕ) (P : Set (Fin 2 → ℝ)) (v : Fin 2 → ℝ)
    (p : Fin (n+1) → (Fin 2 → ℝ))
    (h e : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)
    (hP : P=convexHull ℝ ((insert v (Finset.univ.image p) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)))
    (hv : v ∈ P.extremePoints ℝ) (hp : ∀ i, p i ∈ P.extremePoints ℝ)
    (hpos : ∀ i, 0 < h (p i-v))
    (hinj : Function.Injective (fun z : Fin 2 → ℝ => (h z,e z)))
    (hw : StrictMono (fun i => e (p i-v)/h (p i-v))) :
    let w := fun i => e (p i-v)/h (p i-v)
    let a := fun i => 1/h (p i-v)
    let U := fun (t : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => a k+t*w k < z) (fun _ => Classical.propDecidable _)
        (Finset.univ.image (fun i => a i+t*w i))
    let B := fun (t c : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => z < 1/(a k+t*w k+c)) (fun _ => Classical.propDecidable _)
        (insert 0 (Finset.univ.image (fun i => 1/(a i+t*w i+c))))
    (∀ i j k : Fin (n+1), i < j → j < k →
      (a j-a i)*(w k-w j) < (a k-a j)*(w j-w i)) ∧
    (p 0 ≠ v ∧ IsExposed ℝ P (segment ℝ (p 0) v)) ∧
    (p (Fin.last n) ≠ v ∧ IsExposed ℝ P (segment ℝ (p (Fin.last n)) v)) ∧
    (∀ j : Fin n, p j.castSucc ≠ p j.succ ∧
      IsExposed ℝ P (segment ℝ (p j.castSucc) (p j.succ))) ∧
    ∃ M : ℝ, 0 < M ∧ ∀ k : Fin (n+1),
      (∀ t : ℝ, min k.val (n-k.val) ≤ (U t k).card) ∧
      (U (-M) k).card=k.val ∧ (U M k).card=n-k.val ∧
      ∃ L : ℕ, L=min k.val (n-k.val)+1 ∧ 2*L ≤ n+2 ∧
        (∀ t : ℝ, L ≤ (U t k).card+1) ∧
        (∃ t c : ℝ, (t=M ∨ t=-M) ∧ (∀ i, 0 < a i+t*w i+c) ∧ (B t c k).card=L) ∧
        ∃ q : Fin (L+1) → (Fin 2 → ℝ), q 0=p k ∧ q (Fin.last L)=v ∧
          (∀ i, q i ∈ P.extremePoints ℝ) ∧
          ∀ i : Fin L, q i.castSucc ≠ q i.succ ∧
            IsExposed ℝ P (segment ℝ (q i.castSucc) (q i.succ)) := by sorry
