-- Prove2me | Theorems.Thm_Hirsch_strict_convex_chain_exact_source_rank
-- name    : Hirsch.strict_convex_chain_exact_source_rank
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-23T17:48:03.947421+00:00
-- url     : https://prove2.me/theorems/e5c0158b-f340-4262-865a-7f6936b83db1
-- title:
--   Exact tilted-height source rank on strict convex finite chains
-- statement:
--   For strictly increasing real abscissas w_i and ordinates a_i whose secant slopes are strictly increasing across every ordered triple, derive one positive tilt magnitude M working for every source k. Every real tilt has at least min(k,n-k) distinct heights above source k. The two extreme tilts -M and M have exactly k and n-k upper levels. For each source choose one of them, derive a common shift making all heights positive, and obtain exactly min(k,n-k)+1 distinct reciprocal levels below the source after adjoining target zero, hence twice that count is at most n+2. All slopes, witnesses and counts are derived. This is a finite convex-chain theorem; the reduction from arbitrary original polygons to these charts and the geometric route interpretation are written and tested separately, not asserted by the formal statement.
-- source:
--   A structural bound for the inverse-affine rank of accepted #337. Elementary strict-secant convexity forces an entire strictly monotone side above each source; extreme tilts give matching upper bounds. Reciprocal order and target zero give the exact source-rank formula. This is not a historical-priority claim or an unrestricted Polynomial Hirsch theorem. The current changing-numerator obligation is not duplicated.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.strict_convex_chain_exact_source_rank (n : ℕ) (w a : Fin (n+1) → ℝ)
    (hw : StrictMono w)
    (ha : ∀ i j k : Fin (n+1), i<j → j<k →
      (a j-a i)*(w k-w j) < (a k-a j)*(w j-w i)) :
    let U := fun (t : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => a k+t*w k<z) (fun _ => Classical.propDecidable _)
        (Finset.univ.image (fun i => a i+t*w i))
    let B := fun (t c : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => z<1/(a k+t*w k+c)) (fun _ => Classical.propDecidable _)
        (insert 0 (Finset.univ.image (fun i => 1/(a i+t*w i+c))))
    ∃ M : ℝ, 0<M ∧ ∀ k : Fin (n+1),
      (∀ t : ℝ, min k.val (n-k.val) ≤ (U t k).card) ∧
      (U (-M) k).card=k.val ∧ (U M k).card=n-k.val ∧
      ∃ t c : ℝ, (t=M ∨ t=-M) ∧ (∀ i, 0<a i+t*w i+c) ∧
        (U t k).card=min k.val (n-k.val) ∧
        (B t c k).card=min k.val (n-k.val)+1 ∧
        2*(B t c k).card ≤ n+2 := by sorry
