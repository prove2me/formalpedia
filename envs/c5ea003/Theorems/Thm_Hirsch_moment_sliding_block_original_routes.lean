-- Prove2me | Theorems.Thm_Hirsch_moment_sliding_block_original_routes
-- name    : Hirsch.moment_sliding_block_original_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T20:10:39.994103+00:00
-- url     : https://prove2.me/theorems/e7f0c684-2c01-4076-b964-68ec03d676ad
-- title:
--   Consecutive even root blocks construct bounded original-edge routes in moment systems
-- statement:
--   For any strictly increasing real sequence a indexed by natural numbers, positive k and finite original prefix of m labels with 2k<m, and s,L with s+L+2k<=m, construct L+1 distinct actual extreme points of the ORIGINAL dimension-2k mean-centered moment halfspace intersection. Point t has precisely the consecutive original labels s+t through s+t+2k-1 tight. Every successive segment is an actual exposed subset of the original feasible set. Every original row is tight along an interval of the constructed path, and L<=m-2k. No feasible point, exchange sequence, rank, exposedness or short-path oracle is assumed. This is a constructed class of routes through consecutive-block vertices, not a route between all arbitrary vertices or a solution of Polynomial Hirsch.
-- source:
--   Builds on accepted #295 Hirsch.moment_common_rows_expose_edges and its unchanged namespace prefix, using exact consecutive-root support polynomials. The paired/cyclic moment combinatorics are classical; compare Maksimenko (2009), The diameter of the ridge-graph of a cyclic polytope, DOI10.1515/DMA.2009.003. No historical-priority or improved general cyclic diameter claim.

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Hirsch
theorem moment_sliding_block_original_routes (k m s L : ℕ) (hk : 0 < k) (hm : 2*k < m)
    (hfit : s+L+2*k ≤ m) (a : ℕ → ℝ) (ha : StrictMono a) :
    let row : (Fin (2*k) → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin (2*k),
        (a i.val ^ (j.val+1) - (∑ l : Fin m, a l.val ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin (2*k) → ℝ) := {x | ∀ i : Fin m, row x i ≤ 1}
    L ≤ m-2*k ∧
    ∃ p : Fin (L+1) → (Fin (2*k) → ℝ), Function.Injective p ∧
      (∀ t : Fin (L+1), p t ∈ P.extremePoints ℝ ∧
        (∀ i : Fin m, row (p t) i ≤ 1) ∧
        ∀ i : Fin m, row (p t) i = 1 ↔
          s+t.val ≤ i.val ∧ i.val < s+t.val+2*k) ∧
      (∀ t : Fin L, IsExposed ℝ P (segment ℝ (p t.castSucc) (p t.succ))) ∧
      (∀ i : Fin m, ∀ t u v : Fin (L+1), t ≤ u → u ≤ v →
        row (p t) i = 1 → row (p v) i = 1 → row (p u) i = 1) := by sorry
end Hirsch
