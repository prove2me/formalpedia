-- Prove2me | Theorems.Thm_Hirsch_moment_quantitative_neighbor_transport
-- name    : Hirsch.moment_quantitative_neighbor_transport
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-18T17:42:35.502981+00:00
-- url     : https://prove2.me/theorems/b949797e-9406-4235-9a41-19bce04cf5f9
-- title:
--   Quantitative target improvement from actual original-edge neighbor transport
-- statement:
--   For distinct actual extreme points u and v of the original d-dimensional mean-centered moment inequality system with d<m and arbitrary injective real node parameters, construct a positive first-blocking edge length and normalized release direction for each source-tight row. Every endpoint is an actual extreme point joined to u by an exposed original edge. Define the nonnegative weight at that row as target slack divided by the constructed edge length. The target displacement equals the sum of the actual edge displacements times these weights. Their sum, mass, is at least one. For the score given by the sum of target-tight original rows, construct a positive-weight outgoing neighbor with a strict improvement and mass times its improvement at least the full target-score gap. This chosen step preserves all shared target-tight rows. The public type defines the weights, mass and score explicitly; no small mass, improving-neighbor, rank, inverse, direction or path oracle is assumed. A polynomial upper bound on mass is NOT proved. The result is quantitative local progress, not a polynomial route-length or Polynomial Hirsch theorem.
-- source:
--   Reuses the accepted source prefix through Hirsch.MomentRelease from #298 as contained in accepted #301 proof daa1e4819bdee490620f6ed4df932fb98946cc1c, and the unchanged #301 row_finite_sum and target_score_strict helpers. New proof constructs weights on actual neighboring endpoints, proves their mass lower bound and derives a weighted-average improvement guarantee. Distinct from #300 separated-pair routes and #302 parity catalogue. Classical cone/weighted-average mathematics is credited, without a historical novelty claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_quantitative_neighbor_transport (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let I : Finset (Fin m) := Finset.univ.filter (fun i => row u i = 1)
    let J : Finset (Fin m) := Finset.univ.filter (fun i => row v i = 1)
    let score : (Fin d → ℝ) → ℝ := fun x => ∑ i ∈ J, row x i
    u ∈ P.extremePoints ℝ → v ∈ P.extremePoints ℝ → u ≠ v →
      ∃ (w : I → (Fin d → ℝ)) (t : I → ℝ),
        (∀ p : I, 0 < t p ∧
          (∀ i : I, row (w p) i.val = if i = p then -1 else 0) ∧
          u + t p • w p ∈ P.extremePoints ℝ ∧
          IsExposed ℝ P (segment ℝ u (u + t p • w p))) ∧
        let b : I → ℝ := fun p => (1-row v p.val) / t p
        let mass : ℝ := ∑ p : I, b p
        (∀ p, 0 ≤ b p) ∧ 1 ≤ mass ∧
        v-u = ∑ p : I, b p • ((u + t p • w p)-u) ∧
        ∃ p : I, 0 < b p ∧ score u < score (u + t p • w p) ∧
          score v-score u ≤ mass * (score (u + t p • w p)-score u) ∧
          ∀ i : Fin m, row u i = 1 → row v i = 1 →
            row (u + t p • w p) i = 1 := by sorry
