-- Prove2me | Definitions.Def_Bridges_NeuralCoding_WeightedDescentLorentzian
-- name    : Bridges_NeuralCoding_WeightedDescentLorentzian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:43.810287+00:00
-- url     : https://prove2.me/theorems/032b7059-d36f-4082-8c1b-a2f72d6e2ce3
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_WeightedDescentLorentzian
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.WeightedDescentLorentzian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/WeightedDescentLorentzian.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Weighted-to-Unweighted Descent for Lorentzian Supports

This file establishes a **descent pipeline** connecting weighted log-concavity
to unweighted log-concavity via weight-ratio log-convexity.

## Main Results

* `descFactorial_sq_ge` — Log-concavity of descending factorials in the index.
* `descent_inequality` — The abstract descent from weighted to unweighted log-concavity.
* `descent_inequality_nat` — The descent inequality for natural number sequences.
* `log_concave_of_descent_data` — Log-concavity from `DescentData`.
* `descFactorial_dvd_factorial` — Cross-domain: descending factorials divide factorials.

## References

* Brändén–Huh, "Lorentzian polynomials", Annals of Mathematics, 2020.
* The coefficient transport formula `coeff_iteratedPDeriv` from
  `Pythagorean.IteratedShadowGeometry`.
-/

open Finset BigOperators Nat

noncomputable section

namespace WeightedDescent

/-! ## Part 1: Descending Factorial Log-Concavity -/

/-
**Descending factorial log-concavity.** For `x ≥ k + 1` and `k ≥ 1`:
`(x.descFactorial k)² ≥ x.descFactorial (k-1) * x.descFactorial (k+1)`.

This is equivalent to showing `(x-k+1) ≥ (x-k)` after factoring, which holds
because `x ≥ k`. The descending factorial `x.descFactorial k = x(x-1)⋯(x-k+1)`
factors as `x.descFactorial (k-1) * (x - k + 1)`, and similarly
`x.descFactorial (k+1) = x.descFactorial k * (x - k)`.
-/

/-
Descending factorial is positive when `x ≥ k`.
-/

/-
Descending factorial is monotone in `x`: if `x ≤ y` then
`descFactorial x k ≤ descFactorial y k`.
-/

/-! ## Part 2: Abstract Descent Inequality -/

/-
**The abstract descent inequality.**
If `W² ≥ W₋ * W₊`, `r² ≤ r₋ * r₊`, and `W_i = r_i * S_i` with all quantities
positive, then `S² ≥ S₋ * S₊`.

Proof: From `W = r * S` we get `r² * S² ≥ r₋ * r₊ * S₋ * S₊`.
Since `r₋ * r₊ ≥ r² > 0`, dividing gives `S² ≥ S₋ * S₊`.
-/

/-
**Descent inequality for natural number sequences.**
Version with `ℕ` inputs, transported to `ℝ` for the proof.
-/

/-! ## Part 3: Novel Definition — DescentData -/

/-- **Descent data** for a finite sequence of length `d + 1`.
Packages weighted counts, unweighted counts, and weight ratios satisfying
the decomposition `W k = r k * S k`, enabling the descent pipeline.

This structure captures the algebraic essence of the weighted-to-unweighted
descent. It applies to:
- Lorentzian polynomial shadows (where `W` counts weighted support sizes)
- Matroid basis polynomials (where `S` counts independent sets)
- Mixed volume sequences (where `r` relates to Alexandrov-Fenchel ratios) -/
structure DescentData (d : ℕ) where
  /-- Weighted sequence -/
  W : Fin (d + 1) → ℝ
  /-- Unweighted sequence -/
  S : Fin (d + 1) → ℝ
  /-- Weight ratio sequence -/
  r : Fin (d + 1) → ℝ
  /-- All weighted values positive -/
  W_pos : ∀ k, 0 < W k
  /-- All unweighted values positive -/
  S_pos : ∀ k, 0 < S k
  /-- All ratios positive -/
  r_pos : ∀ k, 0 < r k
  /-- Decomposition: W = r * S -/
  decomp : ∀ k, W k = r k * S k
  /-- Weighted sequence is log-concave -/
  W_log_concave : ∀ k : Fin (d + 1),
    (k : ℕ) ≥ 1 → (k : ℕ) + 1 ≤ d →
    ∀ (hm : (k : ℕ) - 1 < d + 1) (hp : (k : ℕ) + 1 < d + 1),
    (W k) ^ 2 ≥ W ⟨(k : ℕ) - 1, hm⟩ * W ⟨(k : ℕ) + 1, hp⟩
  /-- Weight ratio is log-convex -/
  r_log_convex : ∀ k : Fin (d + 1),
    (k : ℕ) ≥ 1 → (k : ℕ) + 1 ≤ d →
    ∀ (hm : (k : ℕ) - 1 < d + 1) (hp : (k : ℕ) + 1 < d + 1),
    (r k) ^ 2 ≤ r ⟨(k : ℕ) - 1, hm⟩ * r ⟨(k : ℕ) + 1, hp⟩

/-
**Log-concavity from DescentData.**
Given valid descent data, the unweighted sequence is log-concave.
This is the main theorem of the descent pipeline, applying `descent_inequality`
at each index.
-/

/-! ## Part 4: Cross-Domain Connection — Descending Factorials and Factorials -/

/-
The descending factorial divides the ordinary factorial: `x.descFactorial k ∣ x !`.
This connects descending factorials to factorial arithmetic and provides
the bridge between the descent pipeline and binomial coefficient theory.

Cross-domain: This result combines combinatorics (descending factorials),
number theory (divisibility), and algebra (ring structure of ℕ).
-/

/-
`descFactorial x 1 = x` — base case for telescoping.
-/

/-
`descFactorial x x = x !` — the descending factorial of full length equals factorial.
-/

/-! ## Part 5: Testable Conjecture -/

/-
The naive weight-ratio log-convexity conjecture is false:
there exist positive naturals with `r₁² > r₀ * r₂`.
For the uniform matroid U_{3,6}, the weight ratios are r₀=20, r₁=10, r₂=4,
and 10² = 100 > 80 = 20 * 4.
-/

end WeightedDescent


