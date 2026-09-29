-- Prove2me | Definitions.Def_Probability_TalagrandCertifiable
-- name    : Probability_TalagrandCertifiable
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:14.453329+00:00
-- url     : https://prove2.me/theorems/09213524-079a-4992-9d77-b99bae1b0588
-- title:
--   Aether Catalog definitions — Probability_TalagrandCertifiable
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TalagrandCertifiable`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TalagrandCertifiable.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TalagrandHypercube

/-!
# Talagrand's inequality for certifiable functionals

The corollary `Talagrand.lipschitz_concentration` uses the Lipschitz hypothesis
only to produce, for each far point `x`, a *witness weight vector* certifying
that `x` is far from `A` in a weighted Hamming metric.  Because the convex
distance dominates *every* admissible weighted Hamming distance
(`Talagrand.dHamming_sq_le_dTsq` holds for an arbitrary `w`), the witness is
allowed to depend on `x`.  This is exactly the extra freedom that makes
Talagrand's inequality strictly stronger than the bounded-differences
(Azuma–Hoeffding) inequality, and it is what the notion of a *certifiable*
functional exploits.

## Main results

* `Talagrand.certifiable_concentration` — let `f` be `1`-Lipschitz for the plain
  Hamming metric.  Suppose that every `x ∈ S` admits a *certificate* `J x`, a set
  of at most `K` coordinates such that *any* point agreeing with `x` on `J x`
  already satisfies `f ≥ m`.  If `f ≤ b` on `A` and `b ≤ m`, then
  `mass A * mass S ≤ exp (-(m - b)² / (4 K))`.
  Note that the deviation is measured on the scale `√K`, the size of a
  certificate, and **not** on the scale `√n`.
* `Talagrand.cube_ones_count_concentration` — the resulting sharpened
  concentration for the (unnormalised) number-of-ones functional on a product of
  arbitrary independent coins: the tail scale is `√m` rather than `√n`, so the
  bound is nontrivial for level sets of size `m = o(n)` where the weighted
  Lipschitz form gives nothing.
-/

namespace Talagrand

open Finset Real

variable {α : Type*} [Fintype α] [DecidableEq α]

section Certifiable

variable {n : ℕ}

/-- The weight vector attached to a certificate `J`: mass `1/√|J|` spread over the
coordinates of `J`.  It has Euclidean norm `1` when `J` is nonempty (and `0`
otherwise), so it is always admissible in `Talagrand.dHamming_sq_le_dTsq`. -/
noncomputable def certWeight (J : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ J then 1 / Real.sqrt (J.card) else 0







end Certifiable

/-! ### Application: the number of ones on a product of arbitrary independent coins -/

/-- The (unnormalised) number of ones of a point of the discrete cube. -/
noncomputable def onesCount {n : ℕ} (x : Fin n → Bool) : ℝ :=
  ∑ i, (if x i then (1 : ℝ) else 0)






end Talagrand


