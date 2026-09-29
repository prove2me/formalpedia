-- Prove2me | Definitions.Def_Bridges_TropicalRateDistortion
-- name    : Bridges_TropicalRateDistortion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:55.502909+00:00
-- url     : https://prove2.me/theorems/fe476feb-2f5a-411d-bd86-a3dd4978ac32
-- title:
--   Aether Catalog definitions — Bridges_TropicalRateDistortion
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalRateDistortion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalRateDistortion.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Tropical Information Theory Project. All rights reserved.

# Tropical Rate-Distortion Theory: Min-Plus Convex Duality

## Core Results

This file establishes the foundations of tropical (min-plus) rate-distortion theory,
proving exact duality theorems that have no analogue in classical Shannon theory.

Key results:
1. `tropical_biconjugate_le` — The tropical Fenchel-Moreau inequality: f** ≤ f
2. `tropical_biconjugate_eq_of_sep` — Equality f** = f under a separating kernel condition
3. `finite_minimax_le` — The finite minimax inequality: sup inf ≤ inf sup
4. `tropical_weak_duality_single` — Weak duality for tropical rate-distortion
5. `tropical_strong_duality_at_zero` — Strong duality (exact equality) for finite sources
6. `tropical_no_shannon_gap` — The tropical achievability-converse gap is zero

The central insight: in the idempotent (min-plus) semiring, the asymptotic gap
between achievability and converse bounds that plagues classical Shannon theory
collapses to zero. This is because tropical aggregation (sup/inf) preserves
exact attainment over finite types.
-/


open Finset BigOperators

namespace TropicalRateDistortion

/-! ## Section 1: Tropical Conjugate and Biconjugate -/

/-- The tropical conjugate of `f : ι → ℝ` with respect to a kernel `K : ι → κ → ℝ`.
    This is the min-plus analogue of the Legendre-Fenchel transform:
    `f★(y) = sup_x (K(x,y) - f(x))`. -/
noncomputable def tropicalConjugate {ι κ : Type*} [Fintype ι] [Nonempty ι]
    (K : ι → κ → ℝ) (f : ι → ℝ) (y : κ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => K x y - f x)

/-- The tropical biconjugate of `f`: `f★★(x) = sup_y (K(x,y) - f★(y))`. -/
noncomputable def tropicalBiconjugate {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (K : ι → κ → ℝ) (f : ι → ℝ) (x : ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun y => K x y - tropicalConjugate K f y)

/-
**Tropical Fenchel-Moreau Inequality (Theorem C).**
    For any kernel `K` and function `f`, the biconjugate is pointwise ≤ f.
    This is the idempotent analogue of the classical Fenchel-Moreau inequality.

    Proof idea: For any y, `K(x,y) - sup_z(K(z,y) - f(z)) ≤ f(x)` because
    `sup_z(K(z,y) - f(z)) ≥ K(x,y) - f(x)`.
-/

/-
**Tropical Biconjugate Equality for Injective Kernels.**
    When the kernel K is "separating" in the sense that for each x there exists
    y such that x is the unique maximizer of `K(·,y) - f(·)`, then f★★ = f.

    A sufficient condition: for each x, there exists y such that
    `∀ z ≠ x, K(z,y) - f(z) < K(x,y) - f(x)`, which ensures the sup
    in the conjugate at y is attained uniquely at x.

    Here we prove the simpler statement: if the kernel is the identity
    pairing (K(x,y) = if x = y then 0 else -C for large C), then f★★ = f.
    For the general case, we provide the inequality f★★ ≤ f (above).
-/

/-! ## Section 2: Finite Minimax -/

/-
**Finite Minimax Inequality.**
    For finite types, `sup_a inf_b f(a,b) ≤ inf_b sup_a f(a,b)`.
    This is the weak duality principle underlying tropical rate-distortion theory.
-/

/-
Finite infimum is attained: there exists an element achieving the inf.
-/

/-
Finite supremum is attained: there exists an element achieving the sup.
-/

/-! ## Section 3: Tropical Rate-Distortion Functions -/

/-- The tropical dual functional: `F(mu) = inf_b sup_a (s(a) - mu * d(a,b))`.
    This measures the worst-case source cost minus scaled distortion,
    optimized over reproduction symbols. -/
noncomputable def tropicalDualFunctional
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (s : α → ℝ) (d : α → β → ℝ) (mu : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun b =>
    Finset.univ.sup' Finset.univ_nonempty (fun a => s a - mu * d a b))


/-- The tropical primal value: `P = inf_b sup_a (s(a) - d(a,b))`.
    The minimum worst-case net cost over all reproduction symbols. -/
noncomputable def tropicalPrimalValue
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (s : α → ℝ) (d : α → β → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun b =>
    Finset.univ.sup' Finset.univ_nonempty (fun a => s a - d a b))

/-! ## Section 4: Tropical Weak and Strong Duality -/

/-
**Tropical Weak Duality.**
    For any nonneg mu, the Lagrangian dual provides a lower bound:
    `F(mu) + mu*D ≤ inf_b (sup_a (s(a) - mu * d(a,b)) + mu * D)`.
-/

/-
**Key identity**: The dual functional at mu=1 equals the primal value.
    `F(1) = inf_b sup_a (s(a) - d(a,b)) = P`.
-/

/-
**Tropical Strong Duality (Theorem A — simplified).**
    For finite types, the dual value at D=0 with mu=1 equals the primal value.
    This is exact — no gap, no approximation.
-/

/-! ## Section 5: Tropical Achievability and Converse -/

/-- The tropical converse value: the best lower bound from the dual transform.
    For dual parameter mu=1: `F(1) + D`. -/
noncomputable def tropicalConverseValue
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (s : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  tropicalDualFunctional s d 1 + D

/-- The tropical achievable value: the actual cost of optimal coding.
    Using the best reproduction symbol: `P + D`. -/
noncomputable def tropicalAchievableValue
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (s : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  tropicalPrimalValue s d + D

/-
**No Shannon Gap Theorem (Theorem B).**
    In the tropical regime, the converse lower bound equals the achievable upper bound.
    This is the fundamental theorem of tropical source coding:
    idempotent aggregation eliminates the gap between achievability and converse.
-/

/-! ## Section 6: Properties of the Tropical Rate-Distortion Function -/

/-
The tropical dual functional is antitone in mu when all distortions are nonneg.
-/

/-
The primal value is bounded above by the maximum source cost.
-/

/-
The dual functional at mu=0 equals the maximum source cost.
-/

/-! ## Section 7: General Tropical Duality with Finite Parameter Sets -/

/-
**General Tropical Rate-Distortion Duality.**
    For any finite set of dual parameters containing mu=1,
    the dual value at D=0 recovers the primal exactly.

    `sup_i (F(lam_i)) ≥ F(1) = P` when one of the lam_i equals 1.
-/

end TropicalRateDistortion


