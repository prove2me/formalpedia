-- Prove2me | Definitions.Def_Geometry_Stereographic_HolderMoebiusFlows
-- name    : Geometry_Stereographic_HolderMoebiusFlows
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:03.409775+00:00
-- url     : https://prove2.me/theorems/346b4c67-a0c4-45e2-9aa4-3ea0bfb6ab17
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_HolderMoebiusFlows
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.HolderMoebiusFlows`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/HolderMoebiusFlows.lean by skeleton subtraction
import Mathlib
/-! # CatalogBuild.Geometry.Stereographic.HolderMoebiusFlows

Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 20
-/


noncomputable section

/-- A continuous Möbius flow parameter: interpolates between identity (t=0) and
target parameters (t=1). Uses exponential interpolation for smoothness. -/
structure MoebiusFlowParam where
  /-- Target a-parameter (complex, encoded as ℝ×ℝ) -/
  a_target : ℝ × ℝ
  /-- Target b-parameter -/
  b_target : ℝ × ℝ
  /-- Target c-parameter -/
  c_target : ℝ × ℝ
  /-- Target d-parameter -/
  d_target : ℝ × ℝ




/-- Linear interpolation between identity and target. -/
def moebiusFlowAt (p : MoebiusFlowParam) (t : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  let a := ((1 - t) * 1 + t * p.a_target.1, (1 - t) * 0 + t * p.a_target.2)
  let b := ((1 - t) * 0 + t * p.b_target.1, (1 - t) * 0 + t * p.b_target.2)
  let c := ((1 - t) * 0 + t * p.c_target.1, (1 - t) * 0 + t * p.c_target.2)
  let d := ((1 - t) * 1 + t * p.d_target.1, (1 - t) * 0 + t * p.d_target.2)
  (a, b, c, d)












/-- The conformal factor of the stereographic projection composed with a
flow-parameterized Möbius transform. -/
def moebiusFlowConformalFactor (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  2 / (1 + ∑ i, (x i) ^ 2)












/-- Hölder exponent for the flow. We require α ∈ (0, 1]. -/
def holderExponent (alpha : ℝ) : Prop :=
  0 < alpha ∧ alpha ≤ 1








/-- The Hölder seminorm bound for the flow interpolation.
|μ(t) - μ(s)| ≤ C · |t - s|^α -/
def holderBound (C alpha t s : ℝ) : ℝ :=
  C * |t - s| ^ alpha
















/-- The flow velocity (time derivative of the Möbius parameters). -/
def flowVelocity (p : MoebiusFlowParam) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  ((p.a_target.1 - 1, p.a_target.2),
   (p.b_target.1, p.b_target.2),
   (p.c_target.1, p.c_target.2),
   (p.d_target.1 - 1, p.d_target.2))




/-- The squared norm of a pair. -/
def pairSqNorm (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2




/-- The total velocity squared norm. -/
def flowVelocitySqNorm (p : MoebiusFlowParam) : ℝ :=
  let v := flowVelocity p
  pairSqNorm v.1 + pairSqNorm v.2.1 + pairSqNorm v.2.2.1 + pairSqNorm v.2.2.2












/-- Riemannian gradient descent step on the Möbius flow parameter.
We use the flat metric on the parameter space as an approximation. -/
def flowGradientStep (p : MoebiusFlowParam) (lr : ℝ)
    (grad_a grad_b grad_c grad_d : ℝ × ℝ) : MoebiusFlowParam where
  a_target := (p.a_target.1 - lr * grad_a.1, p.a_target.2 - lr * grad_a.2)
  b_target := (p.b_target.1 - lr * grad_b.1, p.b_target.2 - lr * grad_b.2)
  c_target := (p.c_target.1 - lr * grad_c.1, p.c_target.2 - lr * grad_c.2)
  d_target := (p.d_target.1 - lr * grad_d.1, p.d_target.2 - lr * grad_d.2)








end


