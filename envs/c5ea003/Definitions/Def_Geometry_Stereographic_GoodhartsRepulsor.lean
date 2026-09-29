-- Prove2me | Definitions.Def_Geometry_Stereographic_GoodhartsRepulsor
-- name    : Geometry_Stereographic_GoodhartsRepulsor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:03.016911+00:00
-- url     : https://prove2.me/theorems/15a05211-2fda-4a5f-9dd8-8c69d8ef7e49
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_GoodhartsRepulsor
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.GoodhartsRepulsor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/GoodhartsRepulsor.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.Oracles.GoodhartsRepulsor

Auto-generated from theorem catalog database.
Domain: Computation/Oracles
Declarations: 12
-/


noncomputable section

/-- A metric space with a true objective and a proxy objective. -/
structure GoodhartSystem where
  State : Type*
  trueObj : State → ℝ
  proxyObj : State → ℝ
  step : State → State
  proxy_nondecreasing : ∀ s, proxyObj s ≤ proxyObj (step s)








/-- A fixed point is a **repulsor** if nearby perturbations move away from it. -/
def IsRepulsor {X : Type*} [MetricSpace X] (f : X → X) (x0 : X) : Prop :=
  f x0 = x0 ∧ ∃ eps : ℝ, eps > 0 ∧ ∀ x, 0 < dist x x0 → dist x x0 < eps →
    dist (f x) x0 > dist x x0




/-- A fixed point is an **attractor** if nearby points converge to it. -/
def IsAttractor {X : Type*} [MetricSpace X] (f : X → X) (x0 : X) : Prop :=
  f x0 = x0 ∧ ∃ eps : ℝ, eps > 0 ∧ ∀ x, dist x x0 < eps →
    dist (f x) x0 ≤ dist x x0








/-- An oracle that optimizes its own predictions. -/
structure SelfOptimizingOracle where
  State : Type*
  predict : State → ℝ
  optimize : State → State
  predict_nondecreasing : ∀ s, predict s ≤ predict (optimize s)








/-- The near-optimal set for an objective function. -/
def nearOptimalSet {alpha : Type*} (f : alpha → ℝ) (eps : ℝ) (M : ℝ) : Set alpha :=
  {x | f x ≥ M - eps}








/-- Model of alignment decay: over time, the proxy diverges from truth. -/
def alignmentDecay (initialCorrelation decayRate : ℝ) (t : ℕ) : ℝ :=
  initialCorrelation * decayRate ^ t












end


