-- Prove2me | Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
-- name    : Bridges_QuantizedWeightLatticesLandscape
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:10.764571+00:00
-- url     : https://prove2.me/theorems/64bf5a08-5c89-4af8-bab3-9bb9193075bc
-- title:
--   Aether Catalog definitions — Bridges_QuantizedWeightLatticesLandscape
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.QuantizedWeightLatticesLandscape`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/QuantizedWeightLatticesLandscape.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLatticesSharp
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, IV: landscape invariants

Third cycle of the research loop.  Having established that grid quantization
perturbs convexity by at most `2·L·r` (file I), that the codebook is the torsion
of the weight torus (file II) and that the bound is sharp within a factor two
(file III), we now show that the *finer* invariants of the loss landscape also
survive quantization.

* `quadratic_growth_of_strongConvexOn` — strong convexity forces quadratic growth
  around a global minimiser (proved by an explicit limiting argument along
  `t = 1/(n+1)`).
* `strongConvex_quantized_minimizer_close` — consequently, for a strongly convex
  loss *every* lattice-optimal weight lies within `√(2Lr/μ)` of the true optimum.
* `quantized_approxStrongConvex` — the whole strong-convexity modulus `μ` is
  transported to the quantized landscape, with the same additive defect `2Lr`;
  in particular the curvature invariant `μ` itself is preserved exactly.
* `lattice_infimum_close` — the optimal value of the lattice-restricted problem
  and of the continuous problem differ by at most `L·r`.
-/


namespace QuantizedWeightLattices.Landscape

open QuantizedWeightLattices Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Section 1: strong convexity gives quadratic growth at the optimum -/



/-! ## Section 2: the curvature modulus survives quantization -/

/-- `ApproxStrongConvexOn ε μ s g`: `μ`-strong convexity up to an additive defect `ε`. -/
def ApproxStrongConvexOn (ε μ : ℝ) (s : Set E) (g : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    g (a • x + b • y) ≤ a * g x + b * g y - a * b * (μ / 2 * ‖x - y‖ ^ 2) + ε


/-! ## Section 3: the optimal value is preserved -/


end QuantizedWeightLattices.Landscape


