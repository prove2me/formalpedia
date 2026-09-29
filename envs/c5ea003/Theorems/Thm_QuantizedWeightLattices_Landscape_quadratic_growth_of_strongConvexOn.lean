-- Prove2me | Theorems.Thm_QuantizedWeightLattices_Landscape_quadratic_growth_of_strongConvexOn
-- name    : QuantizedWeightLattices.Landscape.quadratic_growth_of_strongConvexOn
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:07:15.014453+00:00
-- url     : https://prove2.me/theorems/e76fecae-d573-4ed0-b572-582df146d6a5
-- title:
--   Theorem L1.
-- statement:
--   **Theorem L1.**  If `f` is `μ`-strongly convex and attains its global minimum at
--   `x₀`, then it grows at least quadratically away from `x₀`.  The proof takes the
--   strong-convexity inequality along the segment `t • x + (1-t) • x₀` and lets
--   `t = 1/(n+1) → 0`.
--
--   ```lean
--   theorem QuantizedWeightLattices.Landscape.quadratic_growth_of_strongConvexOn{μ : ℝ} {f : E → ℝ} {x₀ : E}
--       (hf : StrongConvexOn univ μ f) (hmin : ∀ x, f x₀ ≤ f x) (x : E) :
--       μ / 2 * ‖x - x₀‖ ^ 2 ≤ f x - f x₀ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantizedWeightLatticesLandscape.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantizedWeightLatticesLandscape.lean#L33

-- Thm stub generated from Bridges/QuantizedWeightLatticesLandscape.lean
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
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


open QuantizedWeightLattices.Landscape

open QuantizedWeightLattices Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Section 1: strong convexity gives quadratic growth at the optimum -/

theorem QuantizedWeightLattices.Landscape.quadratic_growth_of_strongConvexOn{μ : ℝ} {f : E → ℝ} {x₀ : E}
    (hf : StrongConvexOn univ μ f) (hmin : ∀ x, f x₀ ≤ f x) (x : E) :
    μ / 2 * ‖x - x₀‖ ^ 2 ≤ f x - f x₀ := by sorry
