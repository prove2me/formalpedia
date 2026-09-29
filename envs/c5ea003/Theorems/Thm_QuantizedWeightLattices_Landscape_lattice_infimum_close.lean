-- Prove2me | Theorems.Thm_QuantizedWeightLattices_Landscape_lattice_infimum_close
-- name    : QuantizedWeightLattices.Landscape.lattice_infimum_close
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:06:55.217657+00:00
-- url     : https://prove2.me/theorems/58a37a82-9e7d-48ab-9b4c-793e24fb15e6
-- title:
--   Theorem L4 (optimal-value stability).
-- statement:
--   **Theorem L4 (optimal-value stability).**  The optimum of the lattice-restricted
--   training problem and the optimum of the continuous problem differ by at most
--   `L·r`.  Quantization therefore preserves the *value* of the global optimum, the
--   coarsest invariant of the loss landscape.
--
--   ```lean
--   theorem QuantizedWeightLattices.Landscape.lattice_infimum_close[Nonempty E] {L : NNReal} {f : E → ℝ}
--       (hL : LipschitzWith L f) (Q : Quantizer E) (hbdd : BddBelow (Set.range f)) :
--       sInf (Set.range f) ≤ sInf (f '' Set.range Q.toFun) ∧
--         sInf (f '' Set.range Q.toFun) ≤ sInf (Set.range f) + (L : ℝ) * Q.radius := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantizedWeightLatticesLandscape.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantizedWeightLatticesLandscape.lean#L108

-- Thm stub generated from Bridges/QuantizedWeightLatticesLandscape.lean
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
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



/-! ## Section 2: the curvature modulus survives quantization -/



/-! ## Section 3: the optimal value is preserved -/

omit [NormedSpace ℝ E] in

theorem QuantizedWeightLattices.Landscape.lattice_infimum_close[Nonempty E] {L : NNReal} {f : E → ℝ}
    (hL : LipschitzWith L f) (Q : Quantizer E) (hbdd : BddBelow (Set.range f)) :
    sInf (Set.range f) ≤ sInf (f '' Set.range Q.toFun) ∧
      sInf (f '' Set.range Q.toFun) ≤ sInf (Set.range f) + (L : ℝ) * Q.radius := by sorry
