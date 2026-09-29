-- Prove2me | Theorems.Thm_QuantizedWeightLattices_Sharp_abstract_defect_bound_optimal
-- name    : QuantizedWeightLattices.Sharp.abstract_defect_bound_optimal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:07:47.423266+00:00
-- url     : https://prove2.me/theorems/7a9c1384-607b-4670-8b5f-7990030f32ef
-- title:
--   Theorem S6 (optimality of the constant in Theorem A).
-- statement:
--   **Theorem S6 (optimality of the constant in Theorem A).**  Over the class of all
--   quantizers of covering radius `r` the defect `2·L·r` of `quantized_approxConvex`
--   cannot be improved at all: the convex `1`-Lipschitz loss `|·|` composed with
--   `skewQuantizer` has defect exactly `2r`.  Together with Theorem S3 this delimits
--   the problem precisely — a possible improvement by a factor two would be a
--   statement about *nearest-point* quantizers, not about the abstract bound.
--
--   ```lean
--   theorem QuantizedWeightLattices.Sharp.abstract_defect_bound_optimal{r ε : ℝ} (hr : 0 < r)
--       (h : ApproxConvexOn ε univ ((fun x : ℝ => |x|) ∘ (skewQuantizer hr).toFun)) :
--       2 * r ≤ ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantizedWeightLatticesSharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantizedWeightLatticesSharp.lean#L136

-- Thm stub generated from Bridges/QuantizedWeightLatticesSharp.lean
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesModular
import Definitions.Def_Bridges_QuantizedWeightLatticesSharp
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, III: sharpness and density

Adversarial (Stage 4) companion to the two previous files.  Two questions are
answered here.

**Is the convexity-preservation theorem vacuous?**  No.  For the archetypal convex
`1`-Lipschitz loss `x ↦ |x|` the `δ`-grid quantized landscape is *provably not
convex*: its convexity defect is at least `δ/2` (`quantized_abs_defect_ge`), while
Theorem A bounds it by `δ`.  Hence the constant `2·L·r` of Theorem A is sharp up
to a factor of two (`defect_bound_sharp`), and the phrase "convexity is preserved"
must be read in the quantitative, approximate sense — exact convexity really is
destroyed (`quantized_abs_not_convex`).  Moreover, over the *whole* class of
radius-`r` quantizers the constant `2·L·r` is exactly optimal
(`abstract_defect_bound_optimal`): the residual factor-two question concerns only
nearest-point projections.

**How rich is the arithmetic of the codebook tower?**  The `m`-level codebooks are
the torsion subgroups of the weight torus `ℝ/δℤ`; they form a divisibility tower
with index `m'/m` (`torsion_card_ratio`) whose union — the full torsion subgroup,
an avatar of `ℚ/ℤ` — is **dense** in the weight torus
(`dense_quantization_tower`).  This is the arithmetic mechanism behind the reverse
transfer theorem (Theorem E): the tower of finite codebooks sees all of weight
space in the limit.
-/


open QuantizedWeightLattices.Sharp

open QuantizedWeightLattices QuantizedWeightLattices.Modular Set

/-! ## Section 1: the scalar quantizer and the model loss `|·|` -/




/-! ## Section 2: three explicit rounding computations -/




/-! ## Section 3: the convexity defect of a quantized convex loss is genuinely positive -/




/-! ## Section 3b: for general quantizers the constant `2·L·r` is exactly optimal -/

theorem QuantizedWeightLattices.Sharp.abstract_defect_bound_optimal{r ε : ℝ} (hr : 0 < r)
    (h : ApproxConvexOn ε univ ((fun x : ℝ => |x|) ∘ (skewQuantizer hr).toFun)) :
    2 * r ≤ ε := by sorry
