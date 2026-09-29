-- Prove2me | solution 1 for QuantizedWeightLattices.Sharp.abstract_defect_bound_optimal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:38:26.787273+00:00
-- url     : https://prove2.me/submissions/117d3d4f-c711-4754-9d45-5f60fc64010a

-- Sol generated from Bridges/QuantizedWeightLatticesSharp.lean
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



/-! ## Section 4: the arithmetic tower of codebooks is dense in the weight torus -/


variable (δ : ℝ)





open QuantizedWeightLattices.Sharp in
theorem solution{r ε : ℝ} (hr : 0 < r)
    (h : ApproxConvexOn ε univ ((fun x : ℝ => |x|) ∘ (skewQuantizer hr).toFun)) :
    2 * r ≤ ε := by
  have h3 : (3 : ℝ) * r ≠ 4 * r := by intro hc; nlinarith
  have h5 : (5 : ℝ) * r ≠ 4 * r := by intro hc; nlinarith
  have e3 : (skewQuantizer hr).toFun (3 * r) = 2 * r := by
    show (if (3 * r : ℝ) = 4 * r then 5 * r else 3 * r - r) = 2 * r
    rw [if_neg h3]; ring
  have e5 : (skewQuantizer hr).toFun (5 * r) = 4 * r := by
    show (if (5 * r : ℝ) = 4 * r then 5 * r else 5 * r - r) = 4 * r
    rw [if_neg h5]; ring
  have e4 : (skewQuantizer hr).toFun (4 * r) = 5 * r := by
    show (if (4 * r : ℝ) = 4 * r then 5 * r else 4 * r - r) = 5 * r
    rw [if_pos rfl]
  have hmid : ((1 : ℝ) / 2) • (3 * r) + ((1 : ℝ) / 2) • (5 * r) = 4 * r := by
    simp only [smul_eq_mul]; ring
  have key := h (mem_univ (3 * r)) (mem_univ (5 * r))
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  rw [hmid] at key
  simp only [Function.comp_apply, e3, e4, e5] at key
  rw [abs_of_pos (by linarith : (0:ℝ) < 5 * r), abs_of_pos (by linarith : (0:ℝ) < 2 * r),
      abs_of_pos (by linarith : (0:ℝ) < 4 * r)] at key
  linarith
