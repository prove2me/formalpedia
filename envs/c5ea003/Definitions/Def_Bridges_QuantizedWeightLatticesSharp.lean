-- Prove2me | Definitions.Def_Bridges_QuantizedWeightLatticesSharp
-- name    : Bridges_QuantizedWeightLatticesSharp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:06.221951+00:00
-- url     : https://prove2.me/theorems/a1e6cbd9-ab32-42f2-b087-1625d4149fc9
-- title:
--   Aether Catalog definitions — Bridges_QuantizedWeightLatticesSharp
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.QuantizedWeightLatticesSharp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/QuantizedWeightLatticesSharp.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesModular
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


namespace QuantizedWeightLattices.Sharp

open QuantizedWeightLattices QuantizedWeightLattices.Modular Set

/-! ## Section 1: the scalar quantizer and the model loss `|·|` -/

/-- The scalar grid quantizer on `ℝ` as an abstract `Quantizer`. -/
noncomputable def scalarQuantizer {δ : ℝ} (hδ : 0 < δ) : Quantizer ℝ where
  toFun := gridRound δ
  radius := δ / 2
  radius_nonneg := by positivity
  error_le := fun x => by simpa [Real.norm_eq_abs] using gridRound_error hδ x



/-! ## Section 2: three explicit rounding computations -/




/-! ## Section 3: the convexity defect of a quantized convex loss is genuinely positive -/




/-! ## Section 3b: for general quantizers the constant `2·L·r` is exactly optimal -/

/-- A quantizer of radius `r` that displaces every weight by exactly `r`, moving the
sample points `3r, 5r` *inwards* but their midpoint `4r` *outwards*.  It is a
legitimate `Quantizer` (its displacement never exceeds the radius) but it is not a
nearest-point lattice projection. -/
noncomputable def skewQuantizer {r : ℝ} (hr : 0 < r) : Quantizer ℝ where
  toFun := fun x => if x = 4 * r then 5 * r else x - r
  radius := r
  radius_nonneg := hr.le
  error_le := fun x => by
    rcases eq_or_ne x (4 * r) with h | h
    · have hval : ‖(if x = 4 * r then 5 * r else x - r) - x‖ = r := by
        rw [if_pos h, h, Real.norm_eq_abs, show 5 * r - 4 * r = r by ring, abs_of_pos hr]
      exact le_of_eq hval
    · have hval : ‖(if x = 4 * r then 5 * r else x - r) - x‖ = r := by
        rw [if_neg h, Real.norm_eq_abs, show x - r - x = -r by ring, abs_neg, abs_of_pos hr]
      exact le_of_eq hval


/-! ## Section 4: the arithmetic tower of codebooks is dense in the weight torus -/

section Tower

variable (δ : ℝ)



end Tower

end QuantizedWeightLattices.Sharp


