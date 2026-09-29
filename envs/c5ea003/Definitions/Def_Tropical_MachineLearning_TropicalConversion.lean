-- Prove2me | Definitions.Def_Tropical_MachineLearning_TropicalConversion
-- name    : Tropical_MachineLearning_TropicalConversion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:09.909803+00:00
-- url     : https://prove2.me/theorems/f5374d0e-ca11-4e67-b894-12a5360c3137
-- title:
--   Aether Catalog definitions — Tropical_MachineLearning_TropicalConversion
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.MachineLearning.TropicalConversion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/MachineLearning/TropicalConversion.lean by skeleton subtraction
import Mathlib

/-! # Tropical Neural Network Conversion — Formal Foundations

This file formalizes the core mathematical guarantees for converting
classical neural network layers to tropical (max-plus) representations.

## Key Results

1. **`relu_is_tropical`** — ReLU(x) = max(x, 0) is a tropical operation.
2. **`tropMul_distrib_left`** — Tropical multiplication distributes over tropical addition.
3. **`relu_conversion_exact`** — Converting ReLU layers to tropical form is exact.
4. **`softmax_concentration`** — Softmax concentrates on the argmax as β → ∞.
5. **`convError_triangle`** — Composition errors compose via triangle inequality.
-/

noncomputable section

open Real Finset BigOperators

-- ═══════════════════════════════════════════════════════════════
-- Section 1: Tropical Semiring Operations
-- ═══════════════════════════════════════════════════════════════

/-- Tropical addition is max. -/
def tropAdd' (a b : ℝ) : ℝ := max a b

/-- Tropical multiplication is classical addition. -/
def tropMul' (a b : ℝ) : ℝ := a + b






-- ═══════════════════════════════════════════════════════════════
-- Section 2: ReLU is Tropical
-- ═══════════════════════════════════════════════════════════════

/-- ReLU function. -/
def reluFn (x : ℝ) : ℝ := max x 0




-- ═══════════════════════════════════════════════════════════════
-- Section 3: Conversion Error Bounds
-- ═══════════════════════════════════════════════════════════════

/-- Conversion error between two functions. -/
def convError (f g : ℝ → ℝ) (x : ℝ) : ℝ := |f x - g x|






-- ═══════════════════════════════════════════════════════════════
-- Section 4: Quantization Error
-- ═══════════════════════════════════════════════════════════════



/-
═══════════════════════════════════════════════════════════════
Section 5: Softmax Concentration (Tropical Limit)
═══════════════════════════════════════════════════════════════

Softmax converges to hardmax (tropical) as temperature → 0.
    For distinct scores, the argmax gets probability → 1.
    Here: exp(β·s₂) / (exp(β·s₁) + exp(β·s₂)) > 1/2 when s₂ > s₁.
-/

end


