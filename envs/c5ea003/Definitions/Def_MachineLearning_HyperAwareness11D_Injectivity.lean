-- Prove2me | Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
-- name    : MachineLearning_HyperAwareness11D_Injectivity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:43:51.844901+00:00
-- url     : https://prove2.me/theorems/b6d2e232-b94c-4592-ad81-1ffff7330064
-- title:
--   Aether Catalog definitions — MachineLearning_HyperAwareness11D_Injectivity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HyperAwareness11D.Injectivity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HyperAwareness11D/Injectivity.lean by skeleton subtraction
import Mathlib

/-!
# Hyper-Awareness I: the exact width threshold for lossless 11-dimensional ReLU perception

This file answers, *exactly*, the central question of the research mission:

> How wide must a single ReLU layer be in order to process an 11-dimensional perception
> vector **without any dimensional reduction loss** (i.e. injectively)?

The answer proved here is **22 = 2 · 11**, and both directions are established:

* `HyperAwareness11D.two_mul_le_card_of_injective` — *lower bound.*  If a ReLU layer
  `x ↦ (relu (⟪wᵢ, x⟫ + bᵢ))ᵢ` on `ℝⁿ` is injective, then the number of output units is at
  least `2n`.  Specialised: an injective ReLU perception layer on `ℝ¹¹` needs `≥ 22` units.
* `HyperAwareness11D.doubleLayer_injective` — *upper bound.*  The "positive/negative split"
  layer `x ↦ (x⁺, x⁻)` with exactly `2n` units is injective, and is even *linearly*
  invertible (`HyperAwareness11D.doubleLayer_reconstruct`).
* `HyperAwareness11D.isLeast_width_11` — combining the two: `22` is the *least* width of an
  injective ReLU layer on 11-dimensional perception vectors.

## Structure of the lower bound proof

The argument is a hybrid of linear algebra, elementary real analysis and a finite
combinatorial duality step, and it avoids any measure theory:

1. `exists_generic_direction` (algebra: one-variable polynomials over an infinite field):
   there is a direction `u` with `⟪wᵢ, u⟫ ≠ 0` for every nonzero row `wᵢ`, obtained by
   evaluating the product of the row polynomials `∑ⱼ wᵢⱼ Xʲ` off its finite root set.
2. `card_activeRows_ge` (linear algebra + a perturbation argument): at any point `x` where
   no nonzero row is exactly at its kink, the *active* rows must have rank `n`; otherwise a
   kernel vector `v` of the active rows can be added to `x` (scaled small enough that the
   inactive rows stay inactive) without changing the output, contradicting injectivity.
   Rank `n` forces at least `n` active rows.
3. `two_mul_le_card_of_injective` (duality): far out along `±u` the active sets are exactly
   the rows with `⟪wᵢ, u⟫ > 0` resp. `< 0`; these two sets are **disjoint** and each has at
   least `n` elements, so the layer has at least `2n` units.

Step 3 is where the factor `2` — and hence the sharp constant `22` in dimension `11` — comes
from: a ReLU unit can only "see" one half-space, so a full 11-dimensional percept needs a
complete positive *and* a complete negative frame.
-/

namespace HyperAwareness11D

open Finset

noncomputable section

open scoped Classical

/-! ## Basic definitions -/

/-- The rectified linear unit. -/
def relu (t : ℝ) : ℝ := max t 0




variable {ι ι' : Type*} {n : ℕ}

/-- Pre-activation of unit `i`: `⟪wᵢ, x⟫ + bᵢ`. -/
def preAct (W : ι → Fin n → ℝ) (b : ι → ℝ) (x : Fin n → ℝ) (i : ι) : ℝ :=
  (∑ j, W i j * x j) + b i

/-- A single ReLU layer `ℝⁿ → ℝ^ι`. -/
def reluLayer (W : ι → Fin n → ℝ) (b : ι → ℝ) (x : Fin n → ℝ) : ι → ℝ :=
  fun i => relu (preAct W b x i)

/-- The units that are strictly active at `x` **and** actually depend on the input. -/
def ActiveRows [Fintype ι] (W : ι → Fin n → ℝ) (b : ι → ℝ) (x : Fin n → ℝ) : Finset ι :=
  univ.filter (fun i => 0 < preAct W b x i ∧ ∃ j, W i j ≠ 0)



/-! ## Two elementary scaling lemmas -/



/-! ## Genericity: a direction transverse to every nonzero row -/


/-! ## The local rank bound -/


/-! ## The sharp lower bound `width ≥ 2n` -/





/-! ## The matching construction: the positive/negative split layer -/

/-- The `2n`-unit "double" layer: unit `inl i` computes `x i⁺`, unit `inr i` computes `x i⁻`. -/
def doubleW (n : ℕ) : (Fin n ⊕ Fin n) → Fin n → ℝ
  | Sum.inl i, j => if i = j then 1 else 0
  | Sum.inr i, j => if i = j then -1 else 0







end

end HyperAwareness11D


