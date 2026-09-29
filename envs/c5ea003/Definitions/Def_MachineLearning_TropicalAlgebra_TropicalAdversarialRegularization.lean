-- Prove2me | Definitions.Def_MachineLearning_TropicalAlgebra_TropicalAdversarialRegularization
-- name    : MachineLearning_TropicalAlgebra_TropicalAdversarialRegularization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:00.785457+00:00
-- url     : https://prove2.me/theorems/2aa91b27-b36c-481d-9fe8-7fafe038ab11
-- title:
--   Aether Catalog definitions — MachineLearning_TropicalAlgebra_TropicalAdversarialRegularization
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TropicalAlgebra.TropicalAdversarialRegularization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TropicalAlgebra/TropicalAdversarialRegularization.lean by skeleton subtraction
import Mathlib

/-!
# Adversarial Training as Tropical Regularization

This file formalizes the equivalence between adversarial robust optimization and
tropical/min-plus regularization for finite classifiers. The key results establish:

1. **Tropical Distance = Certified Radius** (Theorem A): The min-plus distance from a
   point to the adversarial (misclassification) set equals the supremum of radii for
   which all points remain correctly classified.

2. **Robust Loss ≤ Tropical Shift** (Theorem B): Under a margin-Lipschitz hypothesis
   and antitone loss transfer, the adversarial robust loss is bounded by the loss
   evaluated at a tropically shifted (eroded) margin.

3. **Certified Radius from Margin/Lipschitz** (Theorem C): The idempotent closure
   radius is at least `margin / L`, providing a constructive certified defense.

## Mathematical Context

Adversarial perturbation in the tropical/min-plus framework becomes an infimal
convolution (erosion) of the margin function. The robust empirical risk is then
a tropical Moreau envelope, and the certified radius is the idempotent closure
of the tropical margin — connecting adversarial ML to idempotent analysis,
mathematical morphology, and Hamilton–Jacobi semigroups.

## Main Definitions

* `TropAdv.margin` — classification margin: score gap between true and best rival class
* `TropAdv.advSet` — adversarial (misclassification) set where margin ≤ 0
* `TropAdv.tropDist` — tropical distance (min-plus) to the adversarial set
* `TropAdv.robustLoss` — worst-case loss under bounded perturbations
* `TropAdv.idempotentClosureRadius` — largest radius preserving positive margin
* `TropAdv.empiricalRisk` — empirical risk over a finite dataset
* `TropAdv.tropicalRegularizedRisk` — empirical risk with tropical penalty

## Main Results

* `TropAdv.robustLoss_le_tropicalShift` — Theorem B
* `TropAdv.idempotentClosureRadius_ge_margin_div_lipschitz` — Theorem C
* `TropAdv.robustEmpiricalRisk_le_tropicalRegularizedRisk` — Empirical corollary
-/

open Finset BigOperators

noncomputable section

namespace TropAdv

variable {d c : ℕ}

/-- Auxiliary: the set of competing labels is nonempty when `c ≥ 2`. -/
private theorem erase_univ_nonempty (hc : 1 < c) (y : Fin c) :
    (Finset.univ.erase y).Nonempty := by
  have : Nontrivial (Fin c) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  exact ⟨(exists_ne y).choose,
    Finset.mem_erase.mpr ⟨(exists_ne y).choose_spec, Finset.mem_univ _⟩⟩

/-- The input space for classifiers. -/
abbrev InputSpace (d : ℕ) := Fin d → ℝ

/-- The label space for classifiers. -/
abbrev LabelSpace (c : ℕ) := Fin c

/-! ## Core Definitions -/

/-- Classification margin: the gap between the score for the true label `y` and
the maximum score among all competing labels. A positive margin means `y` is the
predicted class. When `c ≥ 2`, the set of competitors `Finset.univ.erase y` is
nonempty.

In tropical geometry, this is a tropical linear functional on the score vector. -/
def margin (score : InputSpace d → LabelSpace c → ℝ) (x : InputSpace d) (y : LabelSpace c)
    (hc : 1 < c) : ℝ :=
  score x y - Finset.sup' (Finset.univ.erase y) (erase_univ_nonempty hc y)
    (fun y' => score x y')

/-- The adversarial set (misclassification locus) for label `y`: the set of inputs
where the margin is nonpositive, meaning `y` is not strictly the top-scoring class. -/
def advSet (score : InputSpace d → LabelSpace c → ℝ) (y : LabelSpace c) (hc : 1 < c) :
    Set (InputSpace d) :=
  {x | margin score x y hc ≤ 0}


/-- Robust loss under adversarial perturbation: the supremum of the loss `φ(margin)`
over all perturbations within budget `ε`. -/
def robustLoss (cost : InputSpace d → InputSpace d → ℝ) (ε : ℝ)
    (score : InputSpace d → LabelSpace c → ℝ) (φ : ℝ → ℝ)
    (x : InputSpace d) (y : LabelSpace c) (hc : 1 < c) : ℝ :=
  sSup {z : ℝ | ∃ x', cost x x' ≤ ε ∧ z = φ (margin score x' y hc)}

/-- Idempotent closure radius: the supremum of radii `r ≥ 0` such that all points
within cost `r` of `x` have strictly positive margin. -/
def idempotentClosureRadius (cost : InputSpace d → InputSpace d → ℝ)
    (score : InputSpace d → LabelSpace c → ℝ)
    (x : InputSpace d) (y : LabelSpace c) (hc : 1 < c) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ x', cost x x' ≤ r → 0 < margin score x' y hc}


/-- Robust empirical risk: the sum of robust losses over the dataset. -/
def robustEmpiricalRisk {m : ℕ} (S : Fin m → InputSpace d × LabelSpace c)
    (cost : InputSpace d → InputSpace d → ℝ) (ε : ℝ)
    (score : InputSpace d → LabelSpace c → ℝ) (φ : ℝ → ℝ) (hc : 1 < c) : ℝ :=
  ∑ i : Fin m, robustLoss cost ε score φ (S i).1 (S i).2 hc


/-! ## Basic Lemmas -/



/-! ## Theorem B: Robust Loss ≤ Tropical Shift -/

/-
**Theorem B (Adversarial loss as tropical regularization).**

Under the margin-Lipschitz hypothesis and antitone loss transfer `φ`, the robust
loss is bounded by `φ` applied to the tropically eroded margin. This is the formal
core of "adversarial training = tropical regularization."
-/

/-! ## Theorem C: Certified Radius from Margin and Lipschitz Constant -/

/-
**Theorem C (Certified radius ≥ margin / L).**

If the margin is positive and `L`-Lipschitz, the idempotent closure radius is at
least `margin(x,y) / L`. This transforms the tropical margin into a constructive
certified defense.
-/

/-! ## Robustness Preservation -/

/-
Within the certified radius `margin/L`, every point has positive margin.
-/

/-
**Robust empirical risk bound.** The robust empirical risk is bounded by the sum
of tropically shifted losses — the dataset-level tropical regularization theorem.
-/

/-! ## Tropical Margin Properties -/

/-
Positive margin means the true label scores strictly above all competitors.
-/

/-
The margin equals the negative of the max competitor advantage (tropical duality).
-/

end TropAdv


