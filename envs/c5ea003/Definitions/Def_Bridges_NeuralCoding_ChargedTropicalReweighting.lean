-- Prove2me | Definitions.Def_Bridges_NeuralCoding_ChargedTropicalReweighting
-- name    : Bridges_NeuralCoding_ChargedTropicalReweighting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:59.958808+00:00
-- url     : https://prove2.me/theorems/cf0480d1-52d7-4b0a-b712-b79b0b7563ae
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_ChargedTropicalReweighting
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.ChargedTropicalReweighting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/ChargedTropicalReweighting.lean by skeleton subtraction
import Mathlib
/-
# Charged Tropical Reweighting: Reduction of Tropical Einstein–Maxwell to Standard Bellman

This file establishes a gauge-elimination principle in tropical dynamics:
electromagnetic forcing encoded by a gauge potential `A` and charge `q` can be absorbed
into a modified Bellman weight, converting a coupled tropical Einstein–Maxwell system
into a pure tropical Einstein equation with an effective charged potential.

## Main results

* `maxwellBellmanOp_eq_bellmanOp_charged` — The Maxwell–Bellman operator equals the
  standard Bellman operator for the charged weight `W + q • A`.
* `tropical_einstein_maxwell_iff_charged` — The tropical Einstein–Maxwell equation is
  logically equivalent to the tropical Einstein equation for `chargedWeight W A q`.
* `tropical_einstein_maxwell_fixedPoint_iff` — Fixed-point equivalence of the two operators.
* `iterate_maxwellBellmanOp_eq` — All iterates of the Maxwell–Bellman operator equal
  iterates of the charged Bellman operator (equivalence of dynamics).
* `chargedWeight_mono_charge` — Monotonicity of charged weight in the charge parameter
  when the gauge potential is nonneg.
-/


open Matrix

/-! ## Core definitions -/

/-- The charged (reweighted) transition cost matrix: `W(i,j) + q * A(i,j)`. -/
def chargedWeight {n : ℕ} (W A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => W i j + q * A i j

/-- Standard tropical Bellman operator: `(T_W Φ)(i) = ⨆ j, (W(i,j) + Φ(j))`. -/
noncomputable def bellmanOp {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (Φ : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ⨆ j : Fin n, (W i j + Φ j)

/-- Maxwell–Bellman operator with gauge coupling:
    `(T_{W,A,q} Φ)(i) = ⨆ j, (W(i,j) + q * A(i,j) + Φ(j))`. -/
noncomputable def maxwellBellmanOp {n : ℕ} (W A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ)
    (Φ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ⨆ j : Fin n, (W i j + q * A i j + Φ j)

/-- The tropical Einstein equation: `Φ(s) = (T_W Φ)(s)`. -/
noncomputable def TropicalEinsteinEquation {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (s : Fin n) (Φ : Fin n → ℝ) : Prop :=
  Φ s = bellmanOp W Φ s

/-- The tropical Einstein–Maxwell equation: `Φ(s) = (T_{W,A,q} Φ)(s)`. -/
noncomputable def TropicalEinsteinMaxwell {n : ℕ}
    (W A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n) (q : ℝ) (Φ : Fin n → ℝ) : Prop :=
  Φ s = maxwellBellmanOp W A q Φ s

/-! ## Simplification lemmas -/




/-! ## Main theorems -/

/-
**Operator equality**: The Maxwell–Bellman operator is exactly the standard Bellman
operator for the charged weight `chargedWeight W A q`. This is the core reduction.
-/




/-
**Equivalence of dynamics**: All iterates of the Maxwell–Bellman operator equal
the corresponding iterates of the charged Bellman operator.
-/

/-! ## Monotonicity corollary -/

/-
**Monotonicity in charge**: When all gauge potential entries are nonneg,
the charged weight is monotone in the charge parameter `q`.
-/

/-! ## Generalized version for arbitrary finite types -/

/-- Charged weight for function-valued weights on arbitrary types. -/
def chargedWeightFn {α : Type*} (W A : α → α → ℝ) (q : ℝ) : α → α → ℝ :=
  fun i j => W i j + q * A i j

/-- Generalized Bellman operator for arbitrary finite types using `iSup`. -/
noncomputable def bellmanOpGen {α : Type*} [Fintype α]
    (W : α → α → ℝ) (Φ : α → ℝ) : α → ℝ :=
  fun i => ⨆ j : α, (W i j + Φ j)

/-- Generalized Maxwell–Bellman operator for arbitrary finite types. -/
noncomputable def maxwellBellmanOpGen {α : Type*} [Fintype α]
    (W A : α → α → ℝ) (q : ℝ) (Φ : α → ℝ) : α → ℝ :=
  fun i => ⨆ j : α, (W i j + q * A i j + Φ j)

/-
**Generalized operator equality** for arbitrary finite types.
-/


/-
**Generalized iterate equivalence** for arbitrary finite types.
-/

/-
Charged weight addition decomposes: `chargedWeight W A (q₁ + q₂)` relates to
successive charging.
-/

/-
Zero charge gives the original weight.
-/


