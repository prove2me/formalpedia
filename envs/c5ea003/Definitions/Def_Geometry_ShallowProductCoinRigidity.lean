-- Prove2me | Definitions.Def_Geometry_ShallowProductCoinRigidity
-- name    : Geometry_ShallowProductCoinRigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:26.237742+00:00
-- url     : https://prove2.me/theorems/72a17a31-dae0-4542-b74c-9f2c85bd59c3
-- title:
--   Aether Catalog definitions — Geometry_ShallowProductCoinRigidity
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ShallowProductCoinRigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ShallowProductCoinRigidity.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Rigidity gap for shallow product coins

## Setting

A *resonance set* is a finite set `R` of states inside a finite state space `X`.
A *coin* is a real weight function `psi : X → ℝ` normalised so that `∑ x, psi x ^ 2 = 1`.
Its *resonance amplitude* is

  `A(psi) = ∑ x ∈ R, psi x`.

Cauchy–Schwarz gives `A(psi) ^ 2 ≤ |R|`, with equality exactly for the (normalised)
indicator of `R`.  This file makes that rigidity **quantitative** for the class of
*product coins*, i.e. coins that factor over the coordinates of the state and hence
cannot "see" the global shape of `R`.

## Main results

* `resonanceAmplitude_defect_identity` — the exact identity
  `|R| - A(psi)^2 = |R| * ∑ x, (psi x - (A/|R|) * 1_R x)^2`.
* `resonanceAmplitude_sq_le` — `A(psi)^2 ≤ |R|`.
* `resonanceAmplitude_sq_eq_iff` — equality holds iff `psi` is a scalar multiple of `1_R`.
* `productCoin_amplitude_sq_le_of_not_box` — **depth-2 rigidity gap.**  If `R ⊆ A × B`
  is not a combinatorial box, then *every* unit product coin `f ⊗ g` satisfies
  `A(f ⊗ g)^2 ≤ |R| - 1/(9 |R|)`.
* `productCoin_amplitude_sq_le_mul_of_not_box` — the same in the form
  `A(f ⊗ g)^2 ≤ (1 - c) |R|` with `c = 1/(9|R|^2) > 0`.
* `productCoin_depth_amplitude_sq_le_of_not_box`,
  `productCoin_depth_amplitude_sq_le_mul_of_not_box` — **depth-`n` rigidity gap** with
  the *same* constant `c = 1/(9|R|^2)`, uniform in the depth `n`.

The constant is explicit and depends only on `|R|`; the hypothesis `|R| ≥ 2` is
automatic from the non-box witness (`two_le_card_of_not_box`).

## Proof mechanism

Write `M` for the 0/1 indicator matrix of `R ⊆ A × B` and `t` for the amplitude of a
unit product coin `f ⊗ g`.  Then `E := M - t · f gᵀ` obeys the exact Pythagoras identity
`‖E‖_F^2 = |R| - t^2` (`prod_defect_identity`).  Failure of `R` to be a box produces a
`2 × 2` submatrix of `M` of determinant `1`, while the corresponding `2 × 2` submatrix of
the rank-one matrix `t · f gᵀ` has determinant `0`.  Expanding the determinant of `M`
along `E` and applying the four-term Cauchy–Schwarz inequality forces
`‖E‖_F^2 ≥ 1/(9|R|)` (`rigidity_gap_core`).
-/

namespace Catalog.Geometry.ShallowProductCoin

open Finset

/-! ## 1. Resonance amplitude and the exact Cauchy–Schwarz defect -/

/-- The resonance amplitude of a coin `psi` against a resonance set `R`. -/
def resonanceAmplitude {X : Type*} (R : Finset X) (psi : X → ℝ) : ℝ := ∑ x ∈ R, psi x

/-- A coin is *unit* when its `ℓ²` mass over the whole state space is `1`. -/
def IsUnitCoin {X : Type*} [Fintype X] (psi : X → ℝ) : Prop := ∑ x, psi x ^ 2 = 1

variable {X : Type*} [Fintype X] [DecidableEq X]




/-! ## 2. The algebraic core of the gap

A purely real-algebraic statement: a `2 × 2` integer block of determinant `1` cannot be
approximated too well, in Frobenius norm, by a `2 × 2` block of a rank-one matrix. -/




/-! ## 3. Depth-2 product coins: the rigidity gap -/

section Depth2

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A resonance set `R ⊆ A × B` is a *combinatorial box* when it is closed under the
rectangle rule: whenever `(a,b)` and `(a',b')` belong to `R`, so does `(a,b')`.
Equivalently `R` is the product of its two projections. -/
def IsBox (R : Finset (A × B)) : Prop :=
  ∀ a a' b b', (a, b) ∈ R → (a', b') ∈ R → (a, b') ∈ R


/-- The product (depth-2) coin built from the factors `f` and `g`. -/
def prodCoin (f : A → ℝ) (g : B → ℝ) : A × B → ℝ := fun p => f p.1 * g p.2









end Depth2

/-! ## 4. Depth-`n` product coins -/

section DepthN

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A depth-`n` product coin: `psi x = ∏ i, f i (x i)`. -/
def depthCoin {n : ℕ} (f : Fin n → D → ℝ) : (Fin n → D) → ℝ := fun x => ∏ i, f i (x i)


/-- The state-space splitting `D^(n+1) ≃ D × D^n` peeling off the first coordinate. -/
def peel (n : ℕ) : (Fin (n + 1) → D) ≃ D × (Fin n → D) := (Fin.consEquiv fun _ => D).symm




end DepthN

end Catalog.Geometry.ShallowProductCoin


