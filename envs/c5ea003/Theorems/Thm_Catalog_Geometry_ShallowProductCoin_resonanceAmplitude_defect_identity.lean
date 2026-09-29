-- Prove2me | Theorems.Thm_Catalog_Geometry_ShallowProductCoin_resonanceAmplitude_defect_identity
-- name    : Catalog.Geometry.ShallowProductCoin.resonanceAmplitude_defect_identity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:08:42.498215+00:00
-- url     : https://prove2.me/theorems/3a91f425-64a1-44fa-b3d6-324bd0902f89
-- title:
--   Exact Cauchy–Schwarz defect identity.
-- statement:
--   **Exact Cauchy–Schwarz defect identity.**  For a unit coin the gap `|R| - A(psi)^2`
--   equals `|R|` times the squared `ℓ²`-distance from `psi` to the best scalar multiple of
--   the indicator of `R`.
--
--   ```lean
--   theorem Catalog.Geometry.ShallowProductCoin.resonanceAmplitude_defect_identity(R : Finset X) (psi : X → ℝ)
--       (hpsi : IsUnitCoin psi) (hR : R.Nonempty) :
--       (R.card : ℝ) - resonanceAmplitude R psi ^ 2 =
--         R.card * ∑ x, (psi x -
--           (resonanceAmplitude R psi / R.card) * (if x ∈ R then (1:ℝ) else 0)) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ShallowProductCoinRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ShallowProductCoinRigidity.lean#L64

-- Thm stub generated from Geometry/ShallowProductCoinRigidity.lean
import Mathlib
import Definitions.Def_Geometry_ShallowProductCoinRigidity
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

open Catalog.Geometry.ShallowProductCoin

open Finset

/-! ## 1. Resonance amplitude and the exact Cauchy–Schwarz defect -/



variable {X : Type*} [Fintype X] [DecidableEq X]

theorem Catalog.Geometry.ShallowProductCoin.resonanceAmplitude_defect_identity(R : Finset X) (psi : X → ℝ)
    (hpsi : IsUnitCoin psi) (hR : R.Nonempty) :
    (R.card : ℝ) - resonanceAmplitude R psi ^ 2 =
      R.card * ∑ x, (psi x -
        (resonanceAmplitude R psi / R.card) * (if x ∈ R then (1:ℝ) else 0)) ^ 2 := by sorry
