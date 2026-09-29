-- Prove2me | solution 1 for Catalog.Geometry.ShallowProductCoin.prod_defect_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:20:13.800296+00:00
-- url     : https://prove2.me/submissions/ff72137e-faf0-4729-9b68-0499c66c0b05

-- Sol generated from Geometry/ShallowProductCoinRigidity.lean
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




/-! ## 2. The algebraic core of the gap

A purely real-algebraic statement: a `2 × 2` integer block of determinant `1` cannot be
approximated too well, in Frobenius norm, by a `2 × 2` block of a rank-one matrix. -/




/-! ## 3. Depth-2 product coins: the rigidity gap -/


variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]




omit [DecidableEq A] [DecidableEq B] in
lemma prodCoin_isUnitCoin {f : A → ℝ} {g : B → ℝ}
    (hf : ∑ a, f a ^ 2 = 1) (hg : ∑ b, g b ^ 2 = 1) : IsUnitCoin (prodCoin f g) := by
  unfold IsUnitCoin prodCoin
  rw [Fintype.sum_prod_type]
  have hin : ∀ a : A, ∑ b : B, (f a * g b) ^ 2 = f a ^ 2 := by
    intro a
    have hpt : ∀ b : B, (f a * g b) ^ 2 = f a ^ 2 * g b ^ 2 := by intro b; ring
    simp only [hpt, ← Finset.mul_sum, hg, mul_one]
  simp only [hin, hf]









/-! ## 4. Depth-`n` product coins -/


variable {D : Type*} [Fintype D] [DecidableEq D]









open Catalog.Geometry.ShallowProductCoin in
theorem solution(R : Finset (A × B)) (f : A → ℝ) (g : B → ℝ)
    (hf : ∑ a, f a ^ 2 = 1) (hg : ∑ b, g b ^ 2 = 1) :
    ∑ p : A × B, ((if p ∈ R then (1:ℝ) else 0)
        - resonanceAmplitude R (prodCoin f g) * f p.1 * g p.2) ^ 2
      = (R.card : ℝ) - resonanceAmplitude R (prodCoin f g) ^ 2 := by
  set t := resonanceAmplitude R (prodCoin f g) with ht
  have hexpand : ∀ p : A × B,
      ((if p ∈ R then (1:ℝ) else 0) - t * f p.1 * g p.2) ^ 2
        = (if p ∈ R then (1:ℝ) else 0)
          - 2 * t * (if p ∈ R then f p.1 * g p.2 else 0)
          + t ^ 2 * (f p.1 * g p.2) ^ 2 := by
    intro p
    by_cases hp : p ∈ R <;> simp [hp] <;> ring
  simp only [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ p : A × B, (if p ∈ R then (1:ℝ) else 0) = (R.card : ℝ) := by
    rw [Finset.sum_ite_mem]; simp
  have h2 : ∑ p : A × B, (if p ∈ R then f p.1 * g p.2 else 0) = t := by
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter]
    rfl
  have h3 : ∑ p : A × B, (f p.1 * g p.2) ^ 2 = 1 := prodCoin_isUnitCoin hf hg
  rw [h1, h2, h3]
  ring
