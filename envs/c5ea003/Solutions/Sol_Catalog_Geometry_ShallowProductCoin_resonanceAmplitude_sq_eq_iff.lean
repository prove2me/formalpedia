-- Prove2me | solution 1 for Catalog.Geometry.ShallowProductCoin.resonanceAmplitude_sq_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:40:26.771705+00:00
-- url     : https://prove2.me/submissions/54c89a69-bc08-4de5-a222-ae6ec7ecd9ce

-- Sol generated from Geometry/ShallowProductCoinRigidity.lean
import Mathlib
import Definitions.Def_Geometry_ShallowProductCoinRigidity
import Theorems.Thm_Catalog_Geometry_ShallowProductCoin_resonanceAmplitude_defect_identity
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













/-! ## 4. Depth-`n` product coins -/


variable {D : Type*} [Fintype D] [DecidableEq D]









open Catalog.Geometry.ShallowProductCoin in
theorem solution(R : Finset X) (psi : X → ℝ)
    (hpsi : IsUnitCoin psi) (hR : R.Nonempty) :
    resonanceAmplitude R psi ^ 2 = R.card ↔
      ∃ c : ℝ, ∀ x, psi x = c * (if x ∈ R then (1:ℝ) else 0) := by
  have hcard : (0:ℝ) < R.card := by exact_mod_cast Finset.card_pos.mpr hR
  have hid := resonanceAmplitude_defect_identity R psi hpsi hR
  constructor
  · intro heq
    refine ⟨resonanceAmplitude R psi / R.card, ?_⟩
    have hzero : ∑ x, (psi x -
        (resonanceAmplitude R psi / R.card) * (if x ∈ R then (1:ℝ) else 0)) ^ 2 = 0 := by
      have hmul : (R.card : ℝ) * ∑ x, (psi x -
          (resonanceAmplitude R psi / R.card) * (if x ∈ R then (1:ℝ) else 0)) ^ 2 = 0 := by
        rw [← hid, heq]; ring
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h (ne_of_gt hcard)
      · exact h
    intro x
    have hx0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (univ : Finset X)) => sq_nonneg _)).mp hzero x (mem_univ x)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx0
    linarith
  · rintro ⟨c, hcf⟩
    have hA : resonanceAmplitude R psi = c * R.card := by
      simp only [resonanceAmplitude, hcf]
      simp [mul_comm]
    have hnorm : (c ^ 2) * R.card = 1 := by
      have hsq : ∑ x, psi x ^ 2 = c ^ 2 * R.card := by
        simp only [hcf]
        have hpt : ∀ x : X, (c * (if x ∈ R then (1:ℝ) else 0)) ^ 2
            = c ^ 2 * (if x ∈ R then (1:ℝ) else 0) := by
          intro x; by_cases hx : x ∈ R <;> simp [hx]
        simp only [hpt, ← Finset.mul_sum]
        simp [mul_comm]
      rw [← hsq]; exact hpsi
    rw [hA]
    nlinarith [hnorm]
