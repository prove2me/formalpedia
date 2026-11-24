-- Prove2me | solution 1 for Cryptography.WeilBLS.AltPairing.pair_coords
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:33:03.667306+00:00
-- url     : https://prove2.me/submissions/5982f8bf-884c-4881-a02f-62f404f6be56

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

universe u v

namespace Cryptography.WeilBLS.AltPairing

private theorem pair_zero_left_aux {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    {E : AltPairing A μ} (y : A) : E.pair 0 y = 1 := by
  simp [pair]

private theorem pair_add_left_aux {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    {E : AltPairing A μ} (x y z : A) : E.pair (x + y) z = E.pair x z * E.pair y z := by
  simp [pair, map_add]

private theorem pair_add_right_aux {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    {E : AltPairing A μ} (x y z : A) : E.pair x (y + z) = E.pair x y * E.pair x z := by
  simp [pair, map_add]

private theorem pair_self_aux {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    {E : AltPairing A μ} (x : A) : E.pair x x = 1 := by
  simp [pair, E.alternating x]

private theorem pair_zsmul_left_aux {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    {E : AltPairing A μ} (a : ℤ) (x y : A) : E.pair (a • x) y = E.pair x y ^ a := by
  simp [pair, map_zsmul]

private theorem pair_zsmul_right_aux {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    {E : AltPairing A μ} (b : ℤ) (x y : A) : E.pair x (b • y) = E.pair x y ^ b := by
  simp [pair, map_zsmul]

private theorem pair_neg_left_aux {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    {E : AltPairing A μ} (x y : A) : E.pair (-x) y = (E.pair x y)⁻¹ := by
  have h : E.pair (-x) y * E.pair x y = 1 := by
    rw [← pair_add_left_aux, neg_add_cancel, pair_zero_left_aux]
  exact eq_inv_of_mul_eq_one_left h

private theorem skew_aux {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    {E : AltPairing A μ} (x y : A) : E.pair y x = (E.pair x y)⁻¹ := by
  have h := pair_self_aux (E := E) (x + y)
  rw [pair_add_left_aux, pair_add_right_aux, pair_add_right_aux, pair_self_aux, pair_self_aux,
    one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

end Cryptography.WeilBLS.AltPairing

open Cryptography.WeilBLS Cryptography.WeilBLS.AltPairing

theorem solution {A : Type u} [AddCommGroup A] {μ : Type v} [CommGroup μ]
    (E : AltPairing A μ) (e₁ e₂ : A) (a b c d : ℤ) :
    E.pair (a • e₁ + b • e₂) (c • e₁ + d • e₂) = E.pair e₁ e₂ ^ (a * d - b * c) := by
  rw [pair_add_left_aux, pair_add_right_aux, pair_add_right_aux, pair_zsmul_left_aux,
    pair_zsmul_left_aux, pair_zsmul_left_aux, pair_zsmul_left_aux, pair_zsmul_right_aux,
    pair_zsmul_right_aux, pair_zsmul_right_aux, pair_zsmul_right_aux, pair_self_aux, pair_self_aux,
    skew_aux e₁ e₂, zpow_sub]
  simp [← zpow_mul, mul_comm]

#print axioms solution
