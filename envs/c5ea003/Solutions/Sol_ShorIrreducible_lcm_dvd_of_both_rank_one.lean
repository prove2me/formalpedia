-- Prove2me | solution 1 for ShorIrreducible.lcm_dvd_of_both_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:46:37.54623+00:00
-- url     : https://prove2.me/submissions/613533e5-5d26-4c05-9ee6-538e91299f7d

import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorQFTOutputState

set_option maxHeartbeats 2000000 in
open Finset Matrix IITTensorNetwork ShorIrreducible in
theorem solution {B C r m x0 j Q : ℕ} {amp : ℝ} [NeZero r] [NeZero m]
    (hamp : amp ≠ 0) (hr : 0 < r) (hm : 0 < m) (hC : 2 ≤ C) (hrB : r ≤ B) (hmB : m ≤ B)
    (hin : schmidtRank (combCutMatrix B C r x0 amp) = 1)
    (hout : schmidtRank (outputCutMatrix B C m j Q amp) = 1) :
    Nat.lcm r m ∣ B := by
  classical
  have hB : 0 < B := lt_of_lt_of_le hr hrB
  have hampC : (amp : ℂ) ≠ 0 := by exact_mod_cast hamp
  simp only [schmidtRank] at hin hout
  ---- an antidiagonal 2x2 pattern forces rank at least 2
  have rank2 : ∀ (A : Matrix (Fin B) (Fin C) ℂ) (b1 b2 : Fin B) (c1 c2 : Fin C),
      A b1 c1 ≠ 0 → A b1 c2 = 0 → A b2 c1 = 0 → A b2 c2 ≠ 0 → 2 ≤ A.rank := by
    intro A b1 b2 c1 c2 h11 h12 h21 h22
    have hsub : (A.submatrix ![b1, b2] ![c1, c2]).rank ≤ A.rank :=
      Matrix.rank_submatrix_le A ![b1, b2] ![c1, c2]
    have hdet : (A.submatrix ![b1, b2] ![c1, c2]).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, h12, h21, mul_zero, zero_mul, sub_zero]
      exact mul_ne_zero h11 h22
    have hunit : IsUnit (A.submatrix ![b1, b2] ![c1, c2]) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hrk : (A.submatrix ![b1, b2] ![c1, c2]).rank = 2 := by
      rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
    omega
  ---- shifting a residue by a nonzero amount less than the modulus changes it
  have hmodne : ∀ (n a t : ℕ), a < n → t < n → 0 < t → (a + t) % n ≠ a := by
    intro n a t ha ht ht0
    rcases lt_or_ge (a + t) n with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  ---- if n does not divide B, columns 0 and 1 carry an antidiagonal residue pattern
  have hcomb : ∀ n u : ℕ, 0 < n → ¬ (n ∣ B) →
      ∃ p q : ℕ, p < n ∧ q < n ∧
        (p + B * 0) % n = u % n ∧ (p + B * 1) % n ≠ u % n ∧
        (q + B * 0) % n ≠ u % n ∧ (q + B * 1) % n = u % n := by
    intro n u hn hnd
    have hs0 : 0 < B % n := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
    have hslt : B % n < n := Nat.mod_lt _ hn
    have hplt : u % n < n := Nat.mod_lt _ hn
    have hqlt : (u % n + (n - B % n)) % n < n := Nat.mod_lt _ hn
    refine ⟨u % n, (u % n + (n - B % n)) % n, hplt, hqlt, ?_, ?_, ?_, ?_⟩
    · rw [mul_zero, Nat.add_zero]
      exact Nat.mod_mod_of_dvd _ (dvd_refl n)
    · rw [mul_one]
      have key : (u % n + B) % n = (u % n + B % n) % n :=
        Nat.ModEq.add_left _ (Nat.mod_modEq B n).symm
      rw [key]
      exact hmodne n (u % n) (B % n) hplt hslt hs0
    · rw [mul_zero, Nat.add_zero, Nat.mod_mod_of_dvd _ (dvd_refl n)]
      exact hmodne n (u % n) (n - B % n) hplt (by omega) (by omega)
    · rw [mul_one]
      have key : (u % n + (n - B % n)) % n + B ≡ u % n + n [MOD n] := by
        calc (u % n + (n - B % n)) % n + B
            ≡ (u % n + (n - B % n)) + B [MOD n] := Nat.ModEq.add_right B (Nat.mod_modEq _ n)
          _ ≡ (u % n + (n - B % n)) + B % n [MOD n] :=
              Nat.ModEq.add_left _ (Nat.mod_modEq B n).symm
          _ = u % n + n := by omega
      rw [show ((u % n + (n - B % n)) % n + B) % n = (u % n + n) % n from key,
        Nat.add_mod_right, Nat.mod_eq_of_lt hplt]
  ---- the comb endpoint forces r ∣ B
  have hrdvd : r ∣ B := by
    by_contra hnd
    obtain ⟨p, q, hp, hq, e11, e12, e21, e22⟩ := hcomb r x0 hr hnd
    have h2 : 2 ≤ (combCutMatrix B C r x0 amp).rank := by
      refine rank2 _ ⟨p, by omega⟩ ⟨q, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ ?_ ?_ ?_ ?_ <;>
        simp only [combCutMatrix]
      · rw [if_pos e11]; exact hampC
      · rw [if_neg e12]
      · rw [if_neg e21]
      · rw [if_pos e22]; exact hampC
    omega
  ---- the QFT output endpoint forces m ∣ B
  have hmdvd : m ∣ B := by
    by_contra hnd
    obtain ⟨p, q, hp, hq, e11, e12, e21, e22⟩ := hcomb m 0 hm hnd
    have hbridge : ∀ x : ℕ, (m ∣ x) ↔ (x % m = 0 % m) := by
      intro x
      rw [Nat.zero_mod]
      constructor
      · rintro ⟨c, rfl⟩
        exact Nat.mul_mod_right m c
      · exact Nat.dvd_of_mod_eq_zero
    have hzeta : zeta Q ≠ 0 := by
      simp only [zeta]
      exact Complex.exp_ne_zero _
    have hz : ∀ x : ℕ, (amp : ℂ) * zeta Q ^ x ≠ 0 :=
      fun x => mul_ne_zero hampC (pow_ne_zero _ hzeta)
    have h2 : 2 ≤ (outputCutMatrix B C m j Q amp).rank := by
      refine rank2 _ ⟨p, by omega⟩ ⟨q, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ ?_ ?_ ?_ ?_ <;>
        simp only [outputCutMatrix]
      · rw [if_pos ((hbridge _).mpr e11)]; exact hz _
      · rw [if_neg (fun hcon => e12 ((hbridge _).mp hcon))]
      · rw [if_neg (fun hcon => e21 ((hbridge _).mp hcon))]
      · rw [if_pos ((hbridge _).mpr e22)]; exact hz _
    omega
  exact Nat.lcm_dvd hrdvd hmdvd
