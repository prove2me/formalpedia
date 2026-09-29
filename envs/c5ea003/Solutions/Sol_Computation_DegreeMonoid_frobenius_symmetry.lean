-- Prove2me | solution 1 for Computation.DegreeMonoid.frobenius_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T03:29:23.14179+00:00
-- url     : https://prove2.me/submissions/ca266b07-a4a8-4966-baeb-45012ae374c6

import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure

open Computation DegreeMonoid in
theorem solution {p q : ℕ} (cop : Nat.Coprime p q) (hp : 1 < p) (hq : 1 < q) {n : ℕ}
    (hn : n ≤ p * q - p - q) :
    (n ∉ AddSubmonoid.closure ({p, q} : Set ℕ) ↔
      (p * q - p - q - n) ∈ AddSubmonoid.closure ({p, q} : Set ℕ)) := by
  have hmem : ∀ x : ℕ, x ∈ AddSubmonoid.closure ({p, q} : Set ℕ) ↔
      ∃ a b : ℕ, a * p + b * q = x := by
    intro x
    rw [AddSubmonoid.mem_closure_pair]
    simp only [smul_eq_mul]
  have hpq : p + q ≤ p * q := by nlinarith
  -- the Frobenius number `pq - p - q` is not representable
  have hF : ∀ a b : ℕ, a * p + b * q ≠ p * q - p - q := by
    intro a b h
    have h1 : (a + 1) * p + (b + 1) * q = p * q := by
      rw [add_mul, add_mul, one_mul, one_mul]
      omega
    have hq1 : q ∣ a + 1 := by
      have hd : q ∣ (a + 1) * p :=
        (Nat.dvd_add_left (dvd_mul_left q (b + 1))).1 (h1 ▸ dvd_mul_left q p)
      exact Nat.Coprime.dvd_of_dvd_mul_right cop.symm hd
    have hp1 : p ∣ b + 1 := by
      have hd : p ∣ (b + 1) * q :=
        (Nat.dvd_add_right (dvd_mul_left p (a + 1))).1 (h1 ▸ dvd_mul_right p q)
      exact Nat.Coprime.dvd_of_dvd_mul_right cop hd
    have ha : q ≤ a + 1 := Nat.le_of_dvd (by omega) hq1
    have hb : p ≤ b + 1 := Nat.le_of_dvd (by omega) hp1
    nlinarith [Nat.mul_le_mul_right p ha, Nat.mul_le_mul_right q hb,
      Nat.mul_pos (by omega : 0 < p) (by omega : 0 < q)]
  constructor
  · intro hns
    -- write `n ≡ a p (mod q)` with `0 ≤ a < q`
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime cop hq
    set a := (u * n) % q with ha_def
    have ha_lt : a < q := Nat.mod_lt _ (by omega)
    have h2 : p * u ≡ 1 [MOD q] := by
      unfold Nat.ModEq
      rw [hu, Nat.mod_eq_of_lt hq]
    have h3 : a * p ≡ n [MOD q] := by
      calc a * p ≡ u * n * p [MOD q] := (Nat.mod_modEq _ _).mul_right p
        _ = (p * u) * n := by ring
        _ ≡ 1 * n [MOD q] := h2.mul_right n
        _ = n := one_mul n
    -- `n` is not representable, so `a p > n`
    have hlt : n < a * p := by
      by_contra hge
      have hge' : a * p ≤ n := not_lt.1 hge
      have hdvd : q ∣ n - a * p := (Nat.modEq_iff_dvd' hge').1 h3
      apply hns
      refine (hmem n).2 ⟨a, (n - a * p) / q, ?_⟩
      rw [Nat.div_mul_cancel hdvd]
      omega
    have hdvd : q ∣ a * p - n := (Nat.modEq_iff_dvd' hlt.le).1 h3.symm
    set c := (a * p - n) / q with hc_def
    have hc : c * q = a * p - n := Nat.div_mul_cancel hdvd
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, zero_mul] at hc
        omega
      · exact h0
    refine (hmem _).2 ⟨q - 1 - a, c - 1, ?_⟩
    have hq1 : 1 ≤ q := by omega
    have haq : a ≤ q - 1 := by omega
    have hp1 : p ≤ p * q := by nlinarith
    have hp2 : q ≤ p * q - p := by omega
    zify [hq1, haq, hc1, hp1, hp2, hn, hlt.le] at hc ⊢
    linear_combination hc
  · intro hN hn'
    obtain ⟨a, b, hab⟩ := (hmem n).1 hn'
    obtain ⟨c, d, hcd⟩ := (hmem _).1 hN
    apply hF (a + c) (b + d)
    rw [add_mul, add_mul]
    omega
