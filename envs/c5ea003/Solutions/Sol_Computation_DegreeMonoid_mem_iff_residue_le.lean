-- Prove2me | solution 1 for Computation.DegreeMonoid.mem_iff_residue_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:58:57.171982+00:00
-- url     : https://prove2.me/submissions/6220eb47-f153-48bd-831f-43bd9e6e659a

import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
open Computation DegreeMonoid in
theorem solution {p q : ℕ} (cop : Nat.Coprime p q) {n b : ℕ} (hb : b < p)
    (hdvd : (p : ℤ) ∣ (n : ℤ) - (b : ℤ) * (q : ℤ)) :
    n ∈ AddSubmonoid.closure ({p, q} : Set ℕ) ↔ b * q ≤ n := by
  rw [AddSubmonoid.mem_closure_pair]
  constructor
  · rintro ⟨x, y, hxy⟩
    simp only [smul_eq_mul] at hxy
    -- `p ∣ (y - b) q`, hence `p ∣ y - b`, hence `y ≥ b` (as `0 ≤ b < p`)
    have h1 : (p : ℤ) ∣ ((y : ℤ) - b) * q := by
      have e : ((y : ℤ) - b) * q = ((n : ℤ) - b * q) - p * x := by
        rw [← hxy]
        push_cast
        ring
      rw [e]
      exact dvd_sub hdvd (dvd_mul_right _ _)
    have hcop : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr cop
    obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_right h1
    have hyb : b ≤ y := by
      by_contra hlt
      replace hlt := lt_of_not_ge hlt
      have hp : (0 : ℤ) < p := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le b) hb)
      have hbZ : (b : ℤ) < p := by exact_mod_cast hb
      have hyZ : (y : ℤ) < b := by exact_mod_cast hlt
      have hy0 : (0 : ℤ) ≤ y := Nat.cast_nonneg y
      rcases lt_or_ge t 0 with ht0 | ht0
      · have : (p : ℤ) * t ≤ -p := by nlinarith
        linarith
      · have : (0 : ℤ) ≤ p * t := mul_nonneg hp.le ht0
        linarith
    have : b * q ≤ y * q := Nat.mul_le_mul_right q hyb
    omega
  · intro h
    -- `n - b q = p t` with `t ≥ 0`
    obtain ⟨t, ht⟩ := hdvd
    have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le b) hb
    have ht0 : 0 ≤ t := by
      have : (0 : ℤ) ≤ (n : ℤ) - b * q := by
        have : ((b * q : ℕ) : ℤ) ≤ n := by exact_mod_cast h
        push_cast at this
        linarith
      have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
      nlinarith
    refine ⟨t.toNat, b, ?_⟩
    simp only [smul_eq_mul]
    have e : ((t.toNat * p + b * q : ℕ) : ℤ) = n := by
      push_cast
      rw [Int.toNat_of_nonneg ht0]
      linarith
    exact_mod_cast e
