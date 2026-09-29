-- Prove2me | solution 1 for Bridges.AlexanderTorus.torusAlexander_defining_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:02:17.913987+00:00
-- url     : https://prove2.me/submissions/88d4454d-d9d9-4f02-80b0-dd7aca217eb7

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXII
open Polynomial Finset Bridges.AlexanderTorus in
theorem solution {r N : ℕ} (hco : Nat.Coprime r N)
    (hr : 0 < r) (hN : 0 < N) :
    ((X : ℤ[X]) ^ (r * N) - 1) * ((X : ℤ[X]) - 1)
      = ((X : ℤ[X]) ^ r - 1) * ((X : ℤ[X]) ^ N - 1) * torusAlexander r N := by
  -- divisors of `r` and of `N` sit inside those of `rN` and meet only in `1`
  have hsub : r.divisors ∪ N.divisors ⊆ (r * N).divisors := by
    intro d hd
    rcases mem_union.1 hd with h | h
    · exact Nat.mem_divisors.2 ⟨(Nat.dvd_of_mem_divisors h).trans (dvd_mul_right r N),
        (Nat.mul_pos hr hN).ne'⟩
    · exact Nat.mem_divisors.2 ⟨(Nat.dvd_of_mem_divisors h).trans (dvd_mul_left N r),
        (Nat.mul_pos hr hN).ne'⟩
  have hinter : r.divisors ∩ N.divisors = {1} := by
    ext d
    simp only [mem_inter, Nat.mem_divisors, mem_singleton]
    constructor
    · rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
      have h := Nat.dvd_gcd h1 h2
      rw [hco.gcd_eq_one] at h
      exact Nat.dvd_one.1 h
    · rintro rfl
      exact ⟨⟨one_dvd _, hr.ne'⟩, ⟨one_dvd _, hN.ne'⟩⟩
  -- `X^n - 1 = ∏_{d ∣ n} Φ_d`
  have hD := prod_cyclotomic_eq_X_pow_sub_one (R := ℤ) (Nat.mul_pos hr hN)
  have hDr := prod_cyclotomic_eq_X_pow_sub_one (R := ℤ) hr
  have hDN := prod_cyclotomic_eq_X_pow_sub_one (R := ℤ) hN
  have hsd : (∏ x ∈ (r * N).divisors \ (r.divisors ∪ N.divisors), cyclotomic x ℤ)
      * ∏ x ∈ r.divisors ∪ N.divisors, cyclotomic x ℤ = ∏ x ∈ (r * N).divisors, cyclotomic x ℤ :=
    prod_sdiff hsub
  have hui : (∏ x ∈ r.divisors ∪ N.divisors, cyclotomic x ℤ)
      * ∏ x ∈ r.divisors ∩ N.divisors, cyclotomic x ℤ
      = (∏ x ∈ r.divisors, cyclotomic x ℤ) * ∏ x ∈ N.divisors, cyclotomic x ℤ :=
    prod_union_inter
  rw [hinter, prod_singleton, cyclotomic_one] at hui
  unfold torusAlexander torusIdx
  rw [← hD, ← hsd, ← hDr, ← hDN, ← hui]
  ring
