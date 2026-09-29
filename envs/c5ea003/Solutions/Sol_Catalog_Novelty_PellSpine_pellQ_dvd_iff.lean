-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellQ_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:07:57.395908+00:00
-- url     : https://prove2.me/submissions/0b9f50ec-e00f-42d9-aadd-68b8be5ffc39

-- Sol generated from Novelty/PellSpineCompanionDivisibility.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_coprime_pellQ
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_pos
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_dvd_index_dvd
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_dvd_odd_multiple
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_even_multiple_modEq
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_succ
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_succ_eq_add
import Theorems.Thm_Catalog_Novelty_PellSpine_two_le_pellP
/-
# The companion divisibility law on the Pell spine

`Novelty.PellSpineDivisibility` shows that the Pell numbers `P` form a strong divisibility
sequence while the half-companion sequence `Q` does **not** (`gcd (Q 3) (Q 6) = 1`).  That
refutation leaves the real question open: *exactly when* does `Q m` divide `Q n`?

This file answers it completely.  For every `m ≥ 2`,

`Q m ∣ Q n  ↔  n = m * k for some odd k`,

a parity-graded divisibility law with no analogue among the `P`'s.  The proof runs in two
independent halves:

* **index step** — `Q m ∣ P (2m)` and `Q n ∣ P (2n)` push the hypothesis into the strong
  divisibility law for `P`, forcing `Q m ∣ P (2 gcd(m,n))`; if `gcd(m,n) < m` the divisor
  exceeds the dividend, so `m ∣ n`;
* **parity step** — modulo `Q m` the companion sequence satisfies the two-step recursion
  `Q (a + 2m) ≡ 2 P m ^ 2 * Q a`, so `Q (2jm) ≡ (2 P m ^ 2) ^ j`, a unit mod `Q m`
  because `Q m` is odd and coprime to `P m`.  Even multiples are therefore ruled out.

## Proved

* `pellQ_odd`, `pellQ_coprime_two_pellP_sq` — the arithmetic units used by the parity step;
* `pellQ_add_two_mul_modEq` — `Q (a + 2m) ≡ 2 P m ^ 2 * Q a [MOD Q m]`;
* `pellQ_even_multiple_modEq` — `Q (2jm) ≡ (2 P m ^ 2) ^ j [MOD Q m]`;
* `pellQ_coprime_even_multiple` — `gcd (Q m) (Q (2jm)) = 1`;
* `pellQ_dvd_index_dvd` — `Q m ∣ Q n → m ∣ n` for `m ≥ 2`;
* `pellQ_dvd_iff` — **the companion divisibility law**;
* `pellQ_gcd_dvd`, `pellQ_gcd_eq_one_of_even_quotient`, `pellQ_gcd_law` — **the companion
  gcd law**: `gcd (Q m) (Q n) = Q (gcd m n)` when both index quotients are odd, and `1`
  otherwise, with no side condition on `m` and `n`;
* `pellQ_gcd_of_odd_quotients` — the graded gcd statement that survives the refutation;
* summation identities `pellQ_sum`, `pellP_sum`, `pellP_sq_sum` tying the two strands
  of the spine together.

## Refuted

* `not_pellQ_dvd_all_multiples` — `Q n ∣ Q (kn)` fails for even `k`: `Q 2 = 3 ∤ 17 = Q 4`;
* `not_pellQ_dvd_iff_index_dvd` — divisibility of indices is **not** sufficient, by the
  same pair, so the parity grading in `pellQ_dvd_iff` cannot be dropped.
-/

open Catalog.Novelty.PellSpine

open Finset

/-! ## Arithmetic units modulo `Q m` -/

/-- Every half-companion Pell number is odd. -/
theorem pellQ_odd (n : ℕ) : Odd (pellQ n) := by
  induction n with
  | zero => exact ⟨0, by norm_num [pellQ]⟩
  | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t + pellP k, by rw [pellQ_succ, ht]; ring⟩

/-- `Q m` is coprime to `2 * P m ^ 2`: it is odd, and coprime to `P m`. -/
theorem pellQ_coprime_two_pellP_sq (m : ℕ) :
    Nat.Coprime (pellQ m) (2 * pellP m ^ 2) := by
  have h2 : Nat.Coprime (pellQ m) 2 := by
    have hnd : ¬ (2 ∣ pellQ m) := by
      simpa [Nat.two_dvd_ne_zero, Nat.odd_iff] using (Nat.odd_iff.mp (pellQ_odd m))
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd).symm
  have hp : Nat.Coprime (pellQ m) (pellP m) :=
    (Nat.coprime_comm.mp (pellP_coprime_pellQ m))
  exact Nat.Coprime.mul_right h2 (hp.pow_right 2)

/-! ## The parity step -/



/-- `Q m` is coprime to every companion value at an even multiple of `m`. -/
theorem pellQ_coprime_even_multiple (m j : ℕ) :
    Nat.Coprime (pellQ m) (pellQ (2 * j * m)) := by
  have hmod := pellQ_even_multiple_modEq m j
  have hcop : Nat.Coprime (pellQ m) ((2 * pellP m ^ 2) ^ j) :=
    (pellQ_coprime_two_pellP_sq m).pow_right j
  have hgcd : Nat.gcd (pellQ m) (pellQ (2 * j * m))
      = Nat.gcd (pellQ m) ((2 * pellP m ^ 2) ^ j) := by
    rw [Nat.gcd_comm (pellQ m) (pellQ (2 * j * m)),
      Nat.gcd_comm (pellQ m) ((2 * pellP m ^ 2) ^ j)]
    exact Nat.ModEq.gcd_eq hmod
  exact hgcd.trans hcop

/-! ## The index step -/

/-- For `m ≥ 2` the companion value strictly dominates the Pell value. -/
theorem pellP_lt_pellQ {m : ℕ} (hm : 2 ≤ m) : pellP m < pellQ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have h := pellQ_succ_eq_add k
  have : 0 < pellP k := pellP_pos hk
  omega

/-- `3 ≤ Q m` whenever `2 ≤ m`. -/
theorem three_le_pellQ {m : ℕ} (hm : 2 ≤ m) : 3 ≤ pellQ m := by
  have h1 : pellP m < pellQ m := pellP_lt_pellQ hm
  have h2 : 2 ≤ pellP m := two_le_pellP hm
  omega


/-! ## The companion divisibility law -/







/-! ## Refutations -/





/-! ## Summation identities linking the two strands -/





open Catalog.Novelty.PellSpine in
theorem solution{m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    pellQ m ∣ pellQ n ↔ ∃ k, Odd k ∧ n = m * k := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := pellQ_dvd_index_dvd hm h
    refine ⟨k, ?_, rfl⟩
    rcases Nat.even_or_odd k with he | ho
    · exfalso
      obtain ⟨j, hj⟩ := he
      have hidx : m * k = 2 * j * m := by subst hj; ring
      have hcop : Nat.Coprime (pellQ m) (pellQ (m * k)) := by
        rw [hidx]; exact pellQ_coprime_even_multiple m j
      have hone : pellQ m ∣ 1 := by
        have : pellQ m ∣ Nat.gcd (pellQ m) (pellQ (m * k)) := Nat.dvd_gcd dvd_rfl h
        rwa [hcop] at this
      have h1 : pellQ m = 1 := Nat.eq_one_of_dvd_one hone
      have := three_le_pellQ hm
      omega
    · exact ho
  · rintro ⟨k, ⟨j, rfl⟩, rfl⟩
    have : m * (2 * j + 1) = (2 * j + 1) * m := Nat.mul_comm _ _
    rw [this]
    exact pellQ_dvd_odd_multiple m j
