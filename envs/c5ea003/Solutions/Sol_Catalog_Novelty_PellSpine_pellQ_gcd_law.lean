-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellQ_gcd_law
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:10:12.174323+00:00
-- url     : https://prove2.me/submissions/32342eff-1f9a-456f-9849-d644fca9e421

-- Sol generated from Novelty/PellSpineCompanionDivisibility.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_coprime_pellQ
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_dvd_odd_multiple
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_even_multiple_modEq
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_gcd_dvd
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_succ
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




/-! ## The companion divisibility law -/


/-- The graded gcd statement that survives `not_pellQ_strong_divisibility`: whenever both
quotients are odd, `Q (gcd m n)` divides `gcd (Q m) (Q n)`. -/
theorem pellQ_gcd_of_odd_quotients {m n g : ℕ} (hg : g = Nat.gcd m n)
    (ha : Odd (m / g)) (hb : Odd (n / g)) :
    pellQ g ∣ Nat.gcd (pellQ m) (pellQ n) := by
  obtain ⟨a, ha'⟩ := ha
  obtain ⟨b, hb'⟩ := hb
  have hm : m = (2 * a + 1) * g := by
    have : g ∣ m := hg ▸ Nat.gcd_dvd_left m n
    rw [← Nat.div_mul_cancel this, ha']
  have hn : n = (2 * b + 1) * g := by
    have : g ∣ n := hg ▸ Nat.gcd_dvd_right m n
    rw [← Nat.div_mul_cancel this, hb']
  exact Nat.dvd_gcd (hm ▸ pellQ_dvd_odd_multiple g a) (hn ▸ pellQ_dvd_odd_multiple g b)



/-- If one of the two index quotients is even, the companion values are coprime. -/
theorem pellQ_gcd_eq_one_of_even_quotient {m n : ℕ} (heven : Even (m / Nat.gcd m n)) :
    Nat.gcd (pellQ m) (pellQ n) = 1 := by
  set g := Nat.gcd m n with hg
  obtain ⟨a, ha⟩ := heven
  have hm : m = 2 * a * g := by
    have hdvd : g ∣ m := hg ▸ Nat.gcd_dvd_left m n
    have : m / g = 2 * a := by omega
    rw [← Nat.div_mul_cancel hdvd, this]
  have h1 : Nat.gcd (pellQ m) (pellQ n) ∣ pellQ g := pellQ_gcd_dvd m n
  have h2 : Nat.gcd (pellQ m) (pellQ n) ∣ pellQ (2 * a * g) := hm ▸ Nat.gcd_dvd_left _ _
  have := Nat.dvd_gcd h1 h2
  rwa [pellQ_coprime_even_multiple g a, Nat.dvd_one] at this


/-! ## Refutations -/





/-! ## Summation identities linking the two strands -/





open Catalog.Novelty.PellSpine in
theorem solution(m n : ℕ) :
    Nat.gcd (pellQ m) (pellQ n)
      = if Odd (m / Nat.gcd m n) ∧ Odd (n / Nat.gcd m n) then pellQ (Nat.gcd m n) else 1 := by
  by_cases hodd : Odd (m / Nat.gcd m n) ∧ Odd (n / Nat.gcd m n)
  · rw [if_pos hodd]
    exact Nat.dvd_antisymm (pellQ_gcd_dvd m n)
      (pellQ_gcd_of_odd_quotients rfl hodd.1 hodd.2)
  · rw [if_neg hodd]
    rcases not_and_or.mp hodd with h | h
    · exact pellQ_gcd_eq_one_of_even_quotient (Nat.not_odd_iff_even.mp h)
    · rw [Nat.gcd_comm]
      have hcomm : Nat.gcd n m = Nat.gcd m n := Nat.gcd_comm n m
      exact pellQ_gcd_eq_one_of_even_quotient (m := n) (n := m)
        (by rw [hcomm]; exact Nat.not_odd_iff_even.mp h)
