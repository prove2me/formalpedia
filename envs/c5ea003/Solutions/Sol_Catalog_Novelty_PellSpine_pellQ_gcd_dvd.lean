-- Prove2me | solution 1 for Catalog.Novelty.PellSpine.pellQ_gcd_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:07:58.226438+00:00
-- url     : https://prove2.me/submissions/06d8e0bc-0fef-4d4f-bb5e-e398aa30c1a8

-- Sol generated from Novelty/PellSpineCompanionDivisibility.lean
import Mathlib
import Definitions.Def_Novelty_PellSpineCore
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_coprime_pellQ
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_dvd_iff
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_gcd
import Theorems.Thm_Catalog_Novelty_PellSpine_pellP_two_mul
import Theorems.Thm_Catalog_Novelty_PellSpine_pellQ_dvd_pellP_two_mul
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


/-! ## The parity step -/




/-! ## The index step -/




/-! ## The companion divisibility law -/



/-- Every divisor of a companion value is odd, hence coprime to `2`. -/
theorem coprime_two_of_dvd_pellQ {d m : ℕ} (h : d ∣ pellQ m) : Nat.Coprime d 2 := by
  have hnd : ¬ (2 ∣ d) := by
    intro h2
    have : (2 : ℕ) ∣ pellQ m := h2.trans h
    have := Nat.odd_iff.mp (pellQ_odd m)
    omega
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd).symm




/-! ## Refutations -/





/-! ## Summation identities linking the two strands -/





open Catalog.Novelty.PellSpine in
theorem solution(m n : ℕ) :
    Nat.gcd (pellQ m) (pellQ n) ∣ pellQ (Nat.gcd m n) := by
  set g := Nat.gcd m n with hg
  set d := Nat.gcd (pellQ m) (pellQ n) with hd
  have hdm : d ∣ pellQ m := Nat.gcd_dvd_left _ _
  have hdn : d ∣ pellQ n := Nat.gcd_dvd_right _ _
  have h2g : d ∣ pellP (2 * g) := by
    have h1 : d ∣ pellP (2 * m) := hdm.trans (pellQ_dvd_pellP_two_mul m)
    have h2 : d ∣ pellP (2 * n) := hdn.trans (pellQ_dvd_pellP_two_mul n)
    have : d ∣ Nat.gcd (pellP (2 * m)) (pellP (2 * n)) := Nat.dvd_gcd h1 h2
    rwa [pellP_gcd, show Nat.gcd (2 * m) (2 * n) = 2 * g by rw [hg, Nat.gcd_mul_left]] at this
  have hprod : d ∣ pellP g * pellQ g := by
    have hform : pellP (2 * g) = 2 * (pellP g * pellQ g) := pellP_two_mul g
    exact (coprime_two_of_dvd_pellQ hdm).dvd_of_dvd_mul_left (by rwa [hform] at h2g)
  have hcopP : Nat.Coprime d (pellP g) := by
    have hPg : pellP g ∣ pellP m := (pellP_dvd_iff g m).mp (hg ▸ Nat.gcd_dvd_left m n)
    have hcm : Nat.Coprime (pellP m) (pellQ m) := pellP_coprime_pellQ m
    exact (Nat.Coprime.coprime_dvd_right hdm (Nat.Coprime.coprime_dvd_left hPg hcm)).symm
  exact hcopP.dvd_of_dvd_mul_left hprod
