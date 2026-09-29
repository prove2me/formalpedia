-- Prove2me | solution 1 for BinomialGCDFRange.F_eq_one_of_not_succ_primePow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:48:01.01539+00:00
-- url     : https://prove2.me/submissions/8df4fc7d-4f62-4a6e-9208-59b204a1c082

-- Sol generated from Novelty/BinomialGCDFRange.lean
import Mathlib
import Definitions.Def_Novelty_BinomialGCDFRange

/-!
# The Pascal-row interior GCD and prime powers

For `k ≥ 1` put `n = k + 1` and let
`F(k) = gcd_{1 ≤ i ≤ k} C(n, i)`
be the gcd of the *interior* entries of row `n` of Pascal's triangle.

This is the classical "Ram" gcd: `F(k) = p` when `n = p^a` is a prime power,
and `F(k) = 1` otherwise.  This file records the corrected qualitative
statement

* `F_eq_one_iff` — for `k ≥ 1`, `F k = 1 ↔ ¬ IsPrimePow (k + 1)`.

The forward direction is the contrapositive of `F_ne_one_of_succ_primePow`
(itself built on `primepower_succ_dvd_F`, which divides every interior binomial
of a prime-power row by the underlying prime via `Nat.Prime.dvd_choose_pow`).
The backward direction is the genuine arithmetic content: if `n` is *not* a
prime power then for every prime `p ∣ n`, taking `i = p^{v_p(n)}` gives an
interior binomial `C(n, i)` not divisible by `p` (Kummer: no carries), so no
prime divides `F k`, whence `F k = 1`.
-/

open BinomialGCDFRange

open Nat Finset


/-- `F k` divides each interior binomial coefficient. -/
theorem F_dvd_term {k i : ℕ} (hi : i ∈ Finset.Icc 1 k) :
    F k ∣ Nat.choose (k + 1) i :=
  Finset.gcd_dvd hi

/-
**Forward (prime-power) divisibility.**  If `k + 1 = p ^ a` is a prime
power then the prime `p` divides every interior binomial of the row, hence
`p ∣ F k`.
-/

/-
**Forward conclusion.**  If `k + 1` is a prime power then `F k ≠ 1`.
-/

/-
**Key arithmetic lemma (Kummer / no carries).**  For a prime `p` and any
`m` not divisible by `p`, the prime `p` does not divide `C(p^a · m, p^a)`.
(Adding `p^a` and `p^a·(m-1)` in base `p` produces no carry because the digit
of `m` at position `a` — namely `m mod p` — is nonzero.)
-/
theorem not_dvd_choose_ordProj {p m a : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    ¬ p ∣ (p ^ a * m).choose (p ^ a) := by
  induction' a with a ih generalizing m <;> simp_all +decide [ pow_succ' ];
  haveI := Fact.mk hp;
  have h_cong : Nat.choose (p * p ^ a * m) (p * p ^ a) ≡ Nat.choose (p ^ a * m) (p ^ a) [MOD p] := by
    have h_lucas : ∀ (n k : ℕ), Nat.choose n k ≡ Nat.choose (n % p) (k % p) * Nat.choose (n / p) (k / p) [MOD p] := by
      exact fun n k => Choose.choose_modEq_choose_mod_mul_choose_div_nat;
    convert h_lucas ( p * p ^ a * m ) ( p * p ^ a ) using 1 ; norm_num [ Nat.mul_assoc, Nat.mul_mod, Nat.mul_div_assoc, hp.pos ];
  simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ]

/-
**Backward direction.**  If `k ≥ 1` and `k + 1` is not a prime power then
`F k = 1`.
-/



open BinomialGCDFRange in
theorem solution{k : ℕ} (hk : 1 ≤ k)
    (h : ¬ IsPrimePow (k + 1)) : F k = 1 := by
  -- By contradiction, assume $F k \neq 1$.
  by_contra h_contra;
  -- By `Nat.exists_prime_and_dvd` there is a prime `p` with `p ∣ F k`.
  obtain ⟨p, hp_prime, hp_div⟩ : ∃ p, Nat.Prime p ∧ p ∣ F k := by
    exact Nat.exists_prime_and_dvd h_contra
  -- Since `p ∣ F k` and `F k ∣ k + 1`, we have `p ∣ k + 1`, i.e. `p ∣ n`.
  have hp_div_n : p ∣ k + 1 := by
    exact dvd_trans hp_div ( F_dvd_term ( Finset.left_mem_Icc.mpr hk ) ) |> fun x => by simpa using x;
  -- Let `a := (k+1).factorization p` and `q := (k+1) / p ^ a`. Then:
  set a := (k + 1).factorization p
  set q := (k + 1) / p ^ a
  have ha_pos : 0 < a := by
    exact pos_iff_ne_zero.mpr ( Finsupp.mem_support_iff.mp ( by aesop ) )
  have hq_pos : 1 ≤ q := by
    exact Nat.div_pos ( Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.ordProj_dvd _ _ ) ) ( pow_pos hp_prime.pos _ )
  have hq_not_div : ¬ p ∣ q := by
    exact Nat.not_dvd_ordCompl hp_prime ( by linarith )
  have hpow_lt_n : p ^ a < k + 1 := by
    refine' lt_of_le_of_ne ( Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.ordProj_dvd _ _ ) ) fun con => h _;
    exact con ▸ hp_prime.isPrimePow.pow ha_pos.ne'
  have hpow_le_k : p ^ a ≤ k := by
    grind
  have hpow_mem : p ^ a ∈ Finset.Icc 1 k := by
    grind
  have hp_div_choose : p ∣ Nat.choose (k + 1) (p ^ a) := by
    exact dvd_trans hp_div ( F_dvd_term hpow_mem )
  have h_contradiction : ¬ p ∣ Nat.choose (p ^ a * q) (p ^ a) := by
    convert not_dvd_choose_ordProj hp_prime hq_not_div using 1;
  exact h_contradiction <| by rwa [ Nat.mul_div_cancel' <| Nat.ordProj_dvd _ _ ] at *;
