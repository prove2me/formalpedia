-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.chapter03_erdos_ge3
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:17:04.716801+00:00
-- url     : https://prove2.me/submissions/e25312b8-da65-4d38-9924-f85c523391e7

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
import Theorems.Thm_ProofsInTheBook_Chapter03_erdos_step1_n_gt_k_sq
import Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_below_sq_of_9_le
import Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_of_pow_gap
import Theorems.Thm_ProofsInTheBook_Chapter03_exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
import Theorems.Thm_ProofsInTheBook_Chapter03_pow_gap_small_k_tail
import Theorems.Thm_ProofsInTheBook_Chapter03_pow_l_dvd_one_factor_of_descFactorial
import Theorems.Thm_ProofsInTheBook_Chapter03_primeCounting_gap_of_120_le
import Theorems.Thm_ProofsInTheBook_Chapter03_primeCounting_gap_of_19_le
import Theorems.Thm_ProofsInTheBook_Chapter03_prod_lPowerFreeParts_dvd_factorial
import Theorems.Thm_ProofsInTheBook_Chapter03_self_eq_lPowerFreePart_mul_lPowerRoot_pow


/-!
# Chapter 3: Binomial coefficients are (almost) never powers

From "Proofs from THE BOOK" (Aigner & Ziegler).

## Book content summary

The book states Sylvester's theorem (1892):

> If n ≥ 2k, then at least one of the numbers n, n - 1, ..., n - k + 1
> has a prime divisor p greater than k.

Equivalently, the binomial coefficient C(n,k) = n(n-1)...(n-k+1)/k!
always has a prime factor p > k when n ≥ 2k.

The central case n = 2k is precisely Bertrand's postulate (Chapter 2).

For the general case, the book notes (p. 13):

> In 1934, Erdős gave a short and elementary Book Proof of Sylvester's
> result, running along the lines of his proof of Bertrand's postulate.

The book does **not** reproduce this proof in full. It references:

> P. Erdős: A theorem of Sylvester and Schur,
> J. London Math. Soc. 9 (1934), 282-288.

The rest of Chapter 3 uses Sylvester's theorem as a lemma to prove the
"binomial coefficients are almost never powers" result.

## Formalization status

The central case (C(2k,k)) is fully proved below using Bertrand's postulate.

The general case (`sylvester_general`) currently takes `hsmooth` (that
n.descFactorial k is not (k+1)-smooth) as a premise. Eliminating this
premise requires a full formalization of Erdős's 1934 Sylvester-Schur
proof, which uses a refined analysis of how prime powers are distributed
among the k consecutive integers — more delicate than the Bertrand
chapter's global inequality bounding.

This is tracked in TODO.md as "Ch03: Sylvester smoothness core" —
difficulty: Medium-Hard, blocker: needs Erdős 1934 proof formalized.
-/

namespace ProofsInTheBook.Chapter03

open Nat





















































































theorem primeCounting_gap_9_120_cert :
    ∀ k : Fin 120, 9 ≤ k.val → 2 * Nat.primeCounting k.val < k.val := by
  intro k hk9
  by_cases hk19 : 19 ≤ k.val
  · exact primeCounting_gap_of_19_le hk19
  · have hklt19 : k.val < 19 := by omega
    interval_cases k.val <;> decide

theorem primeCounting_gap_of_9_le_lt_120 {k : ℕ} (hk9 : 9 ≤ k) (hk120 : k < 120) :
    2 * Nat.primeCounting k < k :=
  primeCounting_gap_9_120_cert ⟨k, hk120⟩ hk9

theorem primeCounting_gap_of_9_le {k : ℕ} (hk9 : 9 ≤ k) :
    2 * Nat.primeCounting k < k := by
  by_cases hk120 : k < 120
  · exact primeCounting_gap_of_9_le_lt_120 hk9 hk120
  · exact primeCounting_gap_of_120_le (by omega)































































































































theorem exists_large_prime_factor_choose_sq_le_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hkn : k ≤ n) (hsq : k * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    (by omega) hkn hsq (primeCounting_gap_of_9_le hk9)





theorem exists_large_prime_factor_choose_small_cert :
    ∀ k : Fin 9, ∀ n : Fin 94,
      0 < k.val → 2 * k.val ≤ n.val →
        ∃ p : Fin 94, k.val < p.val ∧ p.val.Prime ∧ p.val ∣ n.val.choose k.val := by
  set_option maxRecDepth 10000 in
  decide



theorem exists_large_prime_factor_choose_of_lt_9
    {n k : ℕ} (hkpos : 0 < k) (hk9 : k < 9) (hn2k : 2 * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_cases hn94 : n < 94
  · rcases exists_large_prime_factor_choose_small_cert ⟨k, hk9⟩ ⟨n, hn94⟩
      hkpos hn2k with ⟨p, hkp, hp, hpdvd⟩
    exact ⟨p.val, hkp, hp, hpdvd⟩
  · exact exists_large_prime_factor_choose_of_pow_gap (n := n) (k := k)
      hkpos (by omega) (by interval_cases k <;> decide)
      (pow_gap_small_k_tail hkpos hk9 (by omega))






































































































































theorem exists_large_prime_factor_choose_of_two_mul_le
    {n k : ℕ} (hkpos : 0 < k) (hn2k : 2 * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_cases hk9_lt : k < 9
  · exact exists_large_prime_factor_choose_of_lt_9 hkpos hk9_lt hn2k
  · have hk9 : 9 ≤ k := by omega
    by_cases hsq : k * k ≤ n
    · exact exists_large_prime_factor_choose_sq_le_of_9_le hk9 (by omega) hsq
    · have hbelow : n < k * k := by omega
      exact exists_large_prime_factor_choose_below_sq_of_9_le hk9 hn2k hbelow

/-!
### Central case of Sylvester's theorem

For the central binomial coefficient C(2k,k), we can give a clean proof
using Bertrand's postulate (Chapter 2):
- By Bertrand, ∃ prime p with k < p ≤ 2k.
- p divides (2k)! since p ≤ 2k.
- p does not divide k! since p > k.
- Since C(2k,k) · (k!)² = (2k)!, Euclid's lemma gives p | C(2k,k).
-/



/-!
### General Sylvester's theorem

For n ≥ 2k, the book extends the argument to C(n,k) by analyzing the
product n(n-1)···(n-k+1) = k! · C(n,k). For each of the k consecutive
integers n-j (0 ≤ j ≤ k-1), decompose n-j = q_j · r_j where q_j is
k-smooth and r_j has only prime factors > k. The q_j are bounded by
the prime factorization structure, forcing some r_j > 1.
-/

/--
The general Sylvester theorem: for n ≥ 2k and k ≥ 1, C(n,k) has a prime
divisor exceeding k. The proof reduces to showing the descending factorial
n(n-1)···(n-k+1) is not (k+1)-smooth; the existing infrastructure
(`exists_large_prime_dvd_choose_of_descFactorial_not_smooth`) then gives
the prime factor of C(n,k).
-/
theorem sylvester_general (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k :=
  exists_large_prime_factor_choose_of_two_mul_le hk hn









/-!
### Binomial coefficients are (almost) never powers

Erdős's theorem (1951): C(n,k) ≠ m^l for k ≥ 4, n ≥ 2k, l ≥ 2.
Reference: P. Erdős, On a diophantine equation,
J. London Math. Soc. 26 (1951), 176-178.

Below: Step 1 (concentration lemma + n > k²) is complete.
Steps 2–4 are pending (l-th-power-free decomposition, distinctness,
classification {aⱼ}={1,…,k}, and contradiction for l=2, l≥3).
-/

section Tier1

/-! ### Prime-divisibility helpers for Finset products -/





/-! ### Step 1: Concentration lemma → n > k² -/





/-- Strong form of Step 1: under the perfect-power assumption, `n > k^l`. -/
lemma erdos_step1_n_gt_k_pow {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n)
    (hl : 2 ≤ l) (h_eq : n.choose k = m ^ l) : k ^ l < n := by
  have hk_pos : 0 < k := by omega
  have hk_le_n : k ≤ n := by omega
  obtain ⟨p, hkp, hp, hp_choose⟩ := sylvester_general n k hn hk_pos
  have hp_m : p ∣ m := hp.dvd_of_dvd_pow (h_eq ▸ hp_choose)
  have hp_l_dvd_choose : p ^ l ∣ n.choose k := by
    rw [h_eq]
    exact pow_dvd_pow_of_dvd hp_m l
  have hp_l_dvd_desc : p ^ l ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose n k]
    apply hp_l_dvd_choose.trans
    rw [mul_comm]
    exact dvd_mul_right _ _
  have hl_pos : 0 < l := by omega
  obtain ⟨i, hi, h_i_pow⟩ :=
    pow_l_dvd_one_factor_of_descFactorial hp hkp hl_pos hk_le_n hp_l_dvd_desc
  have h_n_minus_i_pos : 0 < n - i := Nat.sub_pos_of_lt (by omega)
  have h_ge : p ^ l ≤ n - i := Nat.le_of_dvd h_n_minus_i_pos h_i_pow
  have h_k_l_lt_p_l : k ^ l < p ^ l :=
    Nat.pow_lt_pow_left hkp (by omega : l ≠ 0)
  omega

/-! ### Step 2: l-th-power-free decomposition -/







/-! ### 2-power-free part: factorization mod 2 (Tier 2 building block for Ch03) -/













/-- The l-power-free part is nonzero on nonzero input. -/
theorem lPowerFreePart_ne_zero {l m : ℕ} (hm : m ≠ 0) :
    lPowerFreePart l m ≠ 0 := by
  intro hz
  have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow l m hm
  rw [hz, zero_mul] at hsplit
  exact hm hsplit

/-- The l-power-free part is positive on positive input. -/
theorem lPowerFreePart_pos_of_ne_zero {l m : ℕ} (hm : m ≠ 0) :
    0 < lPowerFreePart l m :=
  Nat.pos_of_ne_zero (lPowerFreePart_ne_zero (l := l) hm)

/-- The l-power root is nonzero on nonzero input when `l > 0`. -/
theorem lPowerRoot_ne_zero {l m : ℕ} (hl : 0 < l) (hm : m ≠ 0) :
    lPowerRoot l m ≠ 0 := by
  intro hz
  have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow l m hm
  rw [hz, zero_pow hl.ne', mul_zero] at hsplit
  exact hm hsplit

/-- The l-power root is positive on positive input when `l > 0`. -/
theorem lPowerRoot_pos_of_ne_zero {l m : ℕ} (hl : 0 < l) (hm : m ≠ 0) :
    0 < lPowerRoot l m :=
  Nat.pos_of_ne_zero (lPowerRoot_ne_zero hl hm)

























private lemma four_mul_sq_sub_add_two_gt_sq {k : ℕ} (hk : 4 ≤ k) :
    k * k < 4 * (k * k - k + 2) := by
  have h_no_trunc : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
  zify [h_no_trunc]
  have hk_z : (4 : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith only [sq_nonneg ((k : ℤ) - 2), hk_z]









private lemma l_mul_pow_pred_le_succ_pow_sub_pow (b l : ℕ) (hl : 1 ≤ l) :
    l * b ^ (l - 1) ≤ (b + 1) ^ l - b ^ l := by
  have hpow_le_nat : b ^ l ≤ (b + 1) ^ l := Nat.pow_le_pow_left (Nat.le_succ b) l
  have hgeom :
      ((b + 1 : ℤ) ^ l - (b : ℤ) ^ l) =
        ∑ i ∈ Finset.range l, (b + 1 : ℤ) ^ i * (b : ℤ) ^ (l - 1 - i) := by
    have h := (Commute.all (b + 1 : ℤ) (b : ℤ)).mul_geom_sum₂ l
    simpa using h.symm
  have hterm_ge : ∀ i ∈ Finset.range l,
      (b : ℤ) ^ (l - 1) ≤ (b + 1 : ℤ) ^ i * (b : ℤ) ^ (l - 1 - i) := by
    intro i hi
    have hi_lt : i < l := Finset.mem_range.mp hi
    calc
      (b : ℤ) ^ (l - 1) = (b : ℤ) ^ i * (b : ℤ) ^ (l - 1 - i) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ (b + 1 : ℤ) ^ i * (b : ℤ) ^ (l - 1 - i) := by
        gcongr
        · exact_mod_cast Nat.le_succ b
  have hsum_ge : (l : ℤ) * (b : ℤ) ^ (l - 1) ≤
        ∑ i ∈ Finset.range l, (b + 1 : ℤ) ^ i * (b : ℤ) ^ (l - 1 - i) := by
    calc
      (l : ℤ) * (b : ℤ) ^ (l - 1)
          = ∑ _i ∈ Finset.range l, (b : ℤ) ^ (l - 1) := by
            simp [Finset.sum_const]
      _ ≤ ∑ i ∈ Finset.range l, (b + 1 : ℤ) ^ i * (b : ℤ) ^ (l - 1 - i) := by
            exact Finset.sum_le_sum hterm_ge
  rw [← hgeom] at hsum_ge
  have hdiff_ge_z :
      ((l * b ^ (l - 1) : ℕ) : ℤ) ≤ (((b + 1) ^ l - b ^ l : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    rw [Int.ofNat_sub hpow_le_nat]
    exact hsum_ge
  exact_mod_cast hdiff_ge_z

private lemma four_mul_l_component_le_sq {a b l : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hl : 2 ≤ l) :
    4 * (a * b ^ l) ≤ (l * a * b ^ (l - 1)) * (l * a * b ^ (l - 1)) := by
  have h4_le_l2 : 4 ≤ l * l := by nlinarith
  have hpow_le : b ^ l ≤ b ^ (2 * l - 2) := by
    exact Nat.pow_le_pow_right hb (by omega)
  have hbase_le : a * b ^ l ≤ a * a * b ^ (2 * l - 2) := by
    calc
      a * b ^ l ≤ a * b ^ (2 * l - 2) := Nat.mul_le_mul_left a hpow_le
      _ ≤ a * (a * b ^ (2 * l - 2)) :=
        Nat.mul_le_mul_left a (Nat.le_mul_of_pos_left _ ha)
      _ = a * a * b ^ (2 * l - 2) := by ring
  calc
    4 * (a * b ^ l) ≤ (l * l) * (a * b ^ l) := Nat.mul_le_mul_right _ h4_le_l2
    _ ≤ (l * l) * (a * a * b ^ (2 * l - 2)) := Nat.mul_le_mul_left _ hbase_le
    _ = (l * a * b ^ (l - 1)) * (l * a * b ^ (l - 1)) := by
      have hexp : (l - 1) + (l - 1) = 2 * l - 2 := by omega
      rw [← hexp, pow_add]
      ring

private lemma lPowerFreePart_l_ne_of_lt
    {n k l m i j : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 2 ≤ l)
    (h_eq : n.choose k = m ^ l) (hi : i ∈ Finset.range k) (hj : j ∈ Finset.range k)
    (hij : i < j) :
    lPowerFreePart l (n - i) ≠ lPowerFreePart l (n - j) := by
  intro hsame
  have hn_gt : k * k < n := erdos_step1_n_gt_k_sq hk hn hl h_eq
  have hi_lt : i < k := Finset.mem_range.mp hi
  have hj_lt : j < k := Finset.mem_range.mp hj
  have hk_le_n : k ≤ n := by omega
  have hni_ne : n - i ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt (hi_lt.trans_le hk_le_n))
  have hnj_ne : n - j ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt (hj_lt.trans_le hk_le_n))
  have hnj_lt_hni : n - j < n - i := by omega
  have hdiff_nat : j - i = (n - i) - (n - j) := by omega
  have hdiff_lt_k : j - i < k := (Nat.sub_le j i).trans_lt hj_lt
  have hnj_lower : k * k - k + 2 ≤ n - j := by
    apply Nat.le_sub_of_add_le
    have hk_le_kk : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
    have hleft : k * k - k + 2 + j ≤ k * k + 1 := by
      zify [hk_le_kk]
      omega
    exact hleft.trans (Nat.succ_le_of_lt hn_gt)
  set a : ℕ := lPowerFreePart l (n - j) with ha_def
  set bi : ℕ := lPowerRoot l (n - i) with hbi_def
  set bj : ℕ := lPowerRoot l (n - j) with hbj_def
  have hl_pos : 0 < l := by omega
  have ha_pos : 0 < a := by
    rw [ha_def]
    exact lPowerFreePart_pos_of_ne_zero hnj_ne
  have hbj_pos : 0 < bj := by
    rw [hbj_def]
    exact lPowerRoot_pos_of_ne_zero hl_pos hnj_ne
  have hdeci : n - i = a * bi ^ l := by
    have h := self_eq_lPowerFreePart_mul_lPowerRoot_pow l (n - i) hni_ne
    rw [hsame] at h
    simpa [a, bi, ha_def, hbi_def] using h
  have hdecj : n - j = a * bj ^ l := by
    have h := self_eq_lPowerFreePart_mul_lPowerRoot_pow l (n - j) hnj_ne
    simpa [a, bj, ha_def, hbj_def] using h
  have hlt_ab : a * bj ^ l < a * bi ^ l := by
    rw [← hdecj, ← hdeci]
    exact hnj_lt_hni
  have hbj_lt_bi : bj < bi := by
    have hpow : bj ^ l < bi ^ l := Nat.lt_of_mul_lt_mul_left hlt_ab
    exact (Nat.pow_lt_pow_iff_left (by omega : l ≠ 0)).mp hpow
  have hbj_succ_pow_le : (bj + 1) ^ l ≤ bi ^ l := by
    exact Nat.pow_le_pow_left (Nat.succ_le_of_lt hbj_lt_bi) l
  have hdiff_eq : j - i = a * (bi ^ l - bj ^ l) := by
    calc
      j - i = (n - i) - (n - j) := hdiff_nat
      _ = a * bi ^ l - a * bj ^ l := by rw [hdeci, hdecj]
      _ = a * (bi ^ l - bj ^ l) := by rw [Nat.mul_sub_left_distrib]
  have hL_le_diff : l * a * bj ^ (l - 1) ≤ j - i := by
    rw [hdiff_eq]
    calc
      l * a * bj ^ (l - 1) = a * (l * bj ^ (l - 1)) := by ring
      _ ≤ a * ((bj + 1) ^ l - bj ^ l) :=
        Nat.mul_le_mul_left a (l_mul_pow_pred_le_succ_pow_sub_pow bj l (by omega))
      _ ≤ a * (bi ^ l - bj ^ l) :=
        Nat.mul_le_mul_left a (Nat.sub_le_sub_right hbj_succ_pow_le _)
  have hk_sq_lt_four_nj : k * k < 4 * (n - j) := by
    exact (four_mul_sq_sub_add_two_gt_sq hk).trans_le
      (Nat.mul_le_mul_left 4 hnj_lower)
  have hL_sq_ge : 4 * (n - j) ≤ (l * a * bj ^ (l - 1)) * (l * a * bj ^ (l - 1)) := by
    rw [hdecj]
    exact four_mul_l_component_le_sq ha_pos hbj_pos hl
  have hk_lt_L : k < l * a * bj ^ (l - 1) := by
    exact Nat.mul_self_lt_mul_self_iff.mp (hk_sq_lt_four_nj.trans_le hL_sq_ge)
  exact (not_lt_of_ge hL_le_diff) (hdiff_lt_k.trans hk_lt_L)

/-- Step 3a for all exponents `l ≥ 2`: the l-power-free parts in the
descending factorial are pairwise distinct. -/
theorem lPowerFreePart_injective_l
    {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 2 ≤ l)
    (h_eq : n.choose k = m ^ l) :
    Set.InjOn (fun j => lPowerFreePart l (n - j)) (Finset.range k) := by
  intro i hi j hj hsame
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact lPowerFreePart_l_ne_of_lt hk hn hl h_eq hi hj hij hsame
  · exact lPowerFreePart_l_ne_of_lt hk hn hl h_eq hj hi hji hsame.symm

private lemma strictMono_fin_nat_succ_le {k : ℕ} {f : Fin k → ℕ}
    (hf : StrictMono f) (hpos : ∀ i, 0 < f i) :
    ∀ i, i.1 + 1 ≤ f i := by
  induction k with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ k ih =>
      intro i
      refine Fin.cases ?hzero ?hsucc i
      · exact hpos 0
      · intro i
        have hf_prefix : StrictMono (fun t : Fin k => f (Fin.castSucc t)) := by
          intro a b hab
          exact hf (by simpa using hab)
        have hpos_prefix : ∀ t : Fin k, 0 < f (Fin.castSucc t) :=
          fun t => hpos (Fin.castSucc t)
        have hprev : i.1 + 1 ≤ f (Fin.castSucc i) :=
          ih hf_prefix hpos_prefix i
        have hstep : f (Fin.castSucc i) < f i.succ :=
          hf (Fin.castSucc_lt_succ (i := i))
        have hval : (i.succ : Fin (k + 1)).1 = i.1 + 1 := rfl
        omega

private lemma prod_fin_succ_eq_factorial (k : ℕ) :
    (∏ i : Fin k, ((i : ℕ) + 1)) = k.factorial := by
  calc
    (∏ i : Fin k, ((i : ℕ) + 1)) = ∏ i ∈ Finset.range k, (i + 1) := by
      simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) k)
    _ = k.factorial := Finset.prod_range_add_one_eq_factorial k

private lemma prod_orderEmbOfFin_eq {s : Finset ℕ} {k : ℕ} (hcard : s.card = k) :
    (∏ i : Fin k, s.orderEmbOfFin hcard i) = ∏ x ∈ s, x := by
  calc
    (∏ i : Fin k, s.orderEmbOfFin hcard i) =
        ∏ x ∈ Finset.map (s.orderEmbOfFin hcard).toEmbedding Finset.univ, x := by
      simpa using (Finset.prod_map (s := Finset.univ)
        (e := (s.orderEmbOfFin hcard).toEmbedding) (f := fun x : ℕ => x)).symm
    _ = ∏ x ∈ s, x := by
      rw [Finset.map_orderEmbOfFin_univ s hcard]



private lemma factorial_lt_prod_of_card_eq_pos_not_mem
    {s : Finset ℕ} {k t : ℕ} (ht_pos : 1 ≤ t) (htk : t ≤ k)
    (hcard : s.card = k) (hpos : ∀ x ∈ s, 0 < x) (ht_not : t ∉ s) :
    k.factorial < ∏ x ∈ s, x := by
  classical
  let f := s.orderEmbOfFin hcard
  have hf_pos : ∀ i : Fin k, 0 < f i :=
    fun i => hpos (f i) (Finset.orderEmbOfFin_mem s hcard i)
  have hpoint : ∀ i : Fin k, (i : ℕ) + 1 ≤ f i :=
    strictMono_fin_nat_succ_le (f := fun i : Fin k => f i) f.strictMono hf_pos
  let it : Fin k := ⟨t - 1, by omega⟩
  have hit_mem : f it ∈ s := Finset.orderEmbOfFin_mem s hcard it
  have hit_ne : f it ≠ t := fun h => ht_not (h ▸ hit_mem)
  have hit_strict : ((it : ℕ) + 1) < f it := by
    have ht_le : t ≤ f it := by
      have hpoint_it := hpoint it
      simpa [it, Nat.sub_add_cancel ht_pos] using hpoint_it
    have hit_val : (it : ℕ) + 1 = t := by
      simp [it, Nat.sub_add_cancel ht_pos]
    rw [hit_val]
    exact lt_of_le_of_ne ht_le hit_ne.symm
  have hprod_lt : (∏ i : Fin k, ((i : ℕ) + 1)) < ∏ i : Fin k, f i := by
    exact Finset.prod_lt_prod (fun i _ => by omega) (fun i _ => hpoint i)
      ⟨it, Finset.mem_univ it, hit_strict⟩
  calc
    k.factorial = (∏ i : Fin k, ((i : ℕ) + 1)) :=
      (prod_fin_succ_eq_factorial k).symm
    _ < ∏ i : Fin k, f i := hprod_lt
    _ = ∏ x ∈ s, x := prod_orderEmbOfFin_eq hcard

private lemma mem_of_card_eq_pos_prod_dvd_factorial
    {s : Finset ℕ} {k t : ℕ} (ht_pos : 1 ≤ t) (htk : t ≤ k)
    (hcard : s.card = k) (hpos : ∀ x ∈ s, 0 < x)
    (hprod_dvd : (∏ x ∈ s, x) ∣ k !) :
    t ∈ s := by
  by_contra ht_not
  have hlt : k.factorial < ∏ x ∈ s, x :=
    factorial_lt_prod_of_card_eq_pos_not_mem ht_pos htk hcard hpos ht_not
  have hle : ∏ x ∈ s, x ≤ k ! :=
    Nat.le_of_dvd (Nat.factorial_pos k) hprod_dvd
  exact (not_lt_of_ge hle) hlt

private lemma int_natAbs_sub_lt_of_lt {s t k : ℕ} (hs : s < k) (ht : t < k) :
    ((t : ℤ) - (s : ℤ)).natAbs < k := by
  by_cases hst : s ≤ t
  · have hcast : (t : ℤ) - (s : ℤ) = (t - s : ℕ) := by
      exact (Int.ofNat_sub hst).symm
    rw [hcast]
    simp
    omega
  · have hts : t ≤ s := by omega
    have hcast : (t : ℤ) - (s : ℤ) = -((s - t : ℕ) : ℤ) := by
      have h := Int.ofNat_sub hts
      omega
    rw [hcast]
    simp
    omega

private lemma int_natAbs_n_sub_le (n s : ℕ) (hs : s ≤ n) :
    ((n : ℤ) - (s : ℤ)).natAbs ≤ n := by
  have hcast : (n : ℤ) - (s : ℤ) = (n - s : ℕ) := by
    exact (Int.ofNat_sub hs).symm
  rw [hcast]
  simp

private lemma geom_diff_natAbs_lt_two_mul
    {n k r s t : ℕ} (hn_pos : 0 < n) (hr : r < k) (hs : s < k) (ht : t < k)
    (hsn : s ≤ n) (htn : t ≤ n) :
    (((n : ℤ) - (s : ℤ)) ^ 2 - (((n : ℤ) - (r : ℤ)) * ((n : ℤ) - (t : ℤ)))).natAbs
      < 2 * k * n := by
  let E : ℤ := ((n : ℤ) - (s : ℤ)) ^ 2 -
    (((n : ℤ) - (r : ℤ)) * ((n : ℤ) - (t : ℤ)))
  have hE : E = ((n : ℤ) - (s : ℤ)) * ((t : ℤ) - (s : ℤ)) +
        ((n : ℤ) - (t : ℤ)) * ((r : ℤ) - (s : ℤ)) := by
    dsimp [E]
    ring
  have hNs := int_natAbs_n_sub_le n s hsn
  have hNt := int_natAbs_n_sub_le n t htn
  have hts := int_natAbs_sub_lt_of_lt hs ht
  have hrs := int_natAbs_sub_lt_of_lt hs hr
  have hterm1_lt : (((n : ℤ) - (s : ℤ)) * ((t : ℤ) - (s : ℤ))).natAbs < n * k := by
    rw [Int.natAbs_mul]
    exact Nat.mul_lt_mul_of_le_of_lt hNs hts hn_pos
  have hterm2_lt : (((n : ℤ) - (t : ℤ)) * ((r : ℤ) - (s : ℤ))).natAbs < n * k := by
    rw [Int.natAbs_mul]
    exact Nat.mul_lt_mul_of_le_of_lt hNt hrs hn_pos
  calc
    E.natAbs ≤ (((n : ℤ) - (s : ℤ)) * ((t : ℤ) - (s : ℤ))).natAbs +
        (((n : ℤ) - (t : ℤ)) * ((r : ℤ) - (s : ℤ))).natAbs := by
      rw [hE]
      exact Int.natAbs_add_le _ _
    _ < n * k + n * k := by omega
    _ = 2 * k * n := by ring

private lemma int_geom_mean_eq_forces_indices_eq
    {N K R S T : ℤ} (hN : K * K < N)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S) (hT0 : 0 ≤ T)
    (hRk : R < K) (hSk : S < K) (hTk : T < K)
    (heq : (N - S)^2 = (N - R) * (N - T)) : R = T ∧ S = T := by
  have hRT_lt : R * T < K * K := by
    exact mul_lt_mul_of_nonneg hRk hTk hR0 hT0
  have hSsq_lt : S * S < K * K := by
    exact mul_lt_mul_of_nonneg hSk hSk hS0 hS0
  have hexp : (R + T - 2 * S) * N + (S^2 - R*T) = 0 := by nlinarith
  by_cases hCzero : R + T - 2 * S = 0
  · have hconst : S^2 - R*T = 0 := by nlinarith
    have hsq : (R - T)^2 = 0 := by nlinarith
    have hRT : R = T := by
      have hsub : R - T = 0 := (sq_eq_zero_iff.mp hsq)
      omega
    have hST : S = T := by omega
    exact ⟨hRT, hST⟩
  · rcases lt_or_gt_of_ne hCzero with hCneg | hCpos
    · have hleft_gt : K * K < (-(R + T - 2 * S)) * N := by
        nlinarith
      have hleft_eq : (-(R + T - 2 * S)) * N = S^2 - R*T := by nlinarith
      have hright_le : S^2 - R*T ≤ S*S := by nlinarith
      nlinarith
    · have hleft_gt : K * K < (R + T - 2 * S) * N := by
        nlinarith
      have hleft_eq : (R + T - 2 * S) * N = R*T - S^2 := by nlinarith
      have hright_le : R*T - S^2 ≤ R*T := by nlinarith [sq_nonneg S]
      nlinarith

private lemma geom_mean_eq_forces_indices_eq
    {n k r s t : ℕ} (hkn : k * k < n) (hr : r < k) (hs : s < k) (ht : t < k)
    (heq : (n - s)^2 = (n - r) * (n - t)) : r = t ∧ s = t := by
  have hk_le_n : k ≤ n := by
    have hk_pos : 0 < k := by
      by_contra hk0
      omega
    have hk_le_kk : k ≤ k * k := Nat.le_mul_of_pos_left k hk_pos
    omega
  have hrn : r ≤ n := (le_of_lt hr).trans hk_le_n
  have hsn : s ≤ n := (le_of_lt hs).trans hk_le_n
  have htn : t ≤ n := (le_of_lt ht).trans hk_le_n
  have heqz :
      ((n : ℤ) - (s : ℤ))^2 = ((n : ℤ) - (r : ℤ)) * ((n : ℤ) - (t : ℤ)) := by
    zify [hsn, hrn, htn] at heq
    exact heq
  have hres := int_geom_mean_eq_forces_indices_eq
    (N := (n : ℤ)) (K := (k : ℤ)) (R := (r : ℤ)) (S := (s : ℤ)) (T := (t : ℤ))
    (by exact_mod_cast hkn)
    (by exact_mod_cast Nat.zero_le r) (by exact_mod_cast Nat.zero_le s)
    (by exact_mod_cast Nat.zero_le t)
    (by exact_mod_cast hr) (by exact_mod_cast hs) (by exact_mod_cast ht) heqz
  constructor
  · exact_mod_cast hres.1
  · exact_mod_cast hres.2

private lemma natAbs_of_nat_sub_of_le {a b : ℕ} (hab : a ≤ b) :
    (((a : ℤ) - (b : ℤ)).natAbs = b - a) := by
  have hcast : (a : ℤ) - (b : ℤ) = -((b - a : ℕ) : ℤ) := by
    have h := Int.ofNat_sub hab
    omega
  rw [hcast]
  simp

private lemma natAbs_of_nat_sub_of_ge {a b : ℕ} (hab : b ≤ a) :
    (((a : ℤ) - (b : ℤ)).natAbs = a - b) := by
  have hcast : (a : ℤ) - (b : ℤ) = ((a - b : ℕ) : ℤ) := by
    exact (Int.ofNat_sub hab).symm
  rw [hcast]
  simp

private lemma pow_diff_min_lower {A B l : ℕ} (hneq : A ≠ B) (hl : 1 ≤ l) :
    l * (min A B) ^ (l - 1) ≤
      if A ≤ B then B ^ l - A ^ l else A ^ l - B ^ l := by
  by_cases hAB : A ≤ B
  · have hlt : A < B := lt_of_le_of_ne hAB hneq
    have hsucc : A + 1 ≤ B := Nat.succ_le_of_lt hlt
    have hpow_le : (A + 1) ^ l ≤ B ^ l := Nat.pow_le_pow_left hsucc l
    calc
      l * (min A B) ^ (l - 1) = l * A ^ (l - 1) := by rw [min_eq_left hAB]
      _ ≤ (A + 1) ^ l - A ^ l := l_mul_pow_pred_le_succ_pow_sub_pow A l hl
      _ ≤ B ^ l - A ^ l := Nat.sub_le_sub_right hpow_le _
      _ = (if A ≤ B then B ^ l - A ^ l else A ^ l - B ^ l) := by simp [hAB]
  · have hBA : B ≤ A := by omega
    have hlt : B < A := lt_of_le_of_ne hBA (Ne.symm hneq)
    have hsucc : B + 1 ≤ A := Nat.succ_le_of_lt hlt
    have hpow_le : (B + 1) ^ l ≤ A ^ l := Nat.pow_le_pow_left hsucc l
    calc
      l * (min A B) ^ (l - 1) = l * B ^ (l - 1) := by rw [min_eq_right hBA]
      _ ≤ (B + 1) ^ l - B ^ l := l_mul_pow_pred_le_succ_pow_sub_pow B l hl
      _ ≤ A ^ l - B ^ l := Nat.sub_le_sub_right hpow_le _
      _ = (if A ≤ B then B ^ l - A ^ l else A ^ l - B ^ l) := by simp [hAB]

private lemma two_mul_sq_lt_three_mul_sub_sq {n k : ℕ} (hk : 4 ≤ k)
    (hkn : k ^ 3 < n) : 2 * n * n < 3 * (n - k + 1) * (n - k + 1) := by
  have h16k : 16 * k < n := by
    have h16_le : 16 * k ≤ k ^ 3 := by
      have h16_le_kk : 16 ≤ k * k := by nlinarith [hk]
      calc
        16 * k ≤ (k * k) * k := Nat.mul_le_mul_right k h16_le_kk
        _ = k ^ 3 := by ring
    exact lt_of_le_of_lt h16_le hkn
  zify [show k ≤ n by nlinarith [hk, h16k]]
  nlinarith [sq_nonneg ((n : ℤ) - 16 * (k : ℤ)), sq_nonneg ((k : ℤ) - 1)]

/-! ### Interval count + Legendre / `padicValNat_factorial` helpers (Tier 2 building blocks for Ch03) -/



/-! ### Legendre / `padicValNat_factorial` helpers -/













/-! ### Erdős divisibility step (general l) -/



/-! ### Erdős divisibility step (l = 2 case): discharge of `hprod_l2` -/







/-! ### Main theorem assembly -/




end Tier1

end ProofsInTheBook.Chapter03

open ProofsInTheBook.Chapter03
open Nat

theorem solution
    {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 3 ≤ l) :
    n.choose k ≠ m ^ l := by
  classical
  intro h_eq
  have hl2 : 2 ≤ l := by omega
  have hl_pos : 0 < l := by omega
  have hk_le_n : k ≤ n := by omega
  have hn_pos : 0 < n := by omega
  have hn_gt_sq : k * k < n := erdos_step1_n_gt_k_sq hk hn hl2 h_eq
  have hn_gt_pow : k ^ l < n := erdos_step1_n_gt_k_pow hk hn hl2 h_eq
  have hn_gt_cube : k ^ 3 < n := by
    exact (Nat.pow_le_pow_right (by omega : 0 < k) hl).trans_lt hn_gt_pow
  let a : ℕ → ℕ := fun j => lPowerFreePart l (n - j)
  let S : Finset ℕ := (Finset.range k).image a
  have hinj : Set.InjOn a (Finset.range k) := by
    simpa [a] using lPowerFreePart_injective_l hk hn hl2 h_eq
  have hcard : S.card = k := by
    dsimp [S]
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    have hj_lt : j < k := Finset.mem_range.mp hj
    have hnj_ne : n - j ≠ 0 := by
      exact Nat.ne_of_gt (Nat.sub_pos_of_lt (hj_lt.trans_le hk_le_n))
    exact lPowerFreePart_pos_of_ne_zero hnj_ne
  have hprod_S :
      (∏ x ∈ S, x) = ∏ j ∈ Finset.range k, a j := by
    dsimp [S]
    rw [Finset.prod_image hinj]
  have hprod_dvd : (∏ x ∈ S, x) ∣ k ! := by
    rw [hprod_S]
    simpa [a] using prod_lPowerFreeParts_dvd_factorial hk hn hl2 h_eq
  have h1_mem : 1 ∈ S :=
    mem_of_card_eq_pos_prod_dvd_factorial (k := k) (t := 1)
      (by norm_num) (by omega) hcard hpos hprod_dvd
  have h2_mem : 2 ∈ S :=
    mem_of_card_eq_pos_prod_dvd_factorial (k := k) (t := 2)
      (by norm_num) (by omega) hcard hpos hprod_dvd
  have h4_mem : 4 ∈ S :=
    mem_of_card_eq_pos_prod_dvd_factorial (k := k) (t := 4)
      (by norm_num) hk hcard hpos hprod_dvd
  rcases Finset.mem_image.mp h1_mem with ⟨i1, hi1, h1eq⟩
  rcases Finset.mem_image.mp h2_mem with ⟨i2, hi2, h2eq⟩
  rcases Finset.mem_image.mp h4_mem with ⟨i4, hi4, h4eq⟩
  have hi1_lt : i1 < k := Finset.mem_range.mp hi1
  have hi2_lt : i2 < k := Finset.mem_range.mp hi2
  have hi4_lt : i4 < k := Finset.mem_range.mp hi4
  have hi1_le_n : i1 ≤ n := (le_of_lt hi1_lt).trans hk_le_n
  have hi2_le_n : i2 ≤ n := (le_of_lt hi2_lt).trans hk_le_n
  have hi4_le_n : i4 ≤ n := (le_of_lt hi4_lt).trans hk_le_n
  have hni1_ne : n - i1 ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt (hi1_lt.trans_le hk_le_n))
  have hni2_ne : n - i2 ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt (hi2_lt.trans_le hk_le_n))
  have hni4_ne : n - i4 ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt (hi4_lt.trans_le hk_le_n))
  have hfree1 : lPowerFreePart l (n - i1) = 1 := by simpa [a] using h1eq
  have hfree2 : lPowerFreePart l (n - i2) = 2 := by simpa [a] using h2eq
  have hfree4 : lPowerFreePart l (n - i4) = 4 := by simpa [a] using h4eq
  set x : ℕ := lPowerRoot l (n - i1) with hx_def
  set y : ℕ := lPowerRoot l (n - i2) with hy_def
  set z : ℕ := lPowerRoot l (n - i4) with hz_def
  have hx_pos : 0 < x := by
    rw [hx_def]
    exact lPowerRoot_pos_of_ne_zero hl_pos hni1_ne
  have hy_pos : 0 < y := by
    rw [hy_def]
    exact lPowerRoot_pos_of_ne_zero hl_pos hni2_ne
  have hz_pos : 0 < z := by
    rw [hz_def]
    exact lPowerRoot_pos_of_ne_zero hl_pos hni4_ne
  have hdec1 : n - i1 = x ^ l := by
    have h := self_eq_lPowerFreePart_mul_lPowerRoot_pow l (n - i1) hni1_ne
    rw [hfree1] at h
    simpa [x, hx_def] using h
  have hdec2 : n - i2 = 2 * y ^ l := by
    have h := self_eq_lPowerFreePart_mul_lPowerRoot_pow l (n - i2) hni2_ne
    rw [hfree2] at h
    simpa [y, hy_def] using h
  have hdec4 : n - i4 = 4 * z ^ l := by
    have h := self_eq_lPowerFreePart_mul_lPowerRoot_pow l (n - i4) hni4_ne
    rw [hfree4] at h
    simpa [z, hz_def] using h
  have hi1_ne_i4 : i1 ≠ i4 := by
    intro hidx
    have : (1 : ℕ) = 4 := by
      rw [← hfree1, hidx, hfree4]
    norm_num at this
  let A : ℕ := y ^ 2
  let B : ℕ := x * z
  let T : ℕ := min A B
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hx_pos hz_pos
  have hT_pos : 0 < T := by
    dsimp [T]
    exact lt_min hA_pos hB_pos
  have hsquare_eq : (n - i2) ^ 2 = 4 * A ^ l := by
    rw [hdec2]
    dsimp [A]
    rw [mul_pow]
    norm_num
    rw [← pow_mul, ← pow_mul]
    ring_nf
  have hprod_eq : (n - i1) * (n - i4) = 4 * B ^ l := by
    rw [hdec1, hdec4]
    dsimp [B]
    rw [mul_pow]
    ring
  have hA_ne_B : A ≠ B := by
    intro hABeq
    have hpows_eq : A ^ l = B ^ l := by rw [hABeq]
    have hsqprod : (n - i2) ^ 2 = (n - i1) * (n - i4) := by
      rw [hsquare_eq, hprod_eq, hpows_eq]
    rcases geom_mean_eq_forces_indices_eq hn_gt_sq hi1_lt hi2_lt hi4_lt hsqprod with ⟨hi14, _hi24⟩
    exact hi1_ne_i4 hi14
  let Dn : ℕ :=
    (((n : ℤ) - (i2 : ℤ)) ^ 2 -
      (((n : ℤ) - (i1 : ℤ)) * ((n : ℤ) - (i4 : ℤ)))).natAbs
  have hupper : Dn < 2 * k * n := by
    dsimp [Dn]
    exact geom_diff_natAbs_lt_two_mul hn_pos hi1_lt hi2_lt hi4_lt hi2_le_n hi4_le_n
  have hsub1 : (n : ℤ) - (i1 : ℤ) = ((n - i1 : ℕ) : ℤ) := (Int.ofNat_sub hi1_le_n).symm
  have hsub2 : (n : ℤ) - (i2 : ℤ) = ((n - i2 : ℕ) : ℤ) := (Int.ofNat_sub hi2_le_n).symm
  have hsub4 : (n : ℤ) - (i4 : ℤ) = ((n - i4 : ℕ) : ℤ) := (Int.ofNat_sub hi4_le_n).symm
  let Dpow : ℕ := if A ≤ B then B ^ l - A ^ l else A ^ l - B ^ l
  have hDn_eq : Dn = 4 * Dpow := by
    dsimp [Dn]
    rw [hsub1, hsub2, hsub4]
    rw [← Nat.cast_pow, ← Nat.cast_mul]
    rw [hsquare_eq, hprod_eq]
    by_cases hAB : A ≤ B
    · have hpow_le : A ^ l ≤ B ^ l := Nat.pow_le_pow_left hAB l
      have hle4 : 4 * A ^ l ≤ 4 * B ^ l := Nat.mul_le_mul_left 4 hpow_le
      rw [natAbs_of_nat_sub_of_le hle4]
      dsimp [Dpow]
      rw [if_pos hAB, Nat.mul_sub_left_distrib]
    · have hBA : B ≤ A := by omega
      have hpow_le : B ^ l ≤ A ^ l := Nat.pow_le_pow_left hBA l
      have hle4 : 4 * B ^ l ≤ 4 * A ^ l := Nat.mul_le_mul_left 4 hpow_le
      rw [natAbs_of_nat_sub_of_ge hle4]
      dsimp [Dpow]
      rw [if_neg hAB, Nat.mul_sub_left_distrib]
  have hlower_pow : l * T ^ (l - 1) ≤ Dpow := by
    dsimp [T, Dpow]
    exact pow_diff_min_lower hA_ne_B (by omega : 1 ≤ l)
  have hdiff_lt : 4 * (l * T ^ (l - 1)) < 2 * k * n := by
    rw [hDn_eq] at hupper
    exact (Nat.mul_le_mul_left 4 hlower_pow).trans_lt hupper
  have hlow1 : n - k + 1 ≤ n - i1 := by omega
  have hlow2 : n - k + 1 ≤ n - i2 := by omega
  have hlow4 : n - k + 1 ≤ n - i4 := by omega
  have hlow_sq_le_A : (n - k + 1) ^ 2 ≤ 4 * A ^ l := by
    rw [← hsquare_eq]
    exact Nat.pow_le_pow_left hlow2 2
  have hlow_sq_le_B : (n - k + 1) ^ 2 ≤ 4 * B ^ l := by
    rw [← hprod_eq]
    have hmul := Nat.mul_le_mul hlow1 hlow4
    simpa [pow_two] using hmul
  have hlow_sq_le_T : (n - k + 1) ^ 2 ≤ 4 * T ^ l := by
    dsimp [T]
    by_cases hAB : A ≤ B
    · rw [min_eq_left hAB]
      exact hlow_sq_le_A
    · have hBA : B ≤ A := by omega
      rw [min_eq_right hBA]
      exact hlow_sq_le_B
  have hbig_low : 2 * n * n < l * ((n - k + 1) ^ 2) := by
    have hthree := two_mul_sq_lt_three_mul_sub_sq hk hn_gt_cube
    have hthree_le : 3 * ((n - k + 1) ^ 2) ≤ l * ((n - k + 1) ^ 2) :=
      Nat.mul_le_mul_right _ hl
    have hthree' : 2 * n * n < 3 * ((n - k + 1) ^ 2) := by
      simpa [pow_two, mul_assoc] using hthree
    exact hthree'.trans_le hthree_le
  have hbig_T : 2 * n * n < 4 * l * T ^ l := by
    have h := hbig_low.trans_le (Nat.mul_le_mul_left l hlow_sq_le_T)
    calc
      2 * n * n < l * (4 * T ^ l) := h
      _ = 4 * l * T ^ l := by ring
  have hdiff_mul : 4 * l * T ^ l < 2 * k * n * T := by
    calc
      4 * l * T ^ l = (4 * (l * T ^ (l - 1))) * T := by
        have hpow : T ^ (l - 1) * T = T ^ l := pow_sub_one_mul hl_pos.ne' T
        rw [← hpow]
        ring
      _ < (2 * k * n) * T := Nat.mul_lt_mul_of_pos_right hdiff_lt hT_pos
      _ = 2 * k * n * T := by ring
  have hn_lt_kT : n < k * T := by
    have hchain : 2 * n * n < 2 * k * n * T := hbig_T.trans hdiff_mul
    have hmul : (2 * n) * n < (2 * n) * (k * T) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hchain
    exact (Nat.mul_lt_mul_left (by omega : 0 < 2 * n)).mp hmul
  have hx_l_le_n : x ^ l ≤ n := by omega
  have hy_l_le_n : y ^ l ≤ n := by omega
  have hz_l_le_n : z ^ l ≤ n := by omega
  have hA_l_le : A ^ l ≤ n * n := by
    dsimp [A]
    rw [← pow_mul, mul_comm 2 l, pow_mul]
    simpa [pow_two] using Nat.mul_le_mul hy_l_le_n hy_l_le_n
  have hB_l_le : B ^ l ≤ n * n := by
    dsimp [B]
    rw [mul_pow]
    exact Nat.mul_le_mul hx_l_le_n hz_l_le_n
  have hT_l_le : T ^ l ≤ n * n := by
    dsimp [T]
    by_cases hAB : A ≤ B
    · rw [min_eq_left hAB]
      exact hA_l_le
    · have hBA : B ≤ A := by omega
      rw [min_eq_right hBA]
      exact hB_l_le
  have hT3_le_nsq : T ^ 3 ≤ n * n := by
    exact (Nat.pow_le_pow_right hT_pos hl).trans hT_l_le
  have hcube_lt : n ^ 3 < (k * T) ^ 3 :=
    Nat.pow_lt_pow_left hn_lt_kT (by norm_num : (3 : ℕ) ≠ 0)
  rw [mul_pow] at hcube_lt
  have hcube_le : k ^ 3 * T ^ 3 ≤ k ^ 3 * (n * n) :=
    Nat.mul_le_mul_left (k ^ 3) hT3_le_nsq
  have hn3_lt : n ^ 3 < k ^ 3 * (n * n) := hcube_lt.trans_le hcube_le
  have hn_lt_k3 : n < k ^ 3 := by
    have hmul : n * (n * n) < k ^ 3 * (n * n) := by
      simpa [pow_succ, pow_two, mul_assoc, mul_left_comm, mul_comm] using hn3_lt
    exact Nat.lt_of_mul_lt_mul_right hmul
  omega
