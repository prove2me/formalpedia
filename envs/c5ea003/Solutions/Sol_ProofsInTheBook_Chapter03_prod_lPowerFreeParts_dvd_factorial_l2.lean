-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.prod_lPowerFreeParts_dvd_factorial_l2
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:36:58.385545+00:00
-- url     : https://prove2.me/submissions/73934067-d8a5-4a56-aa86-b2ea1d39e30c

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03


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







/-! ### Step 2: l-th-power-free decomposition -/





open scoped BigOperators in
lemma self_eq_lPowerFreePart_mul_lPowerRoot_pow (l m : ℕ) (hm : m ≠ 0) :
    m = lPowerFreePart l m * (lPowerRoot l m) ^ l := by
  have h_prod := (Nat.prod_factorization_pow_eq_self hm).symm
  have h_factor (p : ℕ) : p ^ (m.factorization p % l + l * (m.factorization p / l)) =
      (p ^ (m.factorization p % l)) * ((p ^ (m.factorization p / l)) ^ l) := by
    calc
      p ^ (m.factorization p % l + l * (m.factorization p / l))
          = p ^ (m.factorization p % l) * p ^ (l * (m.factorization p / l)) := by rw [pow_add]
      _ = p ^ (m.factorization p % l) * (p ^ (m.factorization p / l)) ^ l := by
        rw [mul_comm l (m.factorization p / l), ← pow_mul]
      _ = (p ^ (m.factorization p % l)) * ((p ^ (m.factorization p / l)) ^ l) := rfl
  dsimp [lPowerFreePart, lPowerRoot]
  calc
    m = m.factorization.prod (· ^ ·) := h_prod
    _ = ∏ p ∈ m.factorization.support, p ^ (m.factorization p) := rfl
    _ = ∏ p ∈ m.factorization.support, p ^ (m.factorization p % l + l * (m.factorization p / l)) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.mod_add_div (m.factorization p) l]
    _ = ∏ p ∈ m.factorization.support,
        (p ^ (m.factorization p % l)) * ((p ^ (m.factorization p / l)) ^ l) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [h_factor p]
    _ = (∏ p ∈ m.factorization.support, p ^ (m.factorization p % l)) *
        (∏ p ∈ m.factorization.support, (p ^ (m.factorization p / l)) ^ l) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ m.factorization.support, p ^ (m.factorization p % l)) *
        (∏ p ∈ m.factorization.support, p ^ (m.factorization p / l)) ^ l := by
      rw [Finset.prod_pow]
    _ = lPowerFreePart l m * (lPowerRoot l m) ^ l := rfl

/-! ### 2-power-free part: factorization mod 2 (Tier 2 building block for Ch03) -/


























/-- The 2-power-free part `lPowerFreePart 2 m` divides the squarefree radical
`∏ q ∈ m.primeFactors, q` (since each prime appears with exponent in `{0, 1}`). -/
private lemma lPowerFreePart_dvd_radical (m : ℕ) :
    lPowerFreePart 2 m ∣ ∏ q ∈ m.factorization.support, q := by
  classical
  dsimp [lPowerFreePart]
  refine Finset.prod_dvd_prod_of_dvd _ _ (fun q hq => ?_)
  -- q^(m.factorization q % 2) ∣ q since the exponent is ≤ 1.
  have h_le : m.factorization q % 2 ≤ 1 := by omega
  calc q ^ (m.factorization q % 2)
      ∣ q ^ 1 := pow_dvd_pow q h_le
    _ = q := pow_one q

/-- The 2-power-free part of `m` is squarefree. -/
private lemma lPowerFreePart_squarefree (m : ℕ) (_hm : m ≠ 0) :
    Squarefree (lPowerFreePart 2 m) := by
  classical
  -- The radical ∏ q ∈ supp, q is squarefree, and lPowerFreePart divides it.
  have h_radical_ne : (∏ q ∈ m.factorization.support, q) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors
      ((Nat.support_factorization _).symm ▸ hq)
    exact hq_prime.pos.ne'
  have h_radical_sf : Squarefree (∏ q ∈ m.factorization.support, q) := by
    refine (Nat.squarefree_iff_factorization_le_one h_radical_ne).mpr (fun p => ?_)
    rw [Nat.factorization_prod_apply (fun q hq => by
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors
        ((Nat.support_factorization _).symm ▸ hq)
      exact hq_prime.pos.ne')]
    by_cases hp : p.Prime
    · -- Sum has at most one term equal to 1 (when q = p), rest are 0.
      calc ∑ q ∈ m.factorization.support, q.factorization p
          ≤ ∑ q ∈ m.factorization.support, if q = p then 1 else 0 := by
            refine Finset.sum_le_sum (fun q hq => ?_)
            have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors
              ((Nat.support_factorization _).symm ▸ hq)
            rw [Nat.Prime.factorization hq_prime, Finsupp.single_apply]
        _ = (if p ∈ m.factorization.support then 1 else 0) := by
            rw [Finset.sum_ite_eq']
        _ ≤ 1 := by split_ifs <;> simp
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  -- lPowerFreePart 2 m ∣ radical; divisors of squarefree are squarefree.
  exact h_radical_sf.squarefree_of_dvd (lPowerFreePart_dvd_radical m)










/-- For `m ≠ 0`, the factorization of `lPowerFreePart 2 m` at `p` equals
`m.factorization p % 2`. This is the key arithmetic identity used in the Erdős
divisibility step. -/
private lemma lPowerFreePart_factorization_eq_mod (m p : ℕ) (hm : m ≠ 0) :
    (lPowerFreePart 2 m).factorization p = m.factorization p % 2 := by
  -- m = lPowerFreePart 2 m * (lPowerRoot 2 m)^2, and lPowerFreePart is squarefree.
  have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 m hm
  have hpf_ne : lPowerFreePart 2 m ≠ 0 := by
    intro hz; rw [hz, zero_mul] at hsplit; exact hm hsplit
  have hpr_ne : lPowerRoot 2 m ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hsplit
    exact hm hsplit
  have hfactor :
      m.factorization p = (lPowerFreePart 2 m).factorization p +
        2 * (lPowerRoot 2 m).factorization p := by
    conv_lhs => rw [hsplit]
    rw [Nat.factorization_mul hpf_ne (pow_ne_zero 2 hpr_ne),
        Nat.factorization_pow]
    simp [Finsupp.add_apply, two_mul, Finsupp.smul_apply, smul_eq_mul]
  -- Squarefree ⇒ factorization ≤ 1.
  have h_sf := lPowerFreePart_squarefree m hm
  have h_le : (lPowerFreePart 2 m).factorization p ≤ 1 :=
    Squarefree.natFactorization_le_one p h_sf
  omega





















































/-! ### Interval count + Legendre / `padicValNat_factorial` helpers (Tier 2 building blocks for Ch03) -/

/-- Count of `j ∈ range k` with `p ∣ (n - j)`, given `k ≤ n`, is at most `k / p + 1`.
The proof bijects the filter onto multiples of `p` in `Ioc (n - k) n`, then bounds
that count via `Nat.Ioc_filter_dvd_card_eq_div`. -/
private lemma card_filter_dvd_le_aux {n k p : ℕ} (hp : 1 ≤ p) (hkn : k ≤ n) :
    ((Finset.range k).filter (fun j => p ∣ (n - j))).card ≤ k / p + 1 := by
  classical
  -- Step 1: bijection j ↦ n - j onto multiples of p in (n - k, n].
  have h_card_eq :
      ((Finset.range k).filter (fun j => p ∣ (n - j))).card =
        ((Finset.Ioc (n - k) n).filter (fun x => p ∣ x)).card := by
    refine Finset.card_bij (fun j _ => n - j) ?h_mem ?h_inj ?h_surj
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjk, hjd⟩ := hj
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, hjd⟩ <;> omega
    · intro j1 hj1 j2 hj2 h_eq
      simp only [Finset.mem_filter, Finset.mem_range] at hj1 hj2
      obtain ⟨hj1k, _⟩ := hj1
      obtain ⟨hj2k, _⟩ := hj2
      simp only at h_eq
      omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxd⟩ := hx
      refine ⟨n - x, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have hnn : n - (n - x) = x := by omega
        rw [hnn]; exact hxd
      · simp only
        omega
  rw [h_card_eq]
  -- Step 2: count in (n-k, n] = count in (0, n] - count in (0, n-k] (when k > 0).
  by_cases hk0 : k = 0
  · subst hk0; simp
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
  have h_split : Finset.Ioc 0 n =
      (Finset.Ioc 0 (n - k)) ∪ (Finset.Ioc (n - k) n) := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega : n - k ≤ n)]
  have h_disj : Disjoint (Finset.Ioc 0 (n - k)) (Finset.Ioc (n - k) n) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Ioc] at hx1 hx2
    omega
  have h_filter_union :
      (Finset.Ioc 0 n).filter (fun x => p ∣ x) =
        (Finset.Ioc 0 (n - k)).filter (fun x => p ∣ x) ∪
          (Finset.Ioc (n - k) n).filter (fun x => p ∣ x) := by
    rw [h_split, Finset.filter_union]
  have h_filter_disj :
      Disjoint ((Finset.Ioc 0 (n - k)).filter (fun x => p ∣ x))
               ((Finset.Ioc (n - k) n).filter (fun x => p ∣ x)) :=
    h_disj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h_card_total :
      ((Finset.Ioc 0 n).filter (fun x => p ∣ x)).card =
        ((Finset.Ioc 0 (n - k)).filter (fun x => p ∣ x)).card +
          ((Finset.Ioc (n - k) n).filter (fun x => p ∣ x)).card := by
    rw [h_filter_union, Finset.card_union_of_disjoint h_filter_disj]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at h_card_total
  -- Step 3: arithmetic — n/p - (n-k)/p ≤ k/p + 1.
  have hp_pos : 0 < p := hp
  have h_split_div : (n - k + k) / p ≤ (n - k) / p + k / p + 1 := by
    have h := Nat.add_div hp_pos (a := n - k) (b := k)
    -- Nat.add_div: (a + b) / n = a/n + b/n + if (a%n + b%n) < n then 0 else 1
    split_ifs at h <;> omega
  have h_sum_eq : (n - k) + k = n := by omega
  rw [h_sum_eq] at h_split_div
  omega

/-! ### Legendre / `padicValNat_factorial` helpers -/



/-- For prime `p` with `p ^ 2 ≤ k`, `(k !).factorization p ≥ k / p + 1`. -/
private lemma factorization_factorial_ge_div_succ
    (k p : ℕ) (hp : p.Prime) (hpk : p ^ 2 ≤ k) :
    k / p + 1 ≤ (k !).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  have hp_pos : 0 < p := hp.pos
  have h_p2_pos : 0 < p ^ 2 := pow_pos hp_pos 2
  have hk_pos : 1 ≤ k := le_trans h_p2_pos hpk
  have hkp : p ≤ k := le_trans (Nat.le_self_pow (by norm_num) p) hpk
  have h_log_ge_two : 2 ≤ Nat.log p k := by
    have := Nat.log_mono_right (b := p) hpk
    rwa [Nat.log_pow hp.one_lt] at this
  have hlog : Nat.log p k < Nat.log p k + 1 := Nat.lt_succ_self _
  rw [padicValNat_factorial hlog]
  have h_split : Finset.Ico 1 (Nat.log p k + 1) =
      insert 1 (Finset.Ico 2 (Nat.log p k + 1)) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [h_split, Finset.sum_insert (by simp [Finset.mem_Ico]), pow_one]
  have h_2_mem : 2 ∈ Finset.Ico 2 (Nat.log p k + 1) := by
    refine Finset.mem_Ico.mpr ⟨le_refl _, ?_⟩
    omega
  have h_p2_div : 1 ≤ k / p ^ 2 := (Nat.one_le_div_iff h_p2_pos).mpr hpk
  have h_rest_ge : 1 ≤ ∑ i ∈ Finset.Ico 2 (Nat.log p k + 1), k / p ^ i := by
    calc 1 ≤ k / p ^ 2 := h_p2_div
      _ ≤ ∑ i ∈ Finset.Ico 2 (Nat.log p k + 1), k / p ^ i :=
          Finset.single_le_sum (f := fun i => k / p ^ i)
            (fun _ _ => Nat.zero_le _) h_2_mem
  omega

/-- For prime `p` with `k < p ^ 2`, Legendre simplifies: `(k !).factorization p = k / p`. -/
private lemma factorization_factorial_eq_div_of_sq_lt
    (k p : ℕ) (hp : p.Prime) (hpk : k < p ^ 2) :
    (k !).factorization p = k / p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  by_cases hk : k = 0
  · subst hk; simp
  have hlog : Nat.log p k < 2 := by
    rw [Nat.log_lt_iff_lt_pow hp.one_lt hk]
    exact hpk
  rw [padicValNat_factorial hlog]
  rw [show (Finset.Ico 1 2 : Finset ℕ) = {1} from rfl, Finset.sum_singleton, pow_one]







/-! ### Erdős divisibility step (general l) -/



/-! ### Erdős divisibility step (l = 2 case): discharge of `hprod_l2` -/







/-! ### Main theorem assembly -/




end Tier1

end ProofsInTheBook.Chapter03

open Nat
open ProofsInTheBook.Chapter03

theorem solution
    {n k m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (h_eq : n.choose k = m ^ 2) :
    (∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j)) ∣ k ! := by
  classical
  set P : ℕ := ∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j) with hP_def
  have h_njne : ∀ j ∈ Finset.range k, (n - j) ≠ 0 := fun j hj => by
    have : j < k := Finset.mem_range.mp hj; omega
  have h_factor_ne : ∀ j ∈ Finset.range k, lPowerFreePart 2 (n - j) ≠ 0 := by
    intro j hj hz
    have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 (n - j) (h_njne j hj)
    rw [hz, zero_mul] at hsplit
    exact h_njne j hj hsplit
  have hP_ne : P ≠ 0 := by
    rw [hP_def, Finset.prod_ne_zero_iff]; exact h_factor_ne
  have hkfact_ne : (k ! : ℕ) ≠ 0 := Nat.factorial_ne_zero k
  rw [← Nat.factorization_le_iff_dvd hP_ne hkfact_ne, Finsupp.le_def]
  intro p
  by_cases hp_prime : p.Prime
  · have hp_pos : 1 ≤ p := hp_prime.one_lt.le
    -- P.factorization p = ∑ j ∈ range k, (n - j).factorization p % 2.
    have hP_factor :
        P.factorization p =
          ∑ j ∈ Finset.range k, (n - j).factorization p % 2 := by
      rw [hP_def, Nat.factorization_prod_apply h_factor_ne]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      exact lPowerFreePart_factorization_eq_mod (n - j) p (h_njne j hj)
    -- Upper bound: factorization(P) p ≤ #{j : p ∣ (n-j)} ≤ k/p + 1.
    have h_upper : P.factorization p ≤ k / p + 1 := by
      rw [hP_factor]
      have h_sum_le :
          ∑ j ∈ Finset.range k, (n - j).factorization p % 2 ≤
            ((Finset.range k).filter (fun j => p ∣ (n - j))).card := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range k)
              (fun j => p ∣ (n - j))]
        have h_not_zero :
            ∀ j ∈ ((Finset.range k).filter (fun j => ¬ p ∣ (n - j))),
              (n - j).factorization p % 2 = 0 := by
          intro j hj
          rw [Finset.mem_filter] at hj
          rw [Nat.factorization_eq_zero_of_not_dvd hj.2]
        rw [Finset.sum_congr rfl h_not_zero, Finset.sum_const_zero, add_zero]
        calc
          ∑ j ∈ ((Finset.range k).filter (fun j => p ∣ (n - j))),
              (n - j).factorization p % 2
              ≤ ∑ _ ∈ ((Finset.range k).filter (fun j => p ∣ (n - j))), 1 := by
                refine Finset.sum_le_sum ?_
                intro j _
                have := Nat.mod_lt ((n - j).factorization p) (by norm_num : 0 < 2)
                omega
            _ = ((Finset.range k).filter (fun j => p ∣ (n - j))).card := by
                rw [Finset.sum_const, smul_eq_mul, mul_one]
      have h_card_le := card_filter_dvd_le_aux hp_pos (by omega : k ≤ n)
      omega
    -- Parity: factorization(P) p ≡ factorization(k!) p (mod 2)
    -- from n.descFactorial k = P * Q^2 = k! * m^2.
    have h_parity : P.factorization p % 2 = (k !).factorization p % 2 := by
      set Q : ℕ := ∏ j ∈ Finset.range k, lPowerRoot 2 (n - j) with hQ_def
      have h_desc_split : n.descFactorial k = P * Q ^ 2 := by
        rw [hP_def, hQ_def, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
            Nat.descFactorial_eq_prod_range]
        refine Finset.prod_congr rfl (fun j hj => ?_)
        exact self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 (n - j) (h_njne j hj)
      have h_desc_choose : n.descFactorial k = k ! * m ^ 2 := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, h_eq]
      have hQ_ne : Q ≠ 0 := by
        rw [hQ_def, Finset.prod_ne_zero_iff]
        intro j hj hz
        have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow 2 (n - j) (h_njne j hj)
        rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hsplit
        exact h_njne j hj hsplit
      have h_choose_pos : 0 < n.choose k := Nat.choose_pos (by omega : k ≤ n)
      have hm_ne : m ≠ 0 := by
        intro hz
        rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h_eq
        omega
      have h_eq_PQ : P * Q ^ 2 = k ! * m ^ 2 := by
        rw [show P * Q^2 = n.descFactorial k from h_desc_split.symm]
        exact h_desc_choose
      have h_apply : (P * Q ^ 2).factorization p = (k ! * m ^ 2).factorization p :=
        congrArg (fun n => n.factorization p) h_eq_PQ
      rw [Nat.factorization_mul hP_ne (pow_ne_zero 2 hQ_ne),
          Nat.factorization_mul hkfact_ne (pow_ne_zero 2 hm_ne),
          Nat.factorization_pow, Nat.factorization_pow] at h_apply
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h_apply
      omega
    -- Combine bounds + parity to conclude factorization(P) p ≤ factorization(k!) p.
    by_cases hp_sq : p ^ 2 ≤ k
    · have h_lower := factorization_factorial_ge_div_succ k p hp_prime hp_sq
      omega
    · push Not at hp_sq
      have h_eq_k := factorization_factorial_eq_div_of_sq_lt k p hp_prime hp_sq
      omega
  · -- Non-prime p: both factorizations 0.
    rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime,
        Nat.factorization_eq_zero_of_not_prime _ hp_prime]
