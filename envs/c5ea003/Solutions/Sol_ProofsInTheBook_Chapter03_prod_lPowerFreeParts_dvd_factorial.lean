-- Prove2me | solution 1 for ProofsInTheBook.Chapter03.prod_lPowerFreeParts_dvd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:36:38.511768+00:00
-- url     : https://prove2.me/submissions/789cf699-fef9-4692-9ea7-b5f1b5ae2446

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













/-- The l-power-free part is nonzero on nonzero input. -/
theorem lPowerFreePart_ne_zero {l m : ℕ} (hm : m ≠ 0) :
    lPowerFreePart l m ≠ 0 := by
  intro hz
  have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow l m hm
  rw [hz, zero_mul] at hsplit
  exact hm hsplit



/-- The l-power root is nonzero on nonzero input when `l > 0`. -/
theorem lPowerRoot_ne_zero {l m : ℕ} (hl : 0 < l) (hm : m ≠ 0) :
    lPowerRoot l m ≠ 0 := by
  intro hz
  have hsplit := self_eq_lPowerFreePart_mul_lPowerRoot_pow l m hm
  rw [hz, zero_pow hl.ne', mul_zero] at hsplit
  exact hm hsplit



/-- For all `l`, the factorization of the l-power-free part is the original
factorization reduced modulo `l`. -/
private lemma lPowerFreePart_factorization_eq_mod_general (l m p : ℕ) :
    (lPowerFreePart l m).factorization p = m.factorization p % l := by
  classical
  rw [lPowerFreePart]
  have hfac_ne : ∀ q ∈ m.factorization.support, q ^ (m.factorization q % l) ≠ 0 := by
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors
      ((Nat.support_factorization _).symm ▸ hq)
    exact pow_ne_zero _ hq_prime.ne_zero
  rw [Nat.factorization_prod_apply hfac_ne]
  by_cases hp : p.Prime
  · calc
      ∑ q ∈ m.factorization.support, (q ^ (m.factorization q % l)).factorization p
          = ∑ q ∈ m.factorization.support, if q = p then m.factorization p % l else 0 := by
            refine Finset.sum_congr rfl (fun q hq => ?_)
            have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors
              ((Nat.support_factorization _).symm ▸ hq)
            rw [Nat.factorization_pow, hq_prime.factorization, Finsupp.smul_apply,
              Finsupp.single_apply]
            by_cases hqp : q = p
            · subst hqp
              simp
            · simp [hqp]
      _ = (if p ∈ m.factorization.support then m.factorization p % l else 0) := by
            rw [Finset.sum_ite_eq']
      _ = m.factorization p % l := by
            split_ifs with hp_mem
            · rfl
            · have hp_zero : m.factorization p = 0 := by
                exact not_not.mp ((Finsupp.mem_support_iff).not.mp hp_mem)
              rw [hp_zero, zero_mod]
  · have hsum_zero :
        (∑ q ∈ m.factorization.support, (q ^ (m.factorization q % l)).factorization p) = 0 := by
        apply Finset.sum_eq_zero
        intro q _hq
        exact Nat.factorization_eq_zero_of_not_prime _ hp
    have hp_zero : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_prime m hp
    rw [hsum_zero, hp_zero, zero_mod]







































































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







/-- A factorization residue modulo `l` is bounded by the number of initial
prime-power layers `p, p^2, ..., p^(l-1)` that divide the number. -/
private lemma factorization_mod_le_count_pow_dvd
    {p x l : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hl : 0 < l) :
    x.factorization p % l ≤
      ∑ r ∈ Finset.range (l - 1), if p ^ (r + 1) ∣ x then 1 else 0 := by
  classical
  let t := x.factorization p % l
  have ht_lt : t < l := by simpa [t] using Nat.mod_lt (x.factorization p) hl
  have hsub : Finset.range t ⊆ (Finset.range (l - 1)).filter (fun r => p ^ (r + 1) ∣ x) := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have hle_v : r + 1 ≤ x.factorization p := by
      have hle_t : r + 1 ≤ t := by omega
      exact hle_t.trans (Nat.mod_le _ _)
    exact (hp.pow_dvd_iff_le_factorization hx).mpr hle_v
  have hcard_le := Finset.card_le_card hsub
  calc
    x.factorization p % l = (Finset.range t).card := by simp [t]
    _ ≤ ((Finset.range (l - 1)).filter (fun r => p ^ (r + 1) ∣ x)).card := hcard_le
    _ = ∑ r ∈ Finset.range (l - 1), if p ^ (r + 1) ∣ x then 1 else 0 := by
      rw [Finset.card_filter]

/-- Legendre's formula, truncated to the first `l-1` prime-power layers. -/
private lemma factorization_factorial_ge_sum_range_div_pow
    (k p l : ℕ) (hp : p.Prime) :
    (∑ r ∈ Finset.range (l - 1), k / p ^ (r + 1)) ≤ (k !).factorization p := by
  classical
  have hsum_eq :
      (∑ r ∈ Finset.range (l - 1), k / p ^ (r + 1)) =
        ∑ i ∈ Finset.Ico 1 l, k / p ^ i := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun r _hr => ?_)
    rw [Nat.add_comm]
  rw [hsum_eq]
  let b := max l (Nat.log p k + 1)
  have hlog : Nat.log p k < b := by
    dsimp [b]
    omega
  have hfac : (k !).factorization p = ∑ i ∈ Finset.Ico 1 b, k / p ^ i :=
    Nat.factorization_factorial hp hlog
  rw [hfac]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    rw [Finset.mem_Ico] at hi ⊢
    dsimp [b]
    omega
  · intro i _hi _hnot
    exact Nat.zero_le _

/-- If two naturals are congruent modulo `l`, and the first is within `l-1`
above the second, then it is not above it at all. -/
private lemma le_of_mod_eq_of_le_add_pred {x y l : ℕ} (hl : 0 < l)
    (hmod : x % l = y % l) (hle : x ≤ y + (l - 1)) : x ≤ y := by
  by_contra hnot
  have hyx : y < x := lt_of_not_ge hnot
  have hmodEq : y ≡ x [MOD l] := by
    exact hmod.symm
  have hdvd : l ∣ x - y := (Nat.modEq_iff_dvd' hyx.le).mp hmodEq
  have hdiff_pos : 0 < x - y := Nat.sub_pos_of_lt hyx
  have hdiff_ge_l : l ≤ x - y := Nat.le_of_dvd hdiff_pos hdvd
  omega

/-! ### Erdős divisibility step (general l) -/



/-! ### Erdős divisibility step (l = 2 case): discharge of `hprod_l2` -/







/-! ### Main theorem assembly -/




end Tier1

end ProofsInTheBook.Chapter03

open Nat
open ProofsInTheBook.Chapter03

theorem solution
    {n k l m : ℕ} (_hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 2 ≤ l)
    (h_eq : n.choose k = m ^ l) :
    (∏ j ∈ Finset.range k, lPowerFreePart l (n - j)) ∣ k ! := by
  classical
  set P : ℕ := ∏ j ∈ Finset.range k, lPowerFreePart l (n - j) with hP_def
  have hl_pos : 0 < l := by omega
  have h_njne : ∀ j ∈ Finset.range k, (n - j) ≠ 0 := fun j hj => by
    have : j < k := Finset.mem_range.mp hj
    omega
  have h_factor_ne : ∀ j ∈ Finset.range k, lPowerFreePart l (n - j) ≠ 0 := by
    intro j hj
    exact lPowerFreePart_ne_zero (l := l) (m := n - j) (h_njne j hj)
  have hP_ne : P ≠ 0 := by
    rw [hP_def, Finset.prod_ne_zero_iff]
    exact h_factor_ne
  have hkfact_ne : (k ! : ℕ) ≠ 0 := Nat.factorial_ne_zero k
  rw [← Nat.factorization_le_iff_dvd hP_ne hkfact_ne, Finsupp.le_def]
  intro p
  by_cases hp_prime : p.Prime
  · have hP_factor :
        P.factorization p =
          ∑ j ∈ Finset.range k, (n - j).factorization p % l := by
      rw [hP_def, Nat.factorization_prod_apply h_factor_ne]
      refine Finset.sum_congr rfl (fun j _hj => ?_)
      exact lPowerFreePart_factorization_eq_mod_general l (n - j) p
    have h_upper : P.factorization p ≤ (k !).factorization p + (l - 1) := by
      have h_count_bound :
          P.factorization p ≤ ∑ r ∈ Finset.range (l - 1), (k / p ^ (r + 1) + 1) := by
        rw [hP_factor]
        calc
          ∑ j ∈ Finset.range k, (n - j).factorization p % l
              ≤ ∑ j ∈ Finset.range k,
                  ∑ r ∈ Finset.range (l - 1), if p ^ (r + 1) ∣ (n - j) then 1 else 0 := by
                apply Finset.sum_le_sum
                intro j hj
                exact factorization_mod_le_count_pow_dvd hp_prime (h_njne j hj) hl_pos
          _ = ∑ r ∈ Finset.range (l - 1),
                  ∑ j ∈ Finset.range k, if p ^ (r + 1) ∣ (n - j) then 1 else 0 := by
                rw [Finset.sum_comm]
          _ ≤ ∑ r ∈ Finset.range (l - 1), (k / p ^ (r + 1) + 1) := by
                apply Finset.sum_le_sum
                intro r _hr
                rw [← Finset.card_filter]
                exact card_filter_dvd_le_aux
                  (by exact Nat.succ_le_of_lt (pow_pos hp_prime.pos (r + 1)))
                  (by omega : k ≤ n)
      have hsplit :
          (∑ r ∈ Finset.range (l - 1), (k / p ^ (r + 1) + 1)) =
            (∑ r ∈ Finset.range (l - 1), k / p ^ (r + 1)) + (l - 1) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, smul_eq_mul]
      have hleg := factorization_factorial_ge_sum_range_div_pow k p l hp_prime
      rw [hsplit] at h_count_bound
      exact h_count_bound.trans (Nat.add_le_add_right hleg (l - 1))
    have h_mod : P.factorization p % l = (k !).factorization p % l := by
      set Q : ℕ := ∏ j ∈ Finset.range k, lPowerRoot l (n - j) with hQ_def
      have h_desc_split : n.descFactorial k = P * Q ^ l := by
        rw [hP_def, hQ_def, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
            Nat.descFactorial_eq_prod_range]
        refine Finset.prod_congr rfl (fun j hj => ?_)
        exact self_eq_lPowerFreePart_mul_lPowerRoot_pow l (n - j) (h_njne j hj)
      have h_desc_choose : n.descFactorial k = k ! * m ^ l := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, h_eq]
      have hQ_ne : Q ≠ 0 := by
        rw [hQ_def, Finset.prod_ne_zero_iff]
        intro j hj
        exact lPowerRoot_ne_zero (l := l) hl_pos (h_njne j hj)
      have hm_ne : m ≠ 0 := by
        intro hz
        rw [hz, zero_pow hl_pos.ne'] at h_eq
        have h_choose_pos : 0 < n.choose k := Nat.choose_pos (by omega : k ≤ n)
        omega
      have h_eq_PQ : P * Q ^ l = k ! * m ^ l := by
        rw [show P * Q ^ l = n.descFactorial k from h_desc_split.symm]
        exact h_desc_choose
      have h_apply : (P * Q ^ l).factorization p = (k ! * m ^ l).factorization p :=
        congrArg (fun n => n.factorization p) h_eq_PQ
      rw [Nat.factorization_mul hP_ne (pow_ne_zero l hQ_ne),
          Nat.factorization_mul hkfact_ne (pow_ne_zero l hm_ne),
          Nat.factorization_pow, Nat.factorization_pow] at h_apply
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h_apply
      have h_apply_mod := congrArg (fun x : ℕ => x % l) h_apply
      simpa [Nat.add_mul_mod_self_left] using h_apply_mod
    exact le_of_mod_eq_of_le_add_pred hl_pos h_mod h_upper
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime,
        Nat.factorization_eq_zero_of_not_prime _ hp_prime]
