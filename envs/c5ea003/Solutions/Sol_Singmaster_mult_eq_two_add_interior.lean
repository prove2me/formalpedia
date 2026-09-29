-- Prove2me | solution 1 for Singmaster.mult_eq_two_add_interior
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:54:47.623522+00:00
-- url     : https://prove2.me/submissions/fa08219e-68b9-49aa-aa4c-3541437dbd1e

-- Sol generated from Combinatorics/SingmasterExactCounts.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Theorems.Thm_Singmaster_choose_eq_iff_descFactorial
import Theorems.Thm_Singmaster_choose_lt_choose_left
import Theorems.Thm_Singmaster_choose_two_le_choose
import Theorems.Thm_Singmaster_mem_occ
import Theorems.Thm_Singmaster_mem_occ_iff
/-
# Exact multiplicities: a certified finite algorithm, and `N(3003) = 8`

Fifth research cycle.  The earlier files bound or reduce the multiplicity function
`N(t) = Singmaster.mult t`; this file turns the structure theory into a *certified
decision procedure* for a single value of `t`, and runs it.

## The algorithm

Every occurrence of `t ≥ 3` is either one of the two boundary occurrences `(t,1)`,
`(t,t-1)`, or an **interior** one, i.e. `C(n,k) = t` with `2 ≤ k ≤ n - 2`.  An interior
occurrence satisfies `C(n,2) ≤ C(n,k) = t` (`Singmaster.choose_two_le_choose`), so its
row is capped by any `N` with `t < C(N,2)`; that is, by roughly `√(2t)`.  Hence

`N(t) = 2 + #{(n,k) : n,k < N, 2 ≤ k ≤ n-2, C(n,k) = t}`,

a search over an explicitly bounded box (`Singmaster.mult_eq_two_add_interior`).  As in
`Combinatorics.SingmasterCentralBinomial` the test `C(n,k) = t` is carried out through
`Nat.descFactorial` (`Singmaster.choose_eq_iff_descFactorial`), which costs `k`
multiplications instead of `C(n,k)` additions and is what makes kernel evaluation
possible.

## Results

* `Singmaster.mult_eq_two_add_interior` — the certified algorithm;
* `Singmaster.mult_eq_two_of_no_interior` — the "only the two trivial occurrences" case;
* `Singmaster.mult_3003` — **`3003` occurs exactly eight times**, upgrading
  `Singmaster.eight_le_mult_3003` from a lower bound to an equality.  This is the
  specimen singled out in Singmaster's problem;
* `Singmaster.mult_120`, `mult_210`, `mult_1540`, `mult_7140`, `mult_11628` — the other
  small numbers of multiplicity six: each occurs **exactly** six times.

Together with `Combinatorics.SingmasterCentralBinomial` this makes every multiplicity
claim in the classical folklore list machine-checked, except for the asymptotic ones.
-/

open Finset

open Singmaster

/-! ## Binomial coefficients through descending factorials -/


/-! ## The interior occurrences -/


theorem mem_interiorOcc {t N n k : ℕ} :
    (n, k) ∈ interiorOcc t N ↔ (n < N ∧ k < N) ∧ 2 ≤ k ∧ k + 2 ≤ n ∧ n.choose k = t := by
  simp only [interiorOcc, mem_filter, mem_product, mem_range, choose_eq_iff_descFactorial]

/-! ## The certified algorithm -/



/-! ## Running the algorithm

Each of the following is an honest finite search: for `t = 3003` the box is
`79 × 79` and the six interior occurrences found are `(78,2)`, `(78,76)`, `(15,5)`,
`(15,10)`, `(14,6)`, `(14,8)`. -/









open Singmaster in
theorem solution{t N : ℕ} (ht : 3 ≤ t) (hN2 : 2 ≤ N)
    (hN : t < N.choose 2) : mult t = 2 + (interiorOcc t N).card := by
  classical
  have ht2 : 2 ≤ t := by omega
  have hbnd : ({(t, 1), (t, t - 1)} : Finset (ℕ × ℕ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), card_singleton]
  have hdisj : Disjoint ({(t, 1), (t, t - 1)} : Finset (ℕ × ℕ)) (interiorOcc t N) := by
    rw [Finset.disjoint_left]
    rintro ⟨n, k⟩ h1 h2
    rw [mem_interiorOcc] at h2
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h1
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  have hunion : occ t = ({(t, 1), (t, t - 1)} : Finset (ℕ × ℕ)) ∪ interiorOcc t N := by
    ext ⟨n, k⟩
    constructor
    · intro hp
      rw [mem_occ_iff ht2] at hp
      obtain ⟨hk, hck⟩ := hp
      simp only [mem_union, mem_insert, mem_singleton, Prod.mk.injEq, mem_interiorOcc]
      by_cases hk0 : k = 0
      · subst hk0; rw [Nat.choose_zero_right] at hck; omega
      by_cases hkn : k = n
      · subst hkn; rw [Nat.choose_self] at hck; omega
      by_cases hk1 : k = 1
      · subst hk1; rw [Nat.choose_one_right] at hck; exact Or.inl (Or.inl ⟨hck, rfl⟩)
      by_cases hkn1 : k = n - 1
      · subst hkn1
        have hs := Nat.choose_symm (n := n) (k := 1) (by omega)
        rw [Nat.choose_one_right] at hs
        rw [hs] at hck
        exact Or.inl (Or.inr ⟨hck, by omega⟩)
      have hk2 : 2 ≤ k := by omega
      have hkk : k + 2 ≤ n := by omega
      have hc2 : n.choose 2 ≤ t := by rw [← hck]; exact choose_two_le_choose hk2 hkk
      have hnN : n < N := by
        by_contra hcon
        push_neg at hcon
        have hmono : N.choose 2 ≤ n.choose 2 := by
          rcases eq_or_lt_of_le hcon with heq | hlt
          · rw [heq]
          · exact le_of_lt (choose_lt_choose_left (by norm_num) hN2 hlt)
        omega
      exact Or.inr ⟨⟨hnN, by omega⟩, hk2, hkk, hck⟩
    · intro hp
      rw [mem_union] at hp
      rcases hp with hp | hp
      · simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact mem_occ ht2 (by omega) (Nat.choose_one_right _)
        · refine mem_occ ht2 (by omega) ?_
          have hs := Nat.choose_symm (n := n) (k := 1) (by omega)
          rw [Nat.choose_one_right] at hs
          exact hs
      · rw [mem_interiorOcc] at hp
        exact mem_occ ht2 (by omega) hp.2.2.2
  rw [mult, hunion, Finset.card_union_of_disjoint hdisj, hbnd]
