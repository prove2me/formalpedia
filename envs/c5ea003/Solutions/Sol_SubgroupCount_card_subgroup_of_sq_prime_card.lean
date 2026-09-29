-- Prove2me | solution 1 for SubgroupCount.card_subgroup_of_sq_prime_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:08:22.744895+00:00
-- url     : https://prove2.me/submissions/6c1d74e4-9c9a-4d71-8269-62b25ac86aff

-- Sol generated from Algebra/SubgroupCountFiniteAbelian.lean
import Mathlib
import Definitions.Def_Algebra_SubgroupCountFiniteAbelian
import Theorems.Thm_SubgroupCount_card_subgroup_card_eq_prime
/-
# Counting the subgroups of a finite group

This file settles the group-theoretic half of target 1 of the previous research cycle of the
conditional Hilbert class field thread.  By
`HilbertClassFieldDescent.card_intermediateField_eq_card_subgroup`, the number of intermediate
fields of a Hilbert class field `H/K` is the number of subgroups of the class group, so the
arithmetic question "how many intermediate fields?" becomes the group-theoretic question
"how many subgroups?".  The previous cycle answered it for elementary abelian class groups
`(ℤ/p)^r` (the Galois `p`-binomial count).  Here we prove:

* `Subgroup.eq_prod_of_coprime`, `subgroupProdOrderIsoOfCoprime`,
  `card_subgroup_prod_of_coprime` : **multiplicativity**.  If `Nat.card G` and `Nat.card H` are
  coprime then every subgroup of `G × H` is a product of subgroups, the subgroup lattice of
  `G × H` is the product of the two subgroup lattices, and
  `#Subgroup (G × H) = #Subgroup G * #Subgroup H`.  (No commutativity is needed.)
* `card_subgroup_cyclic` : a finite **cyclic** group of order `n` has exactly `d(n)` subgroups,
  `d` the number-of-divisors function.
* `card_subgroup_of_sq_prime_card` : a group of order `p²` of exponent `p` (`p` prime) has
  exactly `p + 3` subgroups: `⊥`, `⊤` and the `p + 1` "lines".
* `card_subgroup_zmod_four`, `card_subgroup_kleinFour`, `card_subgroup_ne_of_order_four` :
  the falsifiable contrast announced in the previous cycle — `ℤ/4` has `3` subgroups while
  `(ℤ/2)²` has `5`, so **the number of intermediate fields of the Hilbert class field is not a
  function of the class number alone**.

Everything is stated for multiplicative groups; the additive models `ZMod n` are reached through
`Multiplicative`.
-/


open Subgroup

open SubgroupCount


/-! ## Multiplicativity over a coprime product -/


variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]










/-! ## Cyclic groups: the divisor count -/


variable {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]






/-! ## Elementary abelian groups of rank two -/


variable {G : Type*} [Group G] [Finite G] {p : ℕ}






/-! ## Cyclic versus elementary abelian at order `p²` -/





/-! ## The falsifiable contrast at order four

Two abelian groups of the same order `4` with different subgroup counts: the cyclic group has
`3` subgroups, the Klein four group has `5`.  Consequently the number of intermediate fields of a
Hilbert class field is *not* determined by the class number. -/








open SubgroupCount in
theorem solution(hp : p.Prime) (hcard : Nat.card G = p ^ 2)
    (hexp : ∀ x : G, x ^ p = 1) : Nat.card (Subgroup G) = p + 3 := by
  classical
  haveI : Fintype (Subgroup G) := Fintype.ofFinite _
  -- classify a subgroup by its order
  have horder : ∀ K : Subgroup G, Nat.card K = 1 ∨ Nat.card K = p ∨ Nat.card K = p ^ 2 := by
    intro K
    have hdvd : Nat.card K ∣ p ^ 2 := hcard ▸ Subgroup.card_subgroup_dvd_card K
    obtain ⟨i, hi, hK⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases i
    · exact Or.inl (by simpa using hK)
    · exact Or.inr (Or.inl (by simpa using hK))
    · exact Or.inr (Or.inr hK)
  have hp1 : p ≠ 1 := hp.ne_one
  have hp2 : 2 ≤ p := hp.two_le
  have hpsq : p ^ 2 ≠ p := by nlinarith [hp.two_le]
  let f : Subgroup G → Fin 3 := fun K =>
    if Nat.card K = 1 then 0 else if Nat.card K = p then 1 else 2
  have hfib0 : Nat.card {K : Subgroup G // f K = 0} = 1 := by
    have e : {K : Subgroup G // f K = 0} ≃ {K : Subgroup G // K = ⊥} := by
      refine Equiv.subtypeEquivRight fun K => ?_
      simp only [f]
      constructor
      · intro h
        by_cases h1 : Nat.card K = 1
        · exact Subgroup.card_eq_one.mp h1
        · simp only [h1, if_false] at h
          split at h <;> simp at h
      · intro h
        simp [h]
    rw [Nat.card_congr e]
    simp
  have hfib2 : Nat.card {K : Subgroup G // f K = 2} = 1 := by
    have e : {K : Subgroup G // f K = 2} ≃ {K : Subgroup G // K = ⊤} := by
      refine Equiv.subtypeEquivRight fun K => ?_
      simp only [f]
      constructor
      · intro h
        by_cases h1 : Nat.card K = 1
        · simp [h1] at h
        by_cases hpK : Nat.card K = p
        · simp [hpK, hp1] at h
        rcases horder K with h' | h' | h'
        · exact absurd h' h1
        · exact absurd h' hpK
        · rw [← Subgroup.card_eq_iff_eq_top, h', hcard]
      · rintro rfl
        rw [Subgroup.card_top, hcard]
        simp [hp1, hpsq]
    rw [Nat.card_congr e]
    simp
  have hfib1 : Nat.card {K : Subgroup G // f K = 1} = p + 1 := by
    have e : {K : Subgroup G // f K = 1} ≃ {K : Subgroup G // Nat.card K = p} := by
      refine Equiv.subtypeEquivRight fun K => ?_
      simp only [f]
      constructor
      · intro h
        by_cases h1 : Nat.card K = 1
        · simp [h1] at h
        by_cases hpK : Nat.card K = p
        · exact hpK
        · simp [h1, hpK] at h
      · intro h
        have h1 : Nat.card K ≠ 1 := by rw [h]; omega
        simp [h, hp1]
    rw [Nat.card_congr e]
    exact card_subgroup_card_eq_prime hp hcard hexp
  have := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [← this, Nat.card_sigma]
  rw [Fin.sum_univ_three]
  rw [hfib0, hfib1, hfib2]
  omega
