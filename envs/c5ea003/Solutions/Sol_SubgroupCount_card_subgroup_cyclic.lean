-- Prove2me | solution 1 for SubgroupCount.card_subgroup_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:04:00.962557+00:00
-- url     : https://prove2.me/submissions/8c3cc6be-7460-40c3-927a-1d6cf7b93da7

-- Sol generated from Algebra/SubgroupCountFiniteAbelian.lean
import Mathlib
import Definitions.Def_Algebra_SubgroupCountFiniteAbelian
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












/-! ## Cyclic groups: the divisor count -/


variable {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]

/-- In a finite cyclic group there is a subgroup of each order dividing the order of the group. -/
theorem exists_subgroup_card_eq {d : ℕ} (hd : d ∣ Nat.card G) :
    ∃ K : Subgroup G, Nat.card K = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  refine ⟨Subgroup.zpowers (g ^ (Nat.card G / d)), ?_⟩
  rw [Nat.card_zpowers, orderOf_pow, hg]
  have hdvd : Nat.card G / d ∣ Nat.card G := Nat.div_dvd_of_dvd hd
  have hpos : 0 < Nat.card G := Nat.card_pos
  rw [Nat.gcd_eq_right hdvd, Nat.div_div_self hd (by omega)]

/-- In a finite cyclic group, the subgroup of order `d` (for `d` dividing the order) is the group
of `d`-th roots of unity; in particular a subgroup is determined by its order. -/
theorem eq_ker_powMonoidHom_of_card_eq {d : ℕ} {L : Subgroup G} (hL : Nat.card L = d) :
    L = (powMonoidHom d : G →* G).ker := by
  have hdvd : d ∣ Nat.card G := hL ▸ Subgroup.card_subgroup_dvd_card L
  have hker : Nat.card (powMonoidHom d : G →* G).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdvd]
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hker, hL])
  intro x hx
  have h : ((⟨x, hx⟩ : L)) ^ Nat.card L = 1 := pow_card_eq_one'
  have hx' : x ^ d = 1 := by
    have := congrArg (Subtype.val) h
    simpa [hL] using this
  simpa [MonoidHom.mem_ker, powMonoidHom] using hx'

/-- In a finite cyclic group a subgroup is determined by its order. -/
theorem subgroup_injective_card {K K' : Subgroup G} (h : Nat.card K = Nat.card K') :
    K = K' := by
  rw [eq_ker_powMonoidHom_of_card_eq (L := K) rfl,
    eq_ker_powMonoidHom_of_card_eq (L := K') h.symm]



/-! ## Elementary abelian groups of rank two -/








/-! ## Cyclic versus elementary abelian at order `p²` -/





/-! ## The falsifiable contrast at order four

Two abelian groups of the same order `4` with different subgroup counts: the cyclic group has
`3` subgroups, the Klein four group has `5`.  Consequently the number of intermediate fields of a
Hilbert class field is *not* determined by the class number. -/








open SubgroupCount in
theorem solution:
    Nat.card (Subgroup G) = (Nat.card G).divisors.card := by
  classical
  have hn : 0 < Nat.card G := Nat.card_pos
  let F : Subgroup G → {d : ℕ // d ∈ (Nat.card G).divisors} := fun K =>
    ⟨Nat.card K, by
      rw [Nat.mem_divisors]
      exact ⟨Subgroup.card_subgroup_dvd_card K, by omega⟩⟩
  have hinj : Function.Injective F := by
    intro K K' h
    have h2 : Nat.card K = Nat.card K' := congrArg Subtype.val h
    exact subgroup_injective_card h2
  have hsurj : Function.Surjective F := by
    rintro ⟨d, hd⟩
    obtain ⟨K, hK⟩ := exists_subgroup_card_eq (G := G) (Nat.mem_divisors.mp hd).1
    exact ⟨K, Subtype.ext hK⟩
  rw [Nat.card_eq_of_bijective F ⟨hinj, hsurj⟩, Nat.card_eq_finsetCard]
