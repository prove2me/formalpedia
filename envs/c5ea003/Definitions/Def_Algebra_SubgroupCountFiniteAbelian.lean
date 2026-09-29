-- Prove2me | Definitions.Def_Algebra_SubgroupCountFiniteAbelian
-- name    : Algebra_SubgroupCountFiniteAbelian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:14:07.46764+00:00
-- url     : https://prove2.me/theorems/a48c3219-aa9b-4cdc-8cdc-8bc6483d2937
-- title:
--   Aether Catalog definitions — Algebra_SubgroupCountFiniteAbelian
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.SubgroupCountFiniteAbelian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/SubgroupCountFiniteAbelian.lean by skeleton subtraction
import Mathlib
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

namespace SubgroupCount

instance finite_subgroup (G : Type*) [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective

/-! ## Multiplicativity over a coprime product -/

section Product

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- If a power `x ^ n` of `x` with `n` coprime to the order of `x` lies in a subgroup, so does
`x` itself. -/
theorem mem_of_pow_mem_of_coprime {A : Type*} [Group A] [Finite A] {K : Subgroup A} {x : A}
    {n : ℕ} (hcop : (orderOf x).Coprime n) (h : x ^ n ∈ K) : x ∈ K := by
  have hle : Subgroup.zpowers (x ^ n) ≤ Subgroup.zpowers x := by
    rw [Subgroup.zpowers_le]
    exact pow_mem (Subgroup.mem_zpowers x) n
  have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers (x ^ n)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow, hcop, Nat.div_one]
  have heq : Subgroup.zpowers (x ^ n) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have : x ∈ Subgroup.zpowers (x ^ n) := by rw [heq]; exact Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.mpr h) this

/-- **Splitting the first coordinate.**  If the orders of `G` and `H` are coprime, then a
subgroup of `G × H` containing `(a, b)` contains `(a, 1)`. -/
theorem mk_one_mem_of_coprime (hco : (Nat.card G).Coprime (Nat.card H))
    {K : Subgroup (G × H)} {a : G} {b : H} (h : (a, b) ∈ K) : ((a, 1) : G × H) ∈ K := by
  set n := Nat.card H with hn
  have hb : b ^ n = 1 := pow_card_eq_one'
  have hpow : ((a, b) : G × H) ^ n = ((a ^ n, 1) : G × H) := by
    rw [Prod.pow_mk, hb]
  have hmem : ((a ^ n, 1) : G × H) ∈ K := by rw [← hpow]; exact pow_mem h n
  have hx : ((a, 1) : G × H) ^ n = ((a ^ n, 1) : G × H) := by rw [Prod.pow_mk, one_pow]
  refine mem_of_pow_mem_of_coprime (x := ((a, 1) : G × H)) ?_ (by rw [hx]; exact hmem)
  have hdvd : orderOf ((a, 1) : G × H) ∣ Nat.card G := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [Prod.pow_mk, one_pow, pow_card_eq_one']
    rfl
  exact Nat.Coprime.coprime_dvd_left hdvd hco

/-- **Splitting the second coordinate.** -/
theorem one_mk_mem_of_coprime (hco : (Nat.card G).Coprime (Nat.card H))
    {K : Subgroup (G × H)} {a : G} {b : H} (h : (a, b) ∈ K) : ((1, b) : G × H) ∈ K := by
  set m := Nat.card G with hm
  have ha : a ^ m = 1 := pow_card_eq_one'
  have hpow : ((a, b) : G × H) ^ m = ((1, b ^ m) : G × H) := by
    rw [Prod.pow_mk, ha]
  have hmem : ((1, b ^ m) : G × H) ∈ K := by rw [← hpow]; exact pow_mem h m
  have hx : ((1, b) : G × H) ^ m = ((1, b ^ m) : G × H) := by rw [Prod.pow_mk, one_pow]
  refine mem_of_pow_mem_of_coprime (x := ((1, b) : G × H)) ?_ (by rw [hx]; exact hmem)
  have hdvd : orderOf ((1, b) : G × H) ∣ Nat.card H := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [Prod.pow_mk, one_pow, pow_card_eq_one']
    rfl
  exact Nat.Coprime.coprime_dvd_left hdvd hco.symm

/-- **Every subgroup of a coprime product is a product of subgroups.** -/
theorem eq_prod_of_coprime (hco : (Nat.card G).Coprime (Nat.card H)) (K : Subgroup (G × H)) :
    K = (K.map (MonoidHom.fst G H)).prod (K.map (MonoidHom.snd G H)) := by
  ext x
  obtain ⟨a, b⟩ := x
  constructor
  · intro h
    exact ⟨⟨(a, b), h, rfl⟩, ⟨(a, b), h, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨⟨a₁, b₁⟩, hab₁, rfl⟩ := h1
    obtain ⟨⟨a₂, b₂⟩, hab₂, rfl⟩ := h2
    have hA : ((a₁, 1) : G × H) ∈ K := mk_one_mem_of_coprime hco hab₁
    have hB : ((1, b₂) : G × H) ∈ K := one_mk_mem_of_coprime hco hab₂
    have : ((a₁, 1) : G × H) * (1, b₂) ∈ K := mul_mem hA hB
    simpa [Prod.ext_iff] using this

omit [Finite G] [Finite H] in
theorem map_fst_prod (A : Subgroup G) (B : Subgroup H) :
    (A.prod B).map (MonoidHom.fst G H) = A := by
  ext a
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, _⟩, rfl⟩; exact hx
  · intro ha; exact ⟨(a, 1), ⟨ha, one_mem B⟩, rfl⟩

omit [Finite G] [Finite H] in
theorem map_snd_prod (A : Subgroup G) (B : Subgroup H) :
    (A.prod B).map (MonoidHom.snd G H) = B := by
  ext b
  constructor
  · rintro ⟨⟨x, y⟩, ⟨_, hy⟩, rfl⟩; exact hy
  · intro hb; exact ⟨(1, b), ⟨one_mem A, hb⟩, rfl⟩

/-- **The subgroup lattice of a coprime product splits.** -/
def subgroupProdOrderIsoOfCoprime (hco : (Nat.card G).Coprime (Nat.card H)) :
    Subgroup (G × H) ≃o Subgroup G × Subgroup H where
  toFun K := (K.map (MonoidHom.fst G H), K.map (MonoidHom.snd G H))
  invFun AB := AB.1.prod AB.2
  left_inv K := (eq_prod_of_coprime hco K).symm
  right_inv AB := by
    obtain ⟨A, B⟩ := AB
    simp [map_fst_prod, map_snd_prod]
  map_rel_iff' := by
    intro K K'
    constructor
    · rintro ⟨h1, h2⟩
      rw [eq_prod_of_coprime hco K, eq_prod_of_coprime hco K']
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact ⟨h1 ha, h2 hb⟩
    · intro h
      exact ⟨Subgroup.map_mono h, Subgroup.map_mono h⟩


end Product

/-! ## Cyclic groups: the divisor count -/

section Cyclic

variable {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]





end Cyclic

/-! ## Elementary abelian groups of rank two -/

section Elementary

variable {G : Type*} [Group G] [Finite G] {p : ℕ}





end Elementary

/-! ## Cyclic versus elementary abelian at order `p²` -/

section Contrast



end Contrast

/-! ## The falsifiable contrast at order four

Two abelian groups of the same order `4` with different subgroup counts: the cyclic group has
`3` subgroups, the Klein four group has `5`.  Consequently the number of intermediate fields of a
Hilbert class field is *not* determined by the class number. -/

section Examples





end Examples

end SubgroupCount


