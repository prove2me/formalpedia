-- Prove2me | solution 1 for SubspaceCounting.card_submodule_eq_sum_gaussBinom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:00:29.033096+00:00
-- url     : https://prove2.me/submissions/ac7255bb-424c-4379-9322-34abb3cc38a8

-- Sol generated from NumberTheory/SubspaceCounting.lean
import Mathlib
import Definitions.Def_NumberTheory_SubspaceCounting
import Theorems.Thm_SubspaceCounting_card_span_fiber
/-
# Counting the subspaces of a finite-dimensional vector space over a finite field

This file proves the classical Gaussian (`q`-binomial) count of subspaces of a finite vector
space, in the form needed for the elementary abelian case of the Hilbert class field descent
picture of `Catalog/NumberTheory/HilbertClassFieldDescent.lean`.

Let `K` be a finite field with `q` elements and `V` a finite `K`-vector space of dimension `n`.

* `gaussBinom q n k` : the Gaussian binomial coefficient
  `∏_{i<k}(q^n - q^i) / ∏_{i<k}(q^k - q^i)`;
* `card_linearIndependent_eq_mul` : linearly independent `k`-tuples of `V` are fibred over the
  `k`-dimensional subspaces, each fibre being the set of bases of that subspace;
* `card_submodule_finrank_mul` : `#{W : dim W = k} * ∏_{i<k}(q^k - q^i) = ∏_{i<k}(q^n - q^i)`;
* `card_submodule_finrank_eq_gaussBinom` : `#{W : dim W = k} = gaussBinom q n k`;
* `card_submodule_eq_sum_gaussBinom` : `#(subspaces of V) = ∑_{k≤n} gaussBinom q n k`;
* `gaussBinom_symm` : `gaussBinom q n k = gaussBinom q n (n - k)` for `k ≤ n`, proved through the
  duality bijection between `k`- and `(n-k)`-dimensional subspaces;
* the specialisations to `V = (ZMod p)^r` used by the class field application.
-/


open Module Finset

open SubspaceCounting




/-- The denominator in the Gaussian binomial coefficient is positive. -/
theorem prod_pos_of_one_lt {q k : ℕ} (hq : 1 < q) :
    0 < ∏ i ∈ Finset.range k, (q ^ k - q ^ i) := by
  refine Finset.prod_pos fun i hi => ?_
  have : q ^ i < q ^ k := Nat.pow_lt_pow_right hq (Finset.mem_range.mp hi)
  omega


variable (K V : Type*) [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]






/-- **Fibration count.**  The number of linearly independent `k`-tuples of `V` is the number of
`k`-dimensional subspaces times the number of bases of each. -/
theorem card_linearIndependent_eq_mul (k : ℕ) :
    Nat.card {s : Fin k → V // LinearIndependent K s}
      = Nat.card {W : Submodule K V // finrank K W = k}
        * ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) := by
  classical
  haveI : Fintype {W : Submodule K V // finrank K W = k} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanOfLinearIndependent K V k)), Nat.card_sigma]
  simp only [card_span_fiber K V]
  rw [Finset.sum_const, smul_eq_mul, ← Nat.card_eq_fintype_card]
  simp [Nat.card_eq_fintype_card]

/-- **The subspace count, in product form.** -/
theorem card_submodule_finrank_mul {k : ℕ} (hk : k ≤ finrank K V) :
    Nat.card {W : Submodule K V // finrank K W = k}
        * ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ))
      = ∏ i : Fin k, (Fintype.card K ^ finrank K V - Fintype.card K ^ (i : ℕ)) := by
  rw [← card_linearIndependent_eq_mul K V k, card_linearIndependent (K := K) (V := V) hk]

/-- **The subspace count.**  A finite `K`-vector space of dimension `n` has exactly
`gaussBinom q n k` subspaces of dimension `k`, for every `k ≤ n`. -/
theorem card_submodule_finrank_eq_gaussBinom {k : ℕ} (hk : k ≤ finrank K V) :
    Nat.card {W : Submodule K V // finrank K W = k}
      = gaussBinom (Fintype.card K) (finrank K V) k := by
  have h := card_submodule_finrank_mul K V hk
  have hD : 0 < ∏ i ∈ Finset.range k, (Fintype.card K ^ k - Fintype.card K ^ i) :=
    prod_pos_of_one_lt Fintype.one_lt_card
  rw [gaussBinom,
    ← Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ finrank K V - Fintype.card K ^ i) k,
    ← Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ k - Fintype.card K ^ i) k]
  rw [← Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ k - Fintype.card K ^ i) k] at hD
  exact (Nat.div_eq_of_eq_mul_left hD h.symm).symm








variable (p r : ℕ) [Fact p.Prime]







/-! ## Explicit small values -/





open SubspaceCounting in
theorem solution:
    Nat.card (Submodule K V)
      = ∑ k ∈ Finset.range (finrank K V + 1), gaussBinom (Fintype.card K) (finrank K V) k := by
  classical
  set n := finrank K V with hn
  let f : Submodule K V → Fin (n + 1) := fun W => ⟨finrank K W, by
    have := Submodule.finrank_le W; omega⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  have hfib : ∀ j : Fin (n + 1),
      Nat.card {W : Submodule K V // f W = j} = gaussBinom (Fintype.card K) n (j : ℕ) := by
    intro j
    have e : {W : Submodule K V // f W = j} ≃ {W : Submodule K V // finrank K W = (j : ℕ)} :=
      Equiv.subtypeEquivRight fun W => by
        constructor
        · intro h; exact congrArg Fin.val h
        · intro h; exact Fin.ext h
    rw [Nat.card_congr e, card_submodule_finrank_eq_gaussBinom K V (by omega : (j : ℕ) ≤ n)]
  rw [Finset.sum_congr rfl fun j _ => hfib j]
  exact Fin.sum_univ_eq_sum_range (fun k => gaussBinom (Fintype.card K) n k) (n + 1)
