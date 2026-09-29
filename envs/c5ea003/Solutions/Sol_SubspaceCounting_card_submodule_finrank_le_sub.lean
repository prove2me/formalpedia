-- Prove2me | solution 1 for SubspaceCounting.card_submodule_finrank_le_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:00:29.843134+00:00
-- url     : https://prove2.me/submissions/d54480c6-3dcb-487e-a4a8-12f764622eef

-- Sol generated from NumberTheory/SubspaceCounting.lean
import Mathlib
import Definitions.Def_NumberTheory_SubspaceCounting
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






variable (K V : Type*) [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]
















variable (p r : ℕ) [Fact p.Prime]







/-! ## Explicit small values -/





open SubspaceCounting in
omit [Fintype K] in
theorem solution(k : ℕ) :
    Nat.card {W : Submodule K V // finrank K W = k}
      ≤ Nat.card {W : Submodule K V // finrank K W = finrank K V - k} := by
  classical
  haveI : FiniteDimensional K V := Module.Finite.of_finite
  let b := Module.finBasis K V
  let E : Dual K V ≃ₗ[K] V := (b.toDualEquiv).symm
  have hinj : Function.Injective
      (fun W : {W : Submodule K V // finrank K W = k} =>
        (⟨Submodule.map (E : Dual K V →ₗ[K] V) W.1.dualAnnihilator, by
          rw [LinearEquiv.finrank_map_eq E W.1.dualAnnihilator]
          have h1 := Submodule.finrank_quotient_add_finrank W.1
          have h2 := (Subspace.quotEquivAnnihilator W.1).finrank_eq
          rw [W.2] at h1
          omega⟩ : {W : Submodule K V // finrank K W = finrank K V - k})) := by
    intro W1 W2 h
    simp only [Subtype.mk.injEq] at h
    have hE : Function.Injective (Submodule.map (E : Dual K V →ₗ[K] V)) :=
      Submodule.map_injective_of_injective E.injective
    exact Subtype.ext (Subspace.dualAnnihilator_inj.mp (hE h))
  exact Nat.card_le_card_of_injective _ hinj
