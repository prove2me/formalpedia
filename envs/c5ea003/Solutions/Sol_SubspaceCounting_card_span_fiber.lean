-- Prove2me | solution 1 for SubspaceCounting.card_span_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:58:45.453835+00:00
-- url     : https://prove2.me/submissions/6e447c52-4410-49ed-9cc5-67418bdcf1b5

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


/-- The bases of a `k`-dimensional subspace: the number of linearly independent `k`-tuples in a
subspace of dimension `k` is `∏_{i<k}(q^k - q^i)`. -/
theorem card_linearIndependent_of_finrank_eq {k : ℕ} (W : Submodule K V)
    (hW : finrank K W = k) :
    Nat.card {s : Fin k → W // LinearIndependent K s}
      = ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) := by
  have h := card_linearIndependent (K := K) (V := W) (k := k) (le_of_eq hW.symm)
  rwa [hW] at h














variable (p r : ℕ) [Fact p.Prime]







/-! ## Explicit small values -/





open SubspaceCounting in
theorem solution{k : ℕ} (W : {W : Submodule K V // finrank K W = k}) :
    Nat.card {s : {s : Fin k → V // LinearIndependent K s} //
        spanOfLinearIndependent K V k s = W}
      = ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ (i : ℕ)) := by
  have e₁ : {s : {s : Fin k → V // LinearIndependent K s} //
        spanOfLinearIndependent K V k s = W} ≃
      {s : Fin k → V // LinearIndependent K s ∧ Submodule.span K (Set.range s) = W.1} :=
    (Equiv.subtypeEquivRight (p := fun s : {s : Fin k → V // LinearIndependent K s} =>
        spanOfLinearIndependent K V k s = W)
        (q := fun s => Submodule.span K (Set.range s.1) = W.1)
        (fun _ => Subtype.ext_iff)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun s : Fin k → V => LinearIndependent K s)
        (fun s => Submodule.span K (Set.range s) = W.1))
  rw [Nat.card_congr (e₁.trans (spanFiberEquiv K V W.1 W.2)),
    card_linearIndependent_of_finrank_eq K V W.1 W.2]
