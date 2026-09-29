-- Prove2me | Definitions.Def_NumberTheory_SubspaceCounting
-- name    : NumberTheory_SubspaceCounting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:17.595162+00:00
-- url     : https://prove2.me/theorems/578c8b19-9881-431d-a49e-fc290d9d364d
-- title:
--   Aether Catalog definitions — NumberTheory_SubspaceCounting
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.SubspaceCounting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/SubspaceCounting.lean by skeleton subtraction
import Mathlib
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

namespace SubspaceCounting

/-- The Gaussian (`q`-)binomial coefficient `binom(n,k)_q`, defined as the exact quotient
`∏_{i<k}(q^n - q^i) / ∏_{i<k}(q^k - q^i)`. -/
def gaussBinom (q n k : ℕ) : ℕ :=
  (∏ i ∈ Finset.range k, (q ^ n - q ^ i)) / (∏ i ∈ Finset.range k, (q ^ k - q ^ i))




section Field

variable (K V : Type*) [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

instance finite_submodule : Finite (Submodule K V) :=
  Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective


/-- The span of a linearly independent `k`-tuple, as a `k`-dimensional subspace. -/
def spanOfLinearIndependent (k : ℕ) (s : {s : Fin k → V // LinearIndependent K s}) :
    {W : Submodule K V // finrank K W = k} :=
  ⟨Submodule.span K (Set.range s.1), by rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩

/-- The linearly independent `k`-tuples spanning a fixed `k`-dimensional subspace `W` are exactly
the bases of `W`. -/
def spanFiberEquiv {k : ℕ} (W : Submodule K V) (hW : finrank K W = k) :
    {s : Fin k → V // LinearIndependent K s ∧ Submodule.span K (Set.range s) = W} ≃
      {t : Fin k → W // LinearIndependent K t} where
  toFun s :=
    ⟨fun i => ⟨s.1 i, by
        have h := Submodule.subset_span (R := K) (s := Set.range s.1) ⟨i, rfl⟩
        rw [s.2.2] at h; exact h⟩,
      LinearIndependent.of_comp W.subtype (by simpa using s.2.1)⟩
  invFun t :=
    ⟨fun i => (t.1 i : V), t.2.map' W.subtype (Submodule.ker_subtype W), by
      have htop : Submodule.span K (Set.range t.1) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card t.2, Fintype.card_fin, hW])
      have hcomp : (fun i => (t.1 i : V)) = W.subtype ∘ t.1 := rfl
      rw [hcomp, Set.range_comp, ← Submodule.map_span, htop, Submodule.map_top,
        Submodule.range_subtype]⟩
  left_inv s := by ext i; rfl
  right_inv t := by ext i; rfl










end Field

section ZMod

variable (p r : ℕ) [Fact p.Prime]






end ZMod

/-! ## Explicit small values -/




end SubspaceCounting


