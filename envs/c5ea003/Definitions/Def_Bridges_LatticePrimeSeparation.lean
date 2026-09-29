-- Prove2me | Definitions.Def_Bridges_LatticePrimeSeparation
-- name    : Bridges_LatticePrimeSeparation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:44.135747+00:00
-- url     : https://prove2.me/theorems/08a3cb05-9a52-47cc-b347-3715e2bfa239
-- title:
--   Aether Catalog definitions — Bridges_LatticePrimeSeparation
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LatticePrimeSeparation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LatticePrimeSeparation.lean by skeleton subtraction
import Mathlib
/-
# Constructive Prime Separation in Finite Distributive Lattices

This file establishes the fundamental prime separation theorem for finite
distributive lattices and applies it to finite closure systems.

## Main results

* `exists_infPrime_separation` — prime separation in finite distributive lattices
* `FiniteClosureSystem` — bundled finite closure operator
* `ClosedSet` — the type of closed sets with a lattice structure
* `exists_prime_closedSet_separation` — prime separation for closed sets
* `closedSet_eq_iInter_prime_extensions` — spectral reconstruction theorem
-/


open Set Finset

/-! ## Part I: Abstract Lattice Separation -/

section LatticeSeparation

variable {α : Type*} [DistribLattice α] [OrderTop α] [Fintype α]

/-
**Prime separation theorem for finite distributive lattices.**
If `a ≰ b` in a finite distributive lattice, then there exists an inf-prime
element `p` with `b ≤ p` and `a ≰ p`.
-/
theorem exists_infPrime_separation {a b : α} (h : ¬(a ≤ b)) :
    ∃ p, InfPrime p ∧ b ≤ p ∧ ¬(a ≤ p) := by
  obtain ⟨ s, hs ⟩ := exists_infIrred_decomposition b;
  -- Since `a ≰ b = s.inf id`, there must be some `p ∈ s` with `a ≰ p`.
  obtain ⟨ p, hp_mem, hp_not_le ⟩ : ∃ p ∈ s, ¬a ≤ p := by
    contrapose! h;
    exact hs.1 ▸ Finset.le_inf h;
  exact ⟨ p, by simpa only [ infPrime_iff_infIrred ] using hs.2 hp_mem, hs.1 ▸ Finset.inf_le hp_mem, hp_not_le ⟩

/-
**Spectral reconstruction.**
`a ≤ b` iff every inf-prime above `b` is also above `a`.
-/

end LatticeSeparation

/-! ## Part II: Finite Closure Systems -/

/-- A bundled finite closure operator on a finite decidable type. -/
structure FiniteClosureSystem (α : Type*) [Fintype α] [DecidableEq α] where
  /-- The closure operator -/
  cl : Set α → Set α
  /-- Closure is monotone -/
  mono_cl : Monotone cl
  /-- Every set is contained in its closure -/
  extensive : ∀ s, s ⊆ cl s
  /-- Closure is idempotent -/
  idempotent : ∀ s, cl (cl s) = cl s

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace FiniteClosureSystem

variable (C : FiniteClosureSystem α)

/-- A set is closed if it equals its own closure. -/
def IsClosed (s : Set α) : Prop := C.cl s = s

theorem isClosed_cl (s : Set α) : C.IsClosed (C.cl s) := C.idempotent s

/-
Intersection of closed sets is closed.
-/
theorem isClosed_inter {A B : Set α} (hA : C.IsClosed A) (hB : C.IsClosed B) :
    C.IsClosed (A ∩ B) := by
  refine' le_antisymm _ _;
  · have := C.mono_cl;
    exact Set.subset_inter ( le_trans ( this ( Set.inter_subset_left ) ) hA.le ) ( le_trans ( this ( Set.inter_subset_right ) ) hB.le );
  · exact C.extensive _

/-
The whole type is closed.
-/
theorem isClosed_univ : C.IsClosed (Set.univ : Set α) := by
  obtain ⟨ s, hs ⟩ := C;
  exact Set.Subset.antisymm ( fun x hx => by aesop ) ( by aesop )

/-- If `s ⊆ t` and `t` is closed, then `cl(s) ⊆ t`. -/
theorem cl_le_of_le {s t : Set α} (hs : s ⊆ t) (ht : C.IsClosed t) :
    C.cl s ⊆ t := by
  calc C.cl s ⊆ C.cl t := C.mono_cl hs
    _ = t := ht

end FiniteClosureSystem

/-! ## Part III: The Type of Closed Sets -/

/-- A closed set in a finite closure system, bundled with its closedness proof. -/
@[ext]
structure ClosedSet (C : FiniteClosureSystem α) where
  /-- The underlying set -/
  carrier : Set α
  /-- Proof that the set is closed -/
  is_closed : C.IsClosed carrier

namespace ClosedSet

variable {C : FiniteClosureSystem α}

instance : CoeTC (ClosedSet C) (Set α) where
  coe T := T.carrier


/-- The lattice structure on closed sets: meet = intersection, join = closure of union. -/
instance : Lattice (ClosedSet C) where
  le K L := K.carrier ⊆ L.carrier
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h1 h2 := ClosedSet.ext (Set.Subset.antisymm h1 h2)
  inf K L := ⟨K.carrier ∩ L.carrier, C.isClosed_inter K.is_closed L.is_closed⟩
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ h1 h2 := Set.subset_inter h1 h2
  sup K L := ⟨C.cl (K.carrier ∪ L.carrier), C.isClosed_cl _⟩
  le_sup_left K L := Set.subset_union_left.trans (C.extensive _)
  le_sup_right K L := Set.subset_union_right.trans (C.extensive _)
  sup_le _ _ M h1 h2 := C.cl_le_of_le (Set.union_subset h1 h2) M.is_closed

instance : OrderTop (ClosedSet C) where
  top := ⟨Set.univ, C.isClosed_univ⟩
  le_top _ := Set.subset_univ _

theorem le_def (K L : ClosedSet C) : K ≤ L ↔ K.carrier ⊆ L.carrier := Iff.rfl




end ClosedSet

/-! ## Part IV: Distributive Closure Systems -/

/-- A finite closure system whose closed sets form a distributive lattice. -/
structure DistribClosureSystem (α : Type*) [Fintype α] [DecidableEq α]
    extends FiniteClosureSystem α where
  /-- Distributivity: `A ∩ cl(B ∪ C) ⊆ cl((A ∩ B) ∪ (A ∩ C))` for closed `A`. -/
  cl_distrib : ∀ (A B C : Set α),
    toFiniteClosureSystem.IsClosed A →
    A ∩ toFiniteClosureSystem.cl (B ∪ C) ⊆
      toFiniteClosureSystem.cl ((A ∩ B) ∪ (A ∩ C))

namespace DistribClosureSystem

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (D : DistribClosureSystem α)

/-- The underlying closure system. -/
abbrev toFCS : FiniteClosureSystem α := D.toFiniteClosureSystem

/-
The lattice of closed sets of a distributive closure system is distributive.
-/
instance instDistribLattice : DistribLattice (ClosedSet D.toFCS) where
  le_sup_inf := by
    intro x y z;
    have h1 : D.toFCS.cl (x.carrier ∪ y.carrier) ∩ D.toFCS.cl (x.carrier ∪ z.carrier) ⊆ D.toFCS.cl ((D.toFCS.cl (x.carrier ∪ y.carrier) ∩ x.carrier) ∪ (D.toFCS.cl (x.carrier ∪ y.carrier) ∩ z.carrier)) := by
      have := D.cl_distrib ( D.toFCS.cl ( x.carrier ∪ y.carrier ) ) x.carrier z.carrier ( D.toFCS.isClosed_cl _ );
      exact this;
    have h2 : D.toFCS.cl (x.carrier ∪ y.carrier) ∩ x.carrier = x.carrier := by
      exact Set.inter_eq_right.mpr ( Set.Subset.trans ( Set.subset_union_left ) ( D.toFCS.extensive _ ) );
    have h3 : D.toFCS.cl (x.carrier ∪ y.carrier) ∩ z.carrier ⊆ D.toFCS.cl ((z.carrier ∩ x.carrier) ∪ (z.carrier ∩ y.carrier)) := by
      have := D.cl_distrib z.carrier x.carrier y.carrier z.is_closed;
      simpa only [ Set.inter_comm ] using this;
    have h4 : D.toFCS.cl (x.carrier ∪ y.carrier) ∩ D.toFCS.cl (x.carrier ∪ z.carrier) ⊆ D.toFCS.cl (x.carrier ∪ D.toFCS.cl ((z.carrier ∩ x.carrier) ∪ (z.carrier ∩ y.carrier))) := by
      refine' Set.Subset.trans h1 _;
      exact D.toFCS.mono_cl ( Set.union_subset_union ( by aesop ) h3 );
    have h5 : D.toFCS.cl (x.carrier ∪ D.toFCS.cl ((z.carrier ∩ x.carrier) ∪ (z.carrier ∩ y.carrier))) ⊆ D.toFCS.cl (x.carrier ∪ (z.carrier ∩ y.carrier)) := by
      have h5 : x.carrier ∪ D.toFCS.cl ((z.carrier ∩ x.carrier) ∪ (z.carrier ∩ y.carrier)) ⊆ D.toFCS.cl (x.carrier ∪ (z.carrier ∩ y.carrier)) := by
        have h5 : x.carrier ⊆ D.toFCS.cl (x.carrier ∪ (z.carrier ∩ y.carrier)) := by
          exact fun x hx => D.toFCS.extensive _ ( Set.mem_union_left _ hx );
        have h6 : D.toFCS.cl ((z.carrier ∩ x.carrier) ∪ (z.carrier ∩ y.carrier)) ⊆ D.toFCS.cl (x.carrier ∪ (z.carrier ∩ y.carrier)) := by
          exact D.toFCS.mono_cl ( by aesop_cat );
        exact Set.union_subset h5 h6;
      exact D.toFCS.mono_cl h5 |> le_trans <| by simp +decide [ D.toFCS.idempotent ] ;
    convert h4.trans h5 using 1;
    simp +decide [ Set.inter_comm, ClosedSet.le_def ];
    congr! 1

end DistribClosureSystem

/-! ## Part V: Prime Closed Sets and Separation -/

section PrimeSeparation

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (D : DistribClosureSystem α)

/-- A closed set is **prime** (meet-prime) if it is `InfPrime` in the
lattice of closed sets. -/
def IsPrimeClosedSet (P : ClosedSet D.toFCS) : Prop := InfPrime P

/-- A closed set `K` is **semiprime** if for every element not in `K`,
there exists a prime closed set extending `K` that avoids that element. -/
def IsSemiprimeClosedSet (K : ClosedSet D.toFCS) : Prop :=
  ∀ a : α, a ∉ K.carrier →
    ∃ P : ClosedSet D.toFCS, IsPrimeClosedSet D P ∧ K ≤ P ∧ a ∉ P.carrier

/-
**Every closed set is semiprime** in a finite distributive closure system.
-/
theorem isSemiprimeClosedSet_of_distrib (K : ClosedSet D.toFCS) :
    IsSemiprimeClosedSet D K := by
  -- Consider the closed set $A_a = \langle D.toFCS.cl \{a\}, isClosed_cl \rangle$.
  intro a ha
  set A_a : ClosedSet D.toFCS := ⟨D.toFCS.cl {a}, D.toFCS.isClosed_cl _⟩
  have hA_a_not_le_K : ¬(A_a ≤ K) := by
    exact fun h => ha <| h <| D.toFCS.extensive _ <| Set.mem_singleton _;
  -- By exists_infPrime_separation, there exists an InfPrime P with K ≤ P and A_a ≰ P.
  obtain ⟨P, hP_prime, hP_K, hP_A_a⟩ : ∃ P : ClosedSet D.toFCS, InfPrime P ∧ K ≤ P ∧ ¬(A_a ≤ P) := by
    have h_lattice : ∃ P : ClosedSet D.toFCS, InfPrime P ∧ K ≤ P ∧ ¬(A_a ≤ P) := by
      have h_lattice : ∀ {a b : ClosedSet D.toFCS}, ¬(a ≤ b) → ∃ p : ClosedSet D.toFCS, InfPrime p ∧ b ≤ p ∧ ¬(a ≤ p) := by
        intros a b hab;
        have := @exists_infPrime_separation ( ClosedSet D.toFCS );
        convert this hab;
        exact Fintype.ofInjective ( fun x => x.carrier ) fun x y hxy => by cases x; cases y; aesop;
      exact h_lattice hA_a_not_le_K;
    exact h_lattice;
  refine' ⟨ P, hP_prime, hP_K, _ ⟩;
  contrapose! hP_A_a;
  exact D.toFCS.cl_le_of_le ( Set.singleton_subset_iff.mpr hP_A_a ) P.is_closed

/-- **Main theorem: constructive prime witness extraction.**
In a finite distributive closure system, for any closed set `K` and any
element `a ∉ K`, there exists a prime closed set extending `K` and
avoiding `a`. -/
theorem exists_prime_closedSet_separation
    (K : ClosedSet D.toFCS) (a : α)
    (ha : a ∉ K.carrier) :
    ∃ P : ClosedSet D.toFCS, IsPrimeClosedSet D P ∧ K ≤ P ∧ a ∉ P.carrier :=
  isSemiprimeClosedSet_of_distrib D K a ha

/-
**Spectral reconstruction theorem.**
-/

end PrimeSeparation

/-! ## Part VI: Algorithmic Witness Extraction -/

section AlgorithmicWitness

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (D : DistribClosureSystem α)

/-- A certificate witnessing prime separation of `a` from `K`. -/
structure PrimeWitnessCert (K : ClosedSet D.toFCS) (a : α) where
  /-- The prime witness -/
  P : ClosedSet D.toFCS
  /-- `P` is prime -/
  isPrime : IsPrimeClosedSet D P
  /-- `P` extends `K` -/
  extends_K : K ≤ P
  /-- `P` avoids `a` -/
  avoids_a : a ∉ P.carrier

/-- Noncomputably extract a prime witness certificate. -/
noncomputable def extractPrimeWitness
    (K : ClosedSet D.toFCS) (a : α) (ha : a ∉ K.carrier) :
    PrimeWitnessCert D K a :=
  have h := exists_prime_closedSet_separation D K a ha
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2⟩


end AlgorithmicWitness


