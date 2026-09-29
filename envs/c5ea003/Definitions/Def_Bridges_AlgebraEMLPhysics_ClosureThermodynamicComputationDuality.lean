-- Prove2me | Definitions.Def_Bridges_AlgebraEMLPhysics_ClosureThermodynamicComputationDuality
-- name    : Bridges_AlgebraEMLPhysics_ClosureThermodynamicComputationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:56.290165+00:00
-- url     : https://prove2.me/theorems/ed0600d9-8927-4ef3-8808-b2b3f50559db
-- title:
--   Aether Catalog definitions — Bridges_AlgebraEMLPhysics_ClosureThermodynamicComputationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlgebraEMLPhysics.ClosureThermodynamicComputationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlgebraEMLPhysics/ClosureThermodynamicComputationDuality.lean by skeleton subtraction
import Mathlib
/-
# Closure–Thermodynamic Computation Duality via Idempotent Dissipation Semimodules
# and Certified Minimal Entropy-Scheduler Reconstruction

This file establishes a finite thermodynamic analogue of Myhill–Nerode minimal
realization theory, where **closure-compatible dissipation semantics** replaces
language acceptance or linear observability.

## Main Results

* `closedProfile_injective` — Dissipation profiles are injective on closed
  sets for separated systems.
* `separated_realization_state_minimal` — A separated realization has the fewest
  closed sets among all realizations of the same dissipation data.
* `separated_realizations_card_eq` — Two separated realizations of the same data
  have equal closed-set counts (uniqueness).
* `separated_realizations_equiv` — Profile-preserving bijection between two
  separated realizations (isomorphism theorem).
* `canonical_realization_exists` — Every nonempty finite dissipation datum
  is realizable by a separated ThermoComp.
* `reversible_or_irreversible` — Every generator is reversible or irreversible.
* `strict_closure_growth_implies_positive_energy` — Non-trivial closure growth
  implies positive energy cost (Landauer witness).
* `thermodynamic_realization_duality` — The complete duality theorem.

## Mathematical Significance

This constitutes a **"Myhill–Nerode theorem for irreversible physics"**: the minimal
finite thermodynamic scheduler is uniquely reconstructible from its
closure-constrained dissipative cost data.
-/


set_option maxHeartbeats 800000

open Finset Function

namespace ClosureThermoDuality

/-! ## Section 1: Closure Operators on Finite Sets -/

/-- A closure operator on `Finset α` over a finite type. -/
structure ClosureOp (α : Type*) [Fintype α] [DecidableEq α] where
  cl : Finset α → Finset α
  extensive : ∀ A, A ⊆ cl A
  mono : ∀ {A B : Finset α}, A ⊆ B → cl A ⊆ cl B
  idem : ∀ A, cl (cl A) = cl A

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set is closed if it is a fixpoint of the closure operator. -/
def ClosureOp.IsClosed (C : ClosureOp α) (A : Finset α) : Prop := C.cl A = A

/-- Decidability of `IsClosed` (since `Finset` equality is decidable). -/
instance (C : ClosureOp α) (A : Finset α) : Decidable (C.IsClosed A) :=
  inferInstanceAs (Decidable (C.cl A = A))



/-! ## Section 2: Thermodynamic Computation Objects -/

/-- A finite thermodynamic computation object: closure + energy + n generators. -/
structure ThermoComp (S : Type*) [Fintype S] [DecidableEq S] (n : ℕ) extends
    ClosureOp S where
  energy : Finset S → ℕ
  energy_mono : ∀ A, energy A ≤ energy (cl A)
  dissip : Fin n → Finset S → ℕ

variable {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}

/-- The dissipation profile of a set: the vector of dissipation costs
    of the closure across all generators. -/
def ThermoComp.profile (T : ThermoComp S n) (A : Finset S) : Fin n → ℕ :=
  fun i => T.dissip i (T.cl A)




/-! ## Section 3: Separatedness and Profile Injectivity -/

/-- A system is **separated** if distinct closed sets have distinct profiles. -/
def ThermoComp.Separated (T : ThermoComp S n) : Prop :=
  ∀ A B : Finset S, T.toClosureOp.IsClosed A → T.toClosureOp.IsClosed B →
    T.profile A = T.profile B → A = B

/-- The type of closed sets of a thermodynamic computation object. -/
abbrev ThermoComp.ClosedSetType (T : ThermoComp S n) :=
  {A : Finset S // T.toClosureOp.IsClosed A}

/-- The profile map restricted to closed sets. -/
def ThermoComp.closedProfile (T : ThermoComp S n) (p : T.ClosedSetType) :
    Fin n → ℕ := T.profile p.val


/-! ## Section 4: Dissipation Data and Realization -/

/-- Abstract dissipation data: a finite family of distinct profiles. -/
structure DissipData (n : ℕ) where
  numProfs : ℕ
  prof : Fin numProfs → (Fin n → ℕ)
  prof_inj : Function.Injective prof

/-- A ThermoComp **realizes** dissipation data if there is a profile-preserving
    surjection from closed sets to data indices. -/
structure ThermoComp.Realizes (T : ThermoComp S n) (D : DissipData n) where
  map : T.ClosedSetType → Fin D.numProfs
  map_surj : Function.Surjective map
  map_compat : ∀ p : T.ClosedSetType, T.closedProfile p = D.prof (map p)




/-! ## Section 5: Minimality and Uniqueness -/




/-! ## Section 6: Canonical Realization -/


/-
**Canonical Realization**: Every nonempty finite dissipation datum is
    realizable by a separated ThermoComp. The construction uses the identity
    closure on `Fin D.numProfs` and encodes set membership via dissipation
    to achieve separation.
-/

/-! ## Section 7: Zero-Loss Strata and Reversibility -/

/-- A closed set has **zero loss** if all generators produce zero dissipation. -/
def ThermoComp.IsZeroLoss (T : ThermoComp S n) (A : Finset S) : Prop :=
  T.toClosureOp.IsClosed A ∧ ∀ i : Fin n, T.dissip i A = 0



/-- A generator is **reversible** if it has zero dissipation on all closed sets. -/
def ThermoComp.IsReversible (T : ThermoComp S n) (i : Fin n) : Prop :=
  ∀ A : Finset S, T.toClosureOp.IsClosed A → T.dissip i A = 0

/-- A generator is **irreversible** if some closed set witnesses positive dissipation. -/
def ThermoComp.IsIrreversible (T : ThermoComp S n) (i : Fin n) : Prop :=
  ∃ A : Finset S, T.toClosureOp.IsClosed A ∧ T.dissip i A ≠ 0



/-- The Finset of reversible generators. -/
noncomputable def ThermoComp.reversibleGens (T : ThermoComp S n) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    ∀ A : Finset S, T.toClosureOp.IsClosed A → T.dissip i A = 0)

/-- The Finset of irreversible generators. -/
noncomputable def ThermoComp.irreversibleGens (T : ThermoComp S n) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    ∃ A : Finset S, T.toClosureOp.IsClosed A ∧ T.dissip i A ≠ 0)



/-! ## Section 8: Strict Energy Growth (Landauer Witness) -/

/-- Strict energy monotonicity: proper closure growth strictly increases energy. -/
def ThermoComp.StrictEnergyMono (T : ThermoComp S n) : Prop :=
  ∀ A : Finset S, T.cl A ≠ A → T.energy A < T.energy (T.cl A)



/-
**Energy chain bound**: For energy strictly monotone on closed sets,
    a strict chain of k closed sets forces energy gap ≥ k-1.
    Here specialized to k=3 for concreteness.
-/

/-! ## Section 9: Profile Equivalence -/

/-- Profile equivalence: two sets have the same dissipation profile. -/
def ThermoComp.ProfileEquiv (T : ThermoComp S n) (A B : Finset S) : Prop :=
  T.profile A = T.profile B



/-! ## Section 10: Complete Duality Theorem -/


/-! ## Section 11: Concrete Example -/

/-- A two-state separated system: two states with identity closure
    and two generators acting as membership indicators, giving
    distinct profiles to every finset. -/
noncomputable def twoStateSeparated : ThermoComp (Fin 2) 2 where
  cl := id
  extensive := fun _ => Finset.Subset.refl _
  mono := fun h => h
  idem := fun _ => rfl
  energy := fun A => A.card
  energy_mono := fun _ => le_refl _
  dissip := fun i A => if i ∈ A then 1 else 0

/-
The two-state system with indicator dissipation is separated:
    distinct sets have distinct profiles since the indicator function
    uniquely determines set membership.
-/

end ClosureThermoDuality


