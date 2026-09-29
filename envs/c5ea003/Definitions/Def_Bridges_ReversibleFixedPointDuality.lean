-- Prove2me | Definitions.Def_Bridges_ReversibleFixedPointDuality
-- name    : Bridges_ReversibleFixedPointDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:01.738339+00:00
-- url     : https://prove2.me/theorems/a5fa0c0a-1578-4202-b741-7e2fdc9b4b5a
-- title:
--   Aether Catalog definitions — Bridges_ReversibleFixedPointDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ReversibleFixedPointDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ReversibleFixedPointDuality.lean by skeleton subtraction
import Mathlib
/-
# Temporal Fixed-Point Duality for Reversible Causal Semirings

This file formalizes a duality between reversible finite-state dynamics,
temporal fixed-point semantics, and certified loop invariant reconstruction.

## Main Results

### Reversible Dynamics (§1-§2)
- `bijective_dynamics_purely_periodic` — Bijections on finite types yield purely periodic orbits
- `iterate_eq_iff_period_dvd` — f^[k] x = x iff period divides k

### Temporal Fixed-Point Operators (§3-§4)
- `temporalReach_monotone` — The temporal reachability operator is monotone
- `temporalCoreach_monotone` — The temporal co-reachability operator is monotone

### Orbit-Fixed-Point Correspondence (§5)
- `periodic_orbit_is_lfp_gfp_pair` — Periodic orbits are minimal invariant sets

### Temporal Congruence (§6)
- `temporalCongruence_is_right_congruence` — Temporal congruence preserved by transitions

### Loop Invariant Reconstruction (§7)
- `certified_loop_invariant_reconstruction` — Certified forward/backward invariants

### Bisimulation Invariance (§9)
- `bisimulation_period_divides` — Periods divide under bisimulation
- `fixedPointSpectrum_coarser_under_bisim` — Spectrum coarsens under bisimulation

## Bridges
- **Algebra ↔ Logic**: Knaster-Tarski fixed points ↔ temporal μ/ν-calculus
- **Logic ↔ Computation**: Temporal congruence ↔ automata minimization
- **Computation ↔ Algebra**: Loop invariants ↔ idempotent semiring dynamics
-/


open Function Finset

noncomputable section

namespace Bridges.TemporalComputation

/-! ## §1. Reversible Finite-State Dynamics -/

/-- A reversible transition system: a bijective self-map on a finite type. -/
structure ReversibleSystem (S : Type*) [Fintype S] where
  /-- The forward transition function -/
  step : S → S
  /-- The inverse transition function -/
  inv : S → S
  /-- step and inv are mutual inverses -/
  left_inv : ∀ s, inv (step s) = s
  right_inv : ∀ s, step (inv s) = s

variable {S : Type*} [Fintype S] [DecidableEq S]


/-! ## §2. Pure Periodicity of Reversible Dynamics -/

/-
On a finite type, a bijective map yields purely periodic orbits:
    there exists p > 0 such that f^[p] x = x. This is strictly stronger
    than `finite_dynamics_eventually_periodic` which only gives f^[m] = f^[n].

    Bridge: connects reversible computation to temporal logic via periodicity.
-/

/-
f^[k] x = x iff the minimal period divides k, for bijections on finite types.
-/

/-
For bijections on finite types, the minimal period is positive.
-/

/-! ## §3. Temporal Fixed-Point Operators on Finsets -/

/-- The **temporal reachability operator**: F(X) = X ∪ f(X).
    Bridge: algebraic reachability ↔ μ-calculus least fixed point. -/
def temporalReach (f : S → S) (X : Finset S) : Finset S :=
  X ∪ X.image f



/-- The **temporal co-reachability operator**: G(X) = {s ∈ X | f(s) ∈ X}.
    Bridge: algebraic co-reachability ↔ ν-calculus greatest fixed point. -/
def temporalCoreach (f : S → S) (X : Finset S) : Finset S :=
  X.filter (fun s => f s ∈ X)



/-! ## §4. Invariant Sets and Their Characterization -/

/-- A set is **T-invariant** if f maps it into itself: f(X) ⊆ X. -/
def IsInvariant (f : S → S) (X : Finset S) : Prop :=
  X.image f ⊆ X

/-
A set is T-invariant iff it is a fixed point of the co-reachability operator.
    Bridge: algebraic (semiring) viewpoint ↔ logical (fixed point) viewpoint.
-/

/-
For a bijection, invariant set has f-image equal to itself.
-/

/-
For a bijection, any invariant set is backward-invariant.
-/


/-! ## §5. Periodic Orbits as Minimal Invariant Sets -/

/-- The forward orbit of a single element under f, computed using Fintype.card bound. -/
def singletonOrbit (f : S → S) (x : S) : Finset S :=
  (Finset.range (Fintype.card S)).image (fun k => (f^[k]) x)


/-
The singleton orbit is T-invariant.
-/

/-
**Orbit minimality theorem**: The orbit of x under a bijection is the
    smallest invariant set containing x.

    Bridge: Knaster-Tarski (Algebra) ↔ μ-calculus reachability (Logic)
    ↔ minimal automaton states (Computation).
-/

/-- **Fixed-point spectrum**: the set of orbit sizes (minimal periods). -/
def fixedPointSpectrum (f : S → S) : Finset ℕ :=
  Finset.univ.image (fun x : S => Function.minimalPeriod f x)

/-! ## §6. Temporal Congruence -/

/-- Two states are **temporally congruent** w.r.t. observation `obs` if
    they produce identical observation sequences under all future iterates.
    Bridge: Myhill-Nerode for temporal logic ↔ automata minimization. -/
def temporalCongruent (f : S → S) (obs : S → ℕ) (x y : S) : Prop :=
  ∀ k : ℕ, obs ((f^[k]) x) = obs ((f^[k]) y)




/-! ## §7. Loop Invariants from Fixed Points -/

/-- A **loop invariant** for f is a predicate preserved by f. -/
def IsLoopInvariant (f : S → S) (P : S → Prop) : Prop :=
  ∀ s, P s → P (f s)


/-
The complement of an invariant set of a bijection is also invariant.
    Bridge: reversible dynamics ↔ dual loop invariants (safety + liveness).
-/



/-! ## §8. Idempotent Semiring Structure -/




/-! ## §9. Bisimulation Invariance of the Spectrum -/

/-- A **bisimulation**: a surjective map commuting with transitions. -/
structure Bisimulation (S₁ S₂ : Type*) [Fintype S₁] [DecidableEq S₁]
    [Fintype S₂] [DecidableEq S₂]
    (f₁ : S₁ → S₁) (f₂ : S₂ → S₂) where
  φ : S₁ → S₂
  surj : Surjective φ
  commutes : ∀ s, φ (f₁ s) = f₂ (φ s)


/-
Under a bisimulation, periods in the codomain divide those in the domain.
    Bridge: the period spectrum is a bisimulation semi-invariant.
-/


/-! ## §10. The Full Duality Theorem -/


end Bridges.TemporalComputation


