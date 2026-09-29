-- Prove2me | Definitions.Def_Bridges_ModularScatteringDuality
-- name    : Bridges_ModularScatteringDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:26.245896+00:00
-- url     : https://prove2.me/theorems/551abee6-bb58-4e99-b916-53aba9ffcacb
-- title:
--   Aether Catalog definitions — Bridges_ModularScatteringDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ModularScatteringDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ModularScatteringDuality.lean by skeleton subtraction
import Mathlib

/-!
# Modular Scattering Duality via Idempotent Closure-Scattering Systems

This module establishes a finite duality and realization theory for **closure-scattering systems**,
creating a certified bridge between closure dynamics, finite idempotent semimodule duality,
and scattering/resonance reconstruction from boundary data.

## Mathematical Overview

A closure-scattering system consists of:
- A state space `X` with a closure operator `cl : Set X → Set X`
- A transfer (evolution) map `T : X → X` propagating states forward in time
- Boundary observation functionals `boundary : X → C → R` measuring states through channels

The **resonance congruence** identifies states that are observationally indistinguishable:
two states are equivalent when all sequences of boundary observations under iterated transfer
coincide. This is the idempotent analogue of Nerode/Myhill equivalence in automata theory.

The **spectral boundary semimodule** is the shift-closed set of response profiles,
representing the "dual" or "spectral" side of a closure-scattering system.

## Main Results

- `resonanceEquiv_is_equivalence`: resonance equivalence is an equivalence relation
- `resonanceEquiv_coarsest`: it is the coarsest observation-compatible equivalence (minimality)
- `transfer_preserves_resonanceEquiv`: transfer respects resonance equivalence
- `separated_systems_isomorphic_of_same_profiles`: separated systems with identical
  response profile ranges are isomorphic (**main duality/uniqueness theorem**)
- `minimalRealization_separated`: the minimal realization is separated
- `minimal_resonance_realization_unique`: any separated realization of the same boundary
  data is isomorphic to the minimal realization (**certified reconstruction**)

## Physical Interpretation

- **Closure defect = resonance**: failure of transfer to preserve closure ↔ resonant modes
- **Boundary response = scattering data**: channel functionals ↔ scattering amplitudes
- **Minimal reduced quotient = minimal resonance realization**
- **Separation by observables = distinguishability of scattering channels**

## Cross-Domain Connections

This framework provides an idempotent analogue of:
- Hankel minimal realization in systems theory
- Nerode/Myhill equivalence in automata theory
- S-matrix reconstruction in scattering theory
- Tropical spectral duality in idempotent geometry
-/

namespace ModularScatteringDuality

/-! ## Core Definitions -/

/-- A closure-scattering system: a closure operator on subsets of a state space,
together with a transfer (evolution) map and boundary observation functionals.

This models a discrete scattering system where `cl` captures reachable/generated states,
`transfer` propagates states forward in time, and `boundary` observes states through
output channels. The interaction between closure and transfer gives rise to resonance. -/
structure ClosureScatteringSystem (R : Type*) (X : Type*) (C : Type*) where
  /-- Closure operator on subsets of the state space -/
  cl : Set X → Set X
  /-- Closure is extensive: every set is contained in its closure -/
  cl_extensive : ∀ A, A ⊆ cl A
  /-- Closure is monotone: larger sets have larger closures -/
  cl_monotone : Monotone cl
  /-- Closure is idempotent: closing a closed set has no effect -/
  cl_idem : ∀ A, cl (cl A) = cl A
  /-- Transfer map: one-step evolution of states -/
  transfer : X → X
  /-- Boundary observation: measures a state through a channel -/
  boundary : X → C → R

variable {R : Type*} {X : Type*} {C : Type*}

/-- The response profile of a state records boundary observations of all iterates
under transfer. This is the complete observable behavior — the idempotent
analogue of an impulse response in systems theory. -/
def ClosureScatteringSystem.responseProfile (S : ClosureScatteringSystem R X C)
    (x : X) : ℕ → C → R :=
  fun n c => S.boundary (S.transfer^[n] x) c

/-- Resonance equivalence: two states are equivalent when they produce identical
response profiles, i.e., they are indistinguishable by any sequence of boundary
observations under transfer evolution. This is the idempotent Nerode equivalence. -/
def ClosureScatteringSystem.resonanceEquiv (S : ClosureScatteringSystem R X C)
    (x y : X) : Prop :=
  S.responseProfile x = S.responseProfile y

/-- A closure-scattering system is **separated** when distinct states have distinct
response profiles. This is the "reduced" or "fully observable" condition: every
state is uniquely determined by its boundary behavior. -/
def ClosureScatteringSystem.Separated (S : ClosureScatteringSystem R X C) : Prop :=
  Function.Injective S.responseProfile

/-- The closure defect of a set measures how much `transfer` fails to commute
with `cl`: it consists of states in `T(cl(A))` that lie outside `cl(T(A))`.
These are the "resonant" states — generated by closure then transferred,
but not reachable by transferring then closing. -/
def ClosureScatteringSystem.closureDefect (S : ClosureScatteringSystem R X C)
    (A : Set X) : Set X :=
  S.transfer '' (S.cl A) \ S.cl (S.transfer '' A)

/-- Transfer is closure-compatible when `T(cl(A)) ⊆ cl(T(A))` for all `A`.
When this holds, there are no resonance defects — transfer and closure commute. -/
def ClosureScatteringSystem.TransferClosureCompatible
    (S : ClosureScatteringSystem R X C) : Prop :=
  ∀ A, S.transfer '' (S.cl A) ⊆ S.cl (S.transfer '' A)

/-- A spectral boundary semimodule is a shift-closed set of response profiles.
This represents the "dual" or "spectral" side of a closure-scattering system:
the observable boundary data organized into an algebraic structure.

The shift-closure property captures the fact that if a response profile is observable,
then so is its time-shifted version (one step of transfer evolution). -/
structure SpectralBoundarySemimodule (R : Type*) (C : Type*) where
  /-- The set of response profiles -/
  profiles : Set (ℕ → C → R)
  /-- Profiles are closed under the time-shift operation -/
  shift_closed : ∀ f ∈ profiles, (fun n c => f (n + 1) c) ∈ profiles

/-- A morphism between closure-scattering systems preserves transfer dynamics
and boundary observations. -/
structure CSSMorphism {R : Type*} {X₁ X₂ : Type*} {C : Type*}
    (S₁ : ClosureScatteringSystem R X₁ C)
    (S₂ : ClosureScatteringSystem R X₂ C) where
  /-- The underlying map on state spaces -/
  toFun : X₁ → X₂
  /-- The map commutes with transfer -/
  transfer_comm : ∀ x, toFun (S₁.transfer x) = S₂.transfer (toFun x)
  /-- The map preserves boundary observations -/
  boundary_comm : ∀ x c, S₁.boundary x c = S₂.boundary (toFun x) c

/-- An isomorphism of closure-scattering systems: a bijective morphism.
This is the correct notion of equivalence for scattering systems — it preserves
all dynamical and observational structure. -/
structure CSSIsomorphism {R : Type*} {X₁ X₂ : Type*} {C : Type*}
    (S₁ : ClosureScatteringSystem R X₁ C)
    (S₂ : ClosureScatteringSystem R X₂ C) extends CSSMorphism S₁ S₂ where
  /-- The underlying map is bijective -/
  toFun_bijective : Function.Bijective toFun

/-! ## Resonance Congruence Properties -/

section ResonanceCongruence

variable (S : ClosureScatteringSystem R X C)



/-
The response profile of `T(x)` is the tail-shift of the response profile of `x`.
This identity links transfer dynamics to the shift operation on spectral boundary
semimodules: applying transfer corresponds to dropping the first observation.
-/

/-
Transfer preserves resonance equivalence: if two states have identical response
profiles, so do their images under transfer.
-/

/-
**Minimality of resonance congruence.**
Resonance equivalence is the coarsest equivalence relation compatible with both
boundary observations and transfer dynamics. If `≈` is any equivalence such that
equivalent states have equal boundary values and transfer preserves the equivalence,
then `x ≈ y` implies `resonanceEquiv x y`.

This means resonance equivalence makes the maximum identifications while preserving
observable behavior — it yields the minimal realization.
-/

/-
When transfer is closure-compatible, the closure defect is empty.
-/

end ResonanceCongruence

/-! ## Morphism Properties -/

section MorphismProperties

variable {R : Type*} {X₁ X₂ : Type*} {C : Type*}
variable {S₁ : ClosureScatteringSystem R X₁ C}
variable {S₂ : ClosureScatteringSystem R X₂ C}

/-
A CSS morphism commutes with iterated transfer: `φ(T₁ⁿ(x)) = T₂ⁿ(φ(x))`.
-/

/-
A CSS morphism preserves response profiles: the response profile of `φ(x)` in `S₂`
equals the response profile of `x` in `S₁`. This is the fundamental compatibility
between morphisms and the spectral boundary.
-/

end MorphismProperties

/-! ## Spectral Boundary Construction -/

section SpectralBoundary

variable {R : Type*} {X : Type*} {C : Type*}

/-
Shift of a response profile remains in the range of response profiles.
This is because shifting corresponds to applying one step of transfer.
-/
theorem responseProfile_shift_mem_range (S : ClosureScatteringSystem R X C)
    {f : ℕ → C → R} (hf : f ∈ Set.range S.responseProfile) :
    (fun n c => f (n + 1) c) ∈ Set.range S.responseProfile := by
  -- Let's obtain the state `x` such that `f = S.responseProfile x`.
  obtain ⟨x, hx⟩ := hf;
  exact ⟨ S.transfer x, by aesop ⟩

/-- Construct the spectral boundary semimodule from a closure-scattering system.
This maps a system to its "dual" representation as a shift-closed set of
response profiles, capturing all observable boundary behavior. -/
noncomputable def ClosureScatteringSystem.toSpectralBoundary
    (S : ClosureScatteringSystem R X C) :
    SpectralBoundarySemimodule R C where
  profiles := Set.range S.responseProfile
  shift_closed _ hf := responseProfile_shift_mem_range S hf

/-
A surjective CSS morphism induces inclusion of spectral boundary profiles:
if `φ : S₁ → S₂` is surjective, then every response profile of `S₂` is also
a response profile of `S₁`.
-/

end SpectralBoundary

/-! ## Main Duality / Uniqueness Theorem -/

section MainDuality

variable {R : Type*} {C : Type*}

/-
**Main Duality Theorem: Separated systems with identical response profile ranges
are isomorphic.**

If two closure-scattering systems are both separated (reduced/observable) and have
the same set of response profiles, then there exists a canonical isomorphism between
them. The isomorphism is constructed by matching states with identical response profiles.

This is the idempotent analogue of the uniqueness of minimal realization in systems
theory, and of the Myhill-Nerode theorem for automata. It establishes that the
observable boundary behavior completely determines the reduced system up to isomorphism.

**Proof idea:** Define `f : X₁ → X₂` by sending each state to the unique state with
the same response profile (exists by equal ranges, unique by separation). Then:
- `f` is injective because `S₁` is separated
- `f` is surjective because the ranges match
- `f` commutes with transfer because shifting response profiles commutes with `f`
- `f` preserves boundary because boundary values are read from response profiles at `n = 0`
-/

end MainDuality

/-! ## Minimal Realization -/

section MinimalRealization

variable {R : Type*} {X : Type*} {C : Type*}

/-- The minimal realization of a closure-scattering system.
States are response profiles (elements of `Set.range S.responseProfile`),
transfer is the shift map, and boundary observation is evaluation at `n = 0`.
The closure is taken to be the identity (trivial closure).

This construction is the idempotent analogue of the observable canonical form
in linear systems theory. It produces the smallest separated system with the
same observable boundary behavior. -/
noncomputable def ClosureScatteringSystem.minimalRealization
    (S : ClosureScatteringSystem R X C) :
    ClosureScatteringSystem R ↥(Set.range S.responseProfile) C where
  cl := fun A => A
  cl_extensive := fun A => le_refl A
  cl_monotone := monotone_id
  cl_idem := fun _ => rfl
  transfer := fun ⟨f, hf⟩ =>
    ⟨fun n c => f (n + 1) c, responseProfile_shift_mem_range S hf⟩
  boundary := fun ⟨f, _⟩ c => f 0 c

/-
The `n`-fold iterate of transfer in the minimal realization shifts
a response profile by `n` steps.
-/

/-
The response profile in the minimal realization equals the underlying
function value. This is the key identity showing that the minimal realization
is a faithful representation of response profiles.
-/

/-
The minimal realization is separated: distinct response profiles remain
distinct in the minimal realization.
-/

/-
The minimal realization has the same spectral boundary as the original system:
the sets of response profiles coincide.
-/

/-
**Certified Minimal Resonance Reconstruction.**
Any separated system with the same response profiles as `S` is isomorphic to
the minimal realization of `S`. This establishes:
1. **Existence**: the minimal realization always exists
2. **Uniqueness**: it is the unique separated system with that boundary data
3. **Reconstruction**: boundary response data certifiably determines the model
-/

/-
**Finite Closure-Scattering Duality.**
For a system with finite state space, there exists a spectral boundary semimodule
such that the minimal realization is separated, has the same spectral boundary,
and the resonance congruence is the coarsest observation-compatible equivalence.
-/

end MinimalRealization

end ModularScatteringDuality


