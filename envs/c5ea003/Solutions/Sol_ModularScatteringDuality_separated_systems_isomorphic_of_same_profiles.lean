-- Prove2me | solution 1 for ModularScatteringDuality.separated_systems_isomorphic_of_same_profiles
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:05:16.693633+00:00
-- url     : https://prove2.me/submissions/b410ecf7-4cbf-4355-b4bd-1d65dddd3b81

-- Sol generated from Bridges/ModularScatteringDuality.lean
import Mathlib
import Definitions.Def_Bridges_ModularScatteringDuality

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

open ModularScatteringDuality

/-! ## Core Definitions -/


variable {R : Type*} {X : Type*} {C : Type*}









/-! ## Resonance Congruence Properties -/


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


/-! ## Morphism Properties -/


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


/-! ## Spectral Boundary Construction -/


variable {R : Type*} {X : Type*} {C : Type*}

/-
Shift of a response profile remains in the range of response profiles.
This is because shifting corresponds to applying one step of transfer.
-/


/-
A surjective CSS morphism induces inclusion of spectral boundary profiles:
if `φ : S₁ → S₂` is surjective, then every response profile of `S₂` is also
a response profile of `S₁`.
-/


/-! ## Main Duality / Uniqueness Theorem -/


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


/-! ## Minimal Realization -/


variable {R : Type*} {X : Type*} {C : Type*}


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



open ModularScatteringDuality in
theorem solution    {X₁ X₂ : Type*}
    (S₁ : ClosureScatteringSystem R X₁ C)
    (S₂ : ClosureScatteringSystem R X₂ C)
    (hsep₁ : S₁.Separated)
    (hsep₂ : S₂.Separated)
    (hrange : Set.range S₁.responseProfile = Set.range S₂.responseProfile) :
    Nonempty (CSSIsomorphism S₁ S₂) := by
  -- Define the map $f : X₁ → X₂$ by $f(x) = y$ where $S₂.responseProfile y = S₁.responseProfile x$.
  have hf : ∀ x : X₁, ∃! y : X₂, S₂.responseProfile y = S₁.responseProfile x := by
    intro x
    obtain ⟨y, hy⟩ : ∃ y : X₂, S₂.responseProfile y = S₁.responseProfile x := by
      exact hrange.subset ( Set.mem_range_self x )
    use y
    aesop;
  choose f hf₁ hf₂ using hf;
  -- Show that $f$ is a morphism of closure-scattering systems.
  have hf_morphism : ∀ x : X₁, S₂.transfer (f x) = f (S₁.transfer x) ∧ ∀ c : C, S₁.boundary x c = S₂.boundary (f x) c := by
    intro x;
    refine' ⟨ hf₂ _ _ _, _ ⟩;
    · convert congr_arg ( fun f => fun n c => f ( n + 1 ) c ) ( hf₁ x ) using 1;
    · exact fun c => by simpa using congr_fun ( congr_fun ( hf₁ x ) 0 ) c |> Eq.symm;
  -- Show that $f$ is bijective.
  have hf_bijective : Function.Bijective f := by
    constructor;
    · intro x y hxy;
      exact hsep₁ ( by have := hf₁ x; have := hf₁ y; aesop );
    · intro y;
      obtain ⟨ x, hx ⟩ := hrange.symm.subset ( Set.mem_range_self y );
      exact ⟨ x, hf₂ x y hx.symm ▸ rfl ⟩;
  exact ⟨ ⟨ ⟨ f, fun x => hf_morphism x |>.1.symm, fun x c => hf_morphism x |>.2 c ⟩, hf_bijective ⟩ ⟩
