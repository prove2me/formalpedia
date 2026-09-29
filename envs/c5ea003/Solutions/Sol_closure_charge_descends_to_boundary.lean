-- Prove2me | solution 1 for closure_charge_descends_to_boundary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:04:27.379575+00:00
-- url     : https://prove2.me/submissions/3ce45608-5046-47e9-9842-23d8693e5fc6

-- Sol generated from Bridges/IdempotentHolographicRealization.lean
import Mathlib
import Definitions.Def_Bridges_IdempotentHolographicRealization

/-!
# Idempotent Holographic Realization via Closure Boundary Semimodules

This file establishes a **bulk–boundary duality theorem** for idempotent computational
systems over commutative semirings, formalizing the principle that boundary observables
plus closure-compatible response data determine the bulk uniquely, minimally, and
canonically.

## Overview

Given a holographic system consisting of:
- A closure operator `c` on a type `X` of bulk states,
- A finite alphabet `Act` of actions with transition maps `T : Act → (X → X)`,
- A boundary observation kernel `K : B → X → S`,
- Boundary probes `xprobe : B → X`,

we define the **boundary response series** and the **closure-refined history equivalence**
(an idempotent Myhill–Nerode relation). The main theorem shows that when the boundary
Hankel rank is finite, the quotient by this equivalence yields a canonical minimal
realization that is unique up to unique isomorphism.

A second theorem shows that **closure-conserved charges** (Noether-style invariants)
descend uniquely to the boundary quotient.

## Application Keywords
tropical Hankel realization, idempotent automata, closure nucleus, EML semantics,
bulk-boundary duality, holographic computation, Myhill-Nerode over semirings,
certified system identification, boundary observability, Noether invariants,
explainable latent states, finite reconstruction, semiring control,
tropical signal processing, categorical holography
-/

open scoped Classical

noncomputable section

/-! ## §1: Closure Operators and Basic Definitions -/








/-! ## §2: Holographic System Structure -/


variable {S : Type*} {Act : Type*} {B : Type*} {X : Type*} [CommSemiring S]

open HolographicSystem










/-! ## §3: Finite Closure Hankel Rank -/


/-! ## §4: The Canonical Minimal Realization -/



/-! ## §5: Quotient Operations -/









/-! ## §6: Main Reconstruction Theorem -/



/-! ## §7: Closure Charge Descent -/





/-! ## §8: Boundary Descent Preserves Charge Structure -/



/-! ## §9: Closure-Compatible Boundary Response Lemma

The boundary response is invariant when we apply closure to the intermediate state.
This is the key compatibility that makes the holographic quotient well-defined. -/


/-! ## §10: Connection to Existing Catalog Results

The `entropy_bound_state_space` theorem from `Bridges/ByzantineCertificate.lean`
provides certified finite-state complexity bounds. In our framework, finite
closure Hankel rank gives a certified upper bound on the number of distinguishable
boundary states, which is the analogue of an entropy bound on the reconstructible
bulk state space.

The `post_quantum_closure_hash_stable` results provide closure-stability under
observational hashing, supporting our claim that the boundary equivalence
relation is stable under closure-compatible compression.

These connections motivate viewing our holographic reconstruction as a
**certified system identification** procedure where boundary complexity
bounds the size of the reconstructible bulk.
-/


theorem solution    {S Act B X Xmin : Type*}
    [CommSemiring S]
    (R : HolographicRealizationData S Act B X Xmin)
    (ch : ClosureCharge S R.c R.T)
    (hdet : ch.IsBoundaryDetectable R.K)
    (hc_idem : ∀ x, R.c (R.c x) = R.c x) :
    ∃! Qbd : Xmin → S,
      (∀ x, Qbd (R.proj x) = ch.Q (R.c x)) ∧
      (∀ a z, Qbd (R.Tmin a z) = Qbd z) := by
  -- The charge is well-defined on the quotient because proj identifies
  -- kernel-indistinguishable states, and the charge is boundary-detectable.
  have well_def : ∀ x y, R.proj x = R.proj y → ch.Q (R.c x) = ch.Q (R.c y) := by
    intro x y hxy
    have hsep := R.proj_sep x y hxy
    exact hdet (R.c x) (R.c y) (hc_idem x) (hc_idem y) hsep
  -- Construct Qbd using the surjective inverse of proj
  have hinv := Function.surjInv_eq R.proj_surj
  let Qbd : Xmin → S := fun z => ch.Q (R.c (Function.surjInv R.proj_surj z))
  refine ⟨Qbd, ⟨?_, ?_⟩, ?_⟩
  · -- (1) Qbd agrees with Q ∘ c on projected states
    intro x
    exact well_def _ _ (hinv (R.proj x))
  · -- (2) Qbd is invariant under Tmin
    intro a z
    obtain ⟨x, rfl⟩ := R.proj_surj z
    show ch.Q (R.c (Function.surjInv R.proj_surj (R.Tmin a (R.proj x)))) =
         ch.Q (R.c (Function.surjInv R.proj_surj (R.proj x)))
    rw [← R.proj_tr a x]
    have h1 := well_def _ _ (hinv (R.proj (R.T a x)))
    have h2 := well_def _ _ (hinv (R.proj x))
    rw [h1, h2]
    exact ch.transition_inv a x
  · -- (3) Uniqueness: any other function satisfying the same spec must equal Qbd
    intro Qbd' ⟨hspec', _⟩
    funext z
    obtain ⟨x, rfl⟩ := R.proj_surj z
    rw [hspec']
    exact (well_def _ _ (hinv (R.proj x))).symm
