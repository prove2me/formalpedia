-- Prove2me | solution 1 for TropicalProofNet.identity_closure_residualEq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:30.628351+00:00
-- url     : https://prove2.me/submissions/d9000f4c-4cb0-44c7-86e5-1f34bf130f51

-- Sol generated from Bridges/TropicalProofNetRealizationDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalProofNetRealizationDuality
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Proof-Net Realization Duality via Idempotent Consequence Semimodules

This file establishes a **finite realization duality theorem** for weighted
consequence systems over linearly ordered types, with primary application
to tropical (min-plus) semirings.

## Core Idea

Given a finite formula set `F` and a weighted consequence system with closure
operator `C`, the **entailment kernel** `K(p,q) = C(δ_p)(q)` records the
minimal cost to derive `q` from singleton premise `p`. Two formulas are
**residually equivalent** when they have identical entailment profiles.

The main theorem establishes:
1. Residual equivalence is a decidable equivalence relation (setoid).
2. The quotient by residual equivalence is finite.
3. The quotient kernel is injective (distinct classes have distinct profiles).
4. Any equiv-compatible map factors through the quotient.
5. Self-entailment cost is `⊥` (free / zero in tropical).

This is a **Myhill–Nerode theorem for weighted proof systems**.

## Main Results

* `residualEq_equivalence` — Residual equivalence is an equivalence relation
* `quotientKernel_injective` — Quotient kernel is injective (separation)
* `entailmentKernel_self` — Self-entailment is free
* `tropical_proofnet_realization_duality` — The main duality theorem
* `certified_reconstruction_from_entailment_kernel` — Reconstruction theorem
* `identity_closure_residualEq_iff` — Residual eq = eq for identity closure
* `exampleSystem_not_residualEq` — Concrete non-equivalence example
* `profile_factors_through_quotient` — Profile factors through quotient
-/


set_option maxHeartbeats 400000

open Finset Function Classical

noncomputable section

open TropicalProofNet

/-! ## §1. Basic Definitions: Weighted Consequence Systems -/



variable {F : Type*} {W : Type*}
variable [Fintype F] [DecidableEq F] [LinearOrder W] [OrderTop W] [OrderBot W]

/-! ## §2. Singleton Cost, Entailment Kernel, and Residual Equivalence -/






/-! ## §3. Residual Equivalence is an Equivalence Relation -/







/-! ## §4. Quotient Type and Finiteness -/






/-! ## §5. Quotient Kernel -/




/-! ## §6. Injectivity of the Quotient Kernel -/


/-! ## §7. Entailment Kernel Properties -/




/-! ## §8. Derivation DAG Structure -/


variable {V V₁ V₂ : Type*}



/-! ## §9. Factorization Through the Canonical Quotient -/


/-! ## §10. Finite Tropical Rank -/



/-! ## §11. The Main Duality Theorem -/


/-! ## §12. Composition and Cut Properties -/


/-! ## §13. Concrete Instance: ℕ∞ Tropical Semiring -/






/-! ## §14. Certified Reconstruction Theorem -/


/-! ## §15. Closure and Kernel Interaction -/



/-! ## §16. Residual Profile as Complete Invariant -/




/-! ## §17. Summary Theorem -/


/-! ## §18. Kernel Monotonicity -/


/-! ## §19. Fixed Point Characterization -/


/-! ## §20. Uniqueness of the Fixed Point Structure -/



open TropicalProofNet in
theorem solution[Nontrivial W]
    (C : WeightedConsequenceSystem F W)
    (hid : ∀ x f, C.closure x f = x f) (p q : F) :
    residualEq C p q ↔ p = q := by
  constructor
  · intro h
    by_contra hne
    have hp := h p
    unfold entailmentKernel at hp
    rw [hid, hid] at hp
    simp [singletonCost, hne] at hp
    have hsub : Subsingleton W := by
      constructor; intro a b
      have ha : a ≤ ⊥ := hp ▸ le_top
      have hb : b ≤ ⊥ := hp ▸ le_top
      exact le_antisymm (ha.trans bot_le) (hb.trans bot_le)
    exact not_subsingleton W hsub
  · rintro rfl
    exact residualEq_refl C p
