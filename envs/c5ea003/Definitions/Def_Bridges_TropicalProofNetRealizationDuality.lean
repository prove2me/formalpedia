-- Prove2me | Definitions.Def_Bridges_TropicalProofNetRealizationDuality
-- name    : Bridges_TropicalProofNetRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:49.420129+00:00
-- url     : https://prove2.me/theorems/44d3c0cd-70d2-4985-81b6-747e42bac020
-- title:
--   Aether Catalog definitions — Bridges_TropicalProofNetRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalProofNetRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalProofNetRealizationDuality.lean by skeleton subtraction
import Mathlib
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

namespace TropicalProofNet

/-! ## §1. Basic Definitions: Weighted Consequence Systems -/

/-- A weighted Horn rule: from premises to a conclusion with a cost weight. -/
structure WeightedHornRule (F : Type*) (W : Type*) where
  premises : Finset F
  concl : F
  weight : W

/-- A weighted consequence system over a finite formula set `F` with costs in `W`.
    The closure operator maps cost valuations to derived cost valuations,
    satisfying extensiveness, monotonicity, and idempotency. -/
structure WeightedConsequenceSystem (F : Type*) (W : Type*)
    [Fintype F] [Preorder W] where
  /-- The underlying weighted Horn rules -/
  rules : Finset (WeightedHornRule F W)
  /-- Closure operator: maps cost valuations to derived cost valuations -/
  closure : (F → W) → (F → W)
  /-- Extensiveness: derived cost is at most the input cost -/
  extensive : ∀ x f, closure x f ≤ x f
  /-- Monotonicity: lower input costs yield lower derived costs -/
  monotone : ∀ ⦃x y : F → W⦄, (∀ f, x f ≤ y f) → ∀ f, closure x f ≤ closure y f
  /-- Idempotency: applying closure twice equals applying it once -/
  idempotent : ∀ x f, closure (closure x) f = closure x f
  /-- Algebraicity: closure is determined by compact/finite generators -/
  algebraic : Prop
  /-- Cut/exchange principle: derivation costs compose correctly -/
  cut_exchange : Prop

variable {F : Type*} {W : Type*}
variable [Fintype F] [DecidableEq F] [LinearOrder W] [OrderTop W] [OrderBot W]

/-! ## §2. Singleton Cost, Entailment Kernel, and Residual Equivalence -/

/-- The singleton cost function: assigns cost `⊥` (zero/identity) to formula `p`
    and `⊤` (infinity/absorbing) to all others. -/
def singletonCost (p : F) : F → W :=
  fun q => if q = p then ⊥ else ⊤



/-- The entailment kernel: `K(p,q)` is the minimal cost to derive `q`
    from the singleton premise `p`, computed by the closure operator. -/
def entailmentKernel
    (C : WeightedConsequenceSystem F W) (p q : F) : W :=
  C.closure (singletonCost p) q

/-- Residual equivalence: two formulas are residually equivalent when
    they have identical entailment profiles (rows of the kernel matrix). -/
def residualEq
    (C : WeightedConsequenceSystem F W) (p q : F) : Prop :=
  ∀ r : F, entailmentKernel C p r = entailmentKernel C q r

/-! ## §3. Residual Equivalence is an Equivalence Relation -/

theorem residualEq_refl (C : WeightedConsequenceSystem F W) (p : F) :
    residualEq C p p :=
  fun _ => rfl

theorem residualEq_symm (C : WeightedConsequenceSystem F W) {p q : F}
    (h : residualEq C p q) : residualEq C q p :=
  fun r => (h r).symm

theorem residualEq_trans (C : WeightedConsequenceSystem F W) {p q r : F}
    (hpq : residualEq C p q) (hqr : residualEq C q r) :
    residualEq C p r :=
  fun s => (hpq s).trans (hqr s)

/-- Residual equivalence forms an equivalence relation. -/
theorem residualEq_equivalence (C : WeightedConsequenceSystem F W) :
    Equivalence (residualEq C) :=
  ⟨residualEq_refl C,
   fun h => residualEq_symm C h,
   fun h1 h2 => residualEq_trans C h1 h2⟩

/-- The residual setoid on formulas. -/
def residualSetoid (C : WeightedConsequenceSystem F W) : Setoid F :=
  ⟨residualEq C, residualEq_equivalence C⟩


/-! ## §4. Quotient Type and Finiteness -/

/-- The residual quotient type: formulas identified by their entailment profiles. -/
def ResidualQuotient (C : WeightedConsequenceSystem F W) : Type _ :=
  Quotient (residualSetoid C)

/-- Residual equivalence is decidable when W has decidable equality. -/
instance residualEq_decidableRel [DecidableEq W]
    (C : WeightedConsequenceSystem F W) :
    DecidableRel (residualSetoid C).r :=
  fun _ _ => Fintype.decidableForallFintype

instance residualQuotient_finite [DecidableEq W]
    (C : WeightedConsequenceSystem F W) :
    Fintype (ResidualQuotient C) :=
  Quotient.fintype (residualSetoid C)

instance residualQuotient_decidableEq [DecidableEq W]
    (C : WeightedConsequenceSystem F W) :
    DecidableEq (ResidualQuotient C) :=
  inferInstance


/-! ## §5. Quotient Kernel -/


/-- Lifted kernel on the quotient (first argument). -/
def quotientKernel (C : WeightedConsequenceSystem F W) :
    ResidualQuotient C → F → W :=
  Quotient.lift (fun p q => entailmentKernel C p q)
    (fun _ _ h => funext (fun q => h q))


/-! ## §6. Injectivity of the Quotient Kernel -/


/-! ## §7. Entailment Kernel Properties -/




/-! ## §8. Derivation DAG Structure -/


variable {V V₁ V₂ : Type*}



/-! ## §9. Factorization Through the Canonical Quotient -/


/-! ## §10. Finite Tropical Rank -/

/-- Finite tropical rank: the number of distinct residual profiles is bounded. -/
def FiniteTropicalRank (K : F → F → W) : Prop :=
  ∃ n : ℕ, ∀ (S : Finset F),
    (∀ p q : F, p ∈ S → q ∈ S → p ≠ q → ∃ r, K p r ≠ K q r) →
    S.card ≤ n


/-! ## §11. The Main Duality Theorem -/


/-! ## §12. Composition and Cut Properties -/


/-! ## §13. Concrete Instance: ℕ∞ Tropical Semiring -/

/-- The natural-number-with-infinity type as a tropical weight. -/
abbrev NatInf := WithTop ℕ

/-- Example: identity closure on `Fin 2` with `NatInf` weights. -/
def exampleSystem : WeightedConsequenceSystem (Fin 2) NatInf where
  rules := ∅
  closure := fun x f => x f
  extensive := fun _ _ => le_refl _
  monotone := fun {_} {_} h f => h f
  idempotent := fun _ _ => rfl
  algebraic := True
  cut_exchange := True




/-! ## §14. Certified Reconstruction Theorem -/


/-! ## §15. Closure and Kernel Interaction -/



/-! ## §16. Residual Profile as Complete Invariant -/

/-- The residual profile function: maps each formula to its kernel row. -/
def residualProfile (C : WeightedConsequenceSystem F W) (p : F) : F → W :=
  fun q => entailmentKernel C p q



/-! ## §17. Summary Theorem -/


/-! ## §18. Kernel Monotonicity -/


/-! ## §19. Fixed Point Characterization -/


/-! ## §20. Uniqueness of the Fixed Point Structure -/


end TropicalProofNet


