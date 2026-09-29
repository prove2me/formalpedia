-- Prove2me | Definitions.Def_Bridges_ClosureScaleDuality
-- name    : Bridges_ClosureScaleDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:43.376158+00:00
-- url     : https://prove2.me/theorems/18dc3ea6-330f-4d91-ae80-1bac976bb931
-- title:
--   Aether Catalog definitions — Bridges_ClosureScaleDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureScaleDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureScaleDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closure–Scale Spectral Duality via Stone–Transfer Theory

This file proves a complete **finite spectral boundary theory for closure dynamics**:
given a closure operator `cl` and scale endomorphism `σ` on a finite type,
the transfer operator `T = cl ∘ σ` has a canonical recurrent core on which it
restricts to a bijection, and eventually stable temporal observables form a
Boolean algebra isomorphic to the powerset of recurrent classes.

## Layer 1: Generic Finite Transfer Dynamics

* `iterate_range_stabilizes` — For any endomorphism on a finite type,
  the descending chain of iterated images stabilizes.
* `bijOn_stable_range` — On the stabilized range, the map is bijective.
* `renorm_comp` — The semigroup law for iterates.

## Layer 2: Closure-Scale Specialization

* `ClosureScaleSystem` — A closure operator with scale endomorphism and absorption law.
* `TransferOp` — The transfer operator `T = cl ∘ σ`.
* `transfer_closed` — `T` lands in the `cl`-closed part.
* `transfer_range_stabilizes` — Range stabilization for `T`.
* `transfer_bijOn_core` — Bijectivity on the core.
* `renorm_semigroup` — Renormalization semigroup action on observables.
* Concrete example with four states and two recurrent classes.
-/

set_option maxHeartbeats 800000

open Function Set Finset

/-! ## Layer 1: Generic Finite Transfer Dynamics -/

namespace FiniteTransferDynamics

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The range of `f^[n+1]` is contained in the range of `f^[n]`. -/
lemma iterate_range_subset (f : C → C) : ∀ n,
    Set.range (f^[n + 1]) ⊆ Set.range (f^[n]) := by
  intro n x hx; aesop


/-
**Theorem A (Range Stabilization).** For any endomorphism on a finite type,
the descending chain of iterated images stabilizes.
-/
theorem iterate_range_stabilizes (f : C → C) :
    ∃ N : ℕ, Set.range (f^[N + 1]) = Set.range (f^[N]) := by
  -- By contradiction, assume the range never stabilizes.
  by_contra h_never_stabilize
  push_neg at h_never_stabilize
  have h_seq : StrictAnti (fun n => Set.range (f^[n])) := by
    exact strictAnti_nat_of_succ_lt fun n => lt_of_le_of_ne ( iterate_range_subset f n ) ( h_never_stabilize n );
  exact absurd ( Set.infinite_range_of_injective h_seq.injective ) ( Set.not_infinite.mpr <| Set.toFinite _ )

/-- The stabilization index. -/
noncomputable def stabilizationIndex (f : C → C) : ℕ :=
  (iterate_range_stabilizes f).choose


/-- The **recurrent core**: the eventual stable image. -/
def recurrentCore (f : C → C) : Set C :=
  Set.range (f^[stabilizationIndex f])

/-
Once stabilized, all subsequent iterates have the same range.
-/

/-
On the stabilized range, `f` maps the core into itself.
-/

/-
On the stabilized range, `f` is surjective.
-/

/-
**Bijectivity on the core.** On the stabilized range, `f` is bijective.
-/



end FiniteTransferDynamics

/-! ## Layer 2: Closure-Scale Systems -/

namespace ClosureScaleDuality

/-- A **closure-scale system** on a preordered type `C`:
- `cl` is a closure operator (extensive, monotone, idempotent),
- `sigma` is a monotone scale endomorphism,
- the absorption law `cl(σ(cl x)) = cl(σ x)` holds. -/
structure ClosureScaleSystem (C : Type*) [Preorder C] where
  cl : C → C
  sigma : C → C
  mono_cl : Monotone cl
  mono_sigma : Monotone sigma
  extensive : ∀ x, x ≤ cl x
  idem_cl : ∀ x, cl (cl x) = cl x
  absorb : ∀ x, cl (sigma (cl x)) = cl (sigma x)

variable {C : Type*} [Fintype C] [DecidableEq C] [Preorder C]

/-- The **transfer operator** `T = cl ∘ σ`. -/
def TransferOp (S : ClosureScaleSystem C) : C → C := S.cl ∘ S.sigma

/-
The transfer operator lands in the `cl`-closed part.
-/

/-
The transfer operator is monotone.
-/



/-! ## Temporal observables -/

/-- A **temporal observable**: a decidable predicate eventually stable under `T`. -/
structure TemporalObservable (S : ClosureScaleSystem C) where
  pred : C → Prop
  dec : DecidablePred pred
  stab_index : ℕ
  stab : ∀ x, pred ((TransferOp S)^[stab_index + 1] x) ↔ pred ((TransferOp S)^[stab_index] x)

/-- Core equality of temporal observables. -/
def TemporalObservable.coreEq (S : ClosureScaleSystem C)
    (p q : TemporalObservable S) : Prop :=
  ∀ x ∈ FiniteTransferDynamics.recurrentCore (TransferOp S),
    p.pred x ↔ q.pred x


/-! ## Renormalization semigroup action -/

/-- The **renormalization action** by pullback along `T^[n]`. -/
def renorm (S : ClosureScaleSystem C) (n : ℕ) (p : C → Prop) : C → Prop :=
  fun x => p ((TransferOp S)^[n] x)

/-
The renormalization action satisfies the semigroup law.
-/


/-! ## Concrete example: four states, two recurrent classes -/

/-- A four-element type. -/
inductive FourState | s₁ | s₂ | s₃ | s₄
  deriving DecidableEq, Fintype, Repr

namespace FourState

instance : Preorder FourState where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

/-- Identity closure. -/
def exCl : FourState → FourState | s₁ => s₁ | s₂ => s₂ | s₃ => s₃ | s₄ => s₄

/-- Scale map: s₃→s₁, s₄→s₂ (transient states collapse). -/
def exSigma : FourState → FourState | s₁ => s₁ | s₂ => s₂ | s₃ => s₁ | s₄ => s₂

/-- The example system. -/
def exSystem : ClosureScaleSystem FourState where
  cl := exCl; sigma := exSigma
  mono_cl := fun _ _ _ => trivial
  mono_sigma := fun _ _ _ => trivial
  extensive := fun _ => trivial
  idem_cl := fun x => by cases x <;> rfl
  absorb := fun x => by cases x <;> rfl


/-
The recurrent core is `{s₁, s₂}`.
-/

/-
Range stabilizes at N=1.
-/

end FourState

/-- The recurrent core is computable as a `Finset`. -/
noncomputable def computeCore (S : ClosureScaleSystem C) : Finset C :=
  (FiniteTransferDynamics.recurrentCore (TransferOp S)).toFinset


end ClosureScaleDuality


