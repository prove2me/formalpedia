-- Prove2me | Definitions.Def_Bridges_TropicalDuality
-- name    : Bridges_TropicalDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:15.721508+00:00
-- url     : https://prove2.me/theorems/1bf5062c-01f3-4eb5-8599-e8d9c4aa3fb4
-- title:
--   Aether Catalog definitions — Bridges_TropicalDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Gelfand Reconstruction on Finite T₀ Spaces

This file establishes a finite tropical analogue of the classical Gelfand duality /
Nullstellensatz: on a finite type `X` equipped with a function semiring `X → S`
(where `S` is a nontrivial commutative semiring with no zero divisors),
we prove:

1. **Kernel–support duality for idempotent KME**: The kernel of a weighted KME functional
   equals the vanishing ideal of its support (`ker_kme_eq_vanishing_support`).

2. **Support recovery**: The support of the vanishing ideal of a set `F` recovers `F`
   (`supportOfIdeal_vanishingIdeal`).

3. **Galois anti-isomorphism**: Subsets of `X` are in order-reversing bijection with
   support-stable geometric-radical ideals of `X → S`
   (`setIdealOrderAntiIso`).

These results form the algebraic-geometric backbone for reconstructing finite spaces
from algebras of tropical/idempotent observables.
-/


namespace TropicalDuality

/-! ## Setup and basic definitions -/

variable {X : Type*} {S : Type*}

section Definitions

variable [CommSemiring S]


/-- The vanishing ideal of a subset `F ⊆ X`: all functions that are zero on `F`. -/
def vanishingIdeal (F : Set X) : Ideal (X → S) where
  carrier := {f | ∀ x ∈ F, f x = 0}
  add_mem' := fun {f g} hf hg x hx => by simp [hf x hx, hg x hx]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun _ _ hf x hx => by simp [hf x hx]

/-- The support of an ideal: points where every function in the ideal vanishes. -/
def supportOfIdeal (I : Ideal (X → S)) : Set X :=
  {x | ∀ f ∈ I, f x = 0}

/-- An ideal is support-stable if it equals the vanishing ideal of its support. -/
def supportStable (I : Ideal (X → S)) : Prop :=
  vanishingIdeal (supportOfIdeal I) = I

/-- An ideal is geometrically radical if membership is determined by vanishing
on the support. -/
def geomRadical (I : Ideal (X → S)) : Prop :=
  ∀ f, (∀ x ∈ supportOfIdeal I, f x = 0) → f ∈ I


end Definitions

section KME

variable [Fintype X] [CommSemiring S] [SemilatticeSup S] [OrderBot S]

/-- The support of a weight function: points where the weight is nonzero. -/
def supportOfMeasure (w : X → S) : Set X := {x | w x ≠ ⊥}

/-- The weighted KME functional: computes `sup_x (w x * f x)`. -/
def kmeFromWeight (w : X → S) (f : X → S) : S :=
  Finset.sup Finset.univ (fun x => w x * f x)

/-- The kernel of a KME functional: functions mapped to ⊥. -/
def kmeKernel (w : X → S) : Set (X → S) := {f | kmeFromWeight w f = ⊥}

end KME

section MonotoneLemmas

variable [CommSemiring S]



/-- Any ideal is contained in the vanishing ideal of its support. -/
theorem le_vanishingIdeal_supportOfIdeal (I : Ideal (X → S)) :
    I ≤ vanishingIdeal (supportOfIdeal I) :=
  fun _ hf _ hx => hx _ hf

end MonotoneLemmas

section SupportRecovery

variable [DecidableEq X] [CommSemiring S] [Nontrivial S]

/-- Point indicator function: equals `1` at `x` and `0` elsewhere. -/
noncomputable def ptIndicator (x : X) : X → S :=
  fun y => if y = x then 1 else 0


omit [Nontrivial S] in
theorem ptIndicator_ne {x y : X} (h : y ≠ x) : ptIndicator (S := S) x y = 0 := by
  simp [ptIndicator, h]

omit [Nontrivial S] in
/-- The indicator of a point not in `F` belongs to the vanishing ideal of `F`. -/
theorem ptIndicator_mem_vanishingIdeal {x : X} {F : Set X} (hx : x ∉ F) :
    ptIndicator (S := S) x ∈ vanishingIdeal F := by
  intro y hy
  exact ptIndicator_ne (fun h => hx (h ▸ hy))

/-- **Support recovery**: The support of the vanishing ideal of `F` is exactly `F`. -/
theorem supportOfIdeal_vanishingIdeal (F : Set X) :
    supportOfIdeal (vanishingIdeal (S := S) F) = F := by
  ext x
  constructor
  · intro hx
    by_contra hxF
    have hmem := ptIndicator_mem_vanishingIdeal (S := S) hxF
    have := hx _ hmem
    simp [ptIndicator] at this
  · exact fun hx _ hf => hf x hx


end SupportRecovery

section IdealClassification

variable [CommSemiring S]

/-- `geomRadical` is equivalent to `supportStable`. -/
theorem geomRadical_iff_supportStable (I : Ideal (X → S)) :
    geomRadical I ↔ supportStable I := by
  constructor
  · exact fun h => le_antisymm (fun f hf => h f hf) (le_vanishingIdeal_supportOfIdeal I)
  · exact fun h f hf => h ▸ hf

variable [DecidableEq X] [Nontrivial S]

/-- Every vanishing ideal is support-stable. -/
theorem supportStable_vanishingIdeal (F : Set X) :
    supportStable (vanishingIdeal (S := S) F) := by
  unfold supportStable
  congr
  exact supportOfIdeal_vanishingIdeal F

/-- Every vanishing ideal is geometrically radical. -/
theorem geomRadical_vanishingIdeal (F : Set X) :
    geomRadical (vanishingIdeal (S := S) F) :=
  (geomRadical_iff_supportStable _).mpr (supportStable_vanishingIdeal F)

end IdealClassification

section KerKME

variable [Fintype X] [CommSemiring S] [SemilatticeSup S] [OrderBot S]
variable [NoZeroDivisors S]


end KerKME

section GaloisConnection

variable [DecidableEq X] [CommSemiring S] [Nontrivial S]

/-- Sets to support-stable ideals. -/
def setToIdeal : Set X → {I : Ideal (X → S) // supportStable I ∧ geomRadical I} :=
  fun F => ⟨vanishingIdeal F, supportStable_vanishingIdeal F, geomRadical_vanishingIdeal F⟩

/-- Support-stable ideals to sets. -/
def idealToSet : {I : Ideal (X → S) // supportStable I ∧ geomRadical I} → Set X :=
  fun I => supportOfIdeal I.1





end GaloisConnection

end TropicalDuality


