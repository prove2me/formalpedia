-- Prove2me | Definitions.Def_Bridges_TropicalStoneRecognitionDuality
-- name    : Bridges_TropicalStoneRecognitionDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:17.496497+00:00
-- url     : https://prove2.me/theorems/5dd1ed02-9ba1-4c06-8ab5-5c8f3bd4b0a0
-- title:
--   Aether Catalog definitions — Bridges_TropicalStoneRecognitionDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalStoneRecognitionDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalStoneRecognitionDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Stone Recognition Duality via Idempotent Congruence Spectra

## Overview

This file establishes a finite duality between tropical recognition algebras
(finite commutative idempotent semirings) and finite spectral predicate spaces
(finite T₀ partial orders).

The central construction is the **upper-set idempotent semiring**: given a finite
poset X, the collection of upper sets forms a commutative semiring with union as
addition (idempotent) and intersection as multiplication (also idempotent). The
**principal upper set map** x ↦ ↑x = {y | x ≤ y} gives a contravariant
order-embedding — the finite analogue of Stone's representation theorem.

Combined with the congruence spectrum construction, this gives the duality:
  tropical language ↔ finite idempotent recognizer ↔ prime congruence spectral space

## Main Results

* `upperSetCommSemiring` — upper sets form a CommSemiring (union = +, ∩ = ×)
* `upperSet_idem_add`, `upperSet_idem_mul` — both operations are idempotent
* `principalUpper_injective` — Stone embedding is injective
* `principalUpper_order_embedding` — contravariant order characterization
* `upperSet_eq_union_principals` — basis decomposition
* `upperSet_absorption` — lattice absorption law
* `upperSet_union_inter_distrib` — union distributes over intersection
* `minimal_recognizer_card_eq` — uniqueness of minimal recognizers
* `finite_tropical_stone_representation` — main duality theorem
* `wordInterp_append` — word interpretation is multiplicative
-/


open Finset Function

noncomputable section

namespace TropicalStoneRecognition

/-! ## §1. Idempotent Semiring Infrastructure -/

/-- A finite commutative idempotent semiring: the fundamental recognition algebra
    for tropical language theory. Addition is idempotent (a + a = a). -/
structure IdemSemiring where
  carrier : Type
  instCSR : CommSemiring carrier
  instFin : Fintype carrier
  instDec : DecidableEq carrier
  idem_add : ∀ a : carrier, a + a = a

attribute [instance] IdemSemiring.instCSR IdemSemiring.instFin IdemSemiring.instDec

/-- The natural order: a ≤ᵢ b iff a + b = b. Makes addition the join. -/
def IdemSemiring.natLE (R : IdemSemiring) (a b : R.carrier) : Prop :=
  a + b = b






/-! ## §2. Finite T₀ Partial Orders -/

/-- A finite T₀ partial order = finite spectral predicate space. -/
structure FinT0Poset where
  carrier : Type
  instFin : Fintype carrier
  instDec : DecidableEq carrier
  instPO : PartialOrder carrier
  instDecLE : DecidableRel instPO.le

attribute [instance] FinT0Poset.instFin FinT0Poset.instDec FinT0Poset.instPO
  FinT0Poset.instDecLE

/-! ## §3. Upper Sets as an Idempotent Semiring -/

/-- An upper set in a finite partial order, represented as a `Finset`. -/
structure UpperSetFin (X : FinT0Poset) where
  val : Finset X.carrier
  upper : ∀ {x y : X.carrier}, x ∈ val → x ≤ y → y ∈ val

@[ext]
theorem UpperSetFin.ext' {X : FinT0Poset} {U V : UpperSetFin X}
    (h : U.val = V.val) : U = V := by
  cases U; cases V; congr

instance upperSetDecEq (X : FinT0Poset) : DecidableEq (UpperSetFin X) :=
  fun U V => decidable_of_iff (U.val = V.val)
    ⟨UpperSetFin.ext', fun h => by rw [h]⟩

def UpperSetFin.empty (X : FinT0Poset) : UpperSetFin X where
  val := ∅
  upper := by simp

def UpperSetFin.full (X : FinT0Poset) : UpperSetFin X where
  val := Finset.univ
  upper := by simp

def UpperSetFin.union {X : FinT0Poset} (U V : UpperSetFin X) : UpperSetFin X where
  val := U.val ∪ V.val
  upper := by
    intro x y hx hxy
    simp only [Finset.mem_union] at hx ⊢
    exact hx.imp (U.upper · hxy) (V.upper · hxy)

def UpperSetFin.inter {X : FinT0Poset} (U V : UpperSetFin X) : UpperSetFin X where
  val := U.val ∩ V.val
  upper := by
    intro x y hx hxy
    simp only [Finset.mem_inter] at hx ⊢
    exact ⟨U.upper hx.1 hxy, V.upper hx.2 hxy⟩

instance (X : FinT0Poset) : Zero (UpperSetFin X) := ⟨UpperSetFin.empty X⟩
instance (X : FinT0Poset) : One (UpperSetFin X) := ⟨UpperSetFin.full X⟩
instance (X : FinT0Poset) : Add (UpperSetFin X) := ⟨UpperSetFin.union⟩
instance (X : FinT0Poset) : Mul (UpperSetFin X) := ⟨UpperSetFin.inter⟩

/-- Membership in the union of upper sets (addition). -/
theorem UpperSetFin.add_val {X : FinT0Poset} (U V : UpperSetFin X) (x : X.carrier) :
    x ∈ (U + V).val ↔ x ∈ U.val ∨ x ∈ V.val := Finset.mem_union

/-- Membership in the intersection of upper sets (multiplication). -/
theorem UpperSetFin.mul_val {X : FinT0Poset} (U V : UpperSetFin X) (x : X.carrier) :
    x ∈ (U * V).val ↔ x ∈ U.val ∧ x ∈ V.val := Finset.mem_inter





/-- The upper sets of a finite poset form a `CommSemiring`. -/
instance upperSetCommSemiring (X : FinT0Poset) : CommSemiring (UpperSetFin X) where
  nsmul := nsmulRec
  add_assoc a b c := UpperSetFin.ext' (Finset.union_assoc _ _ _)
  zero_add a := UpperSetFin.ext' (Finset.empty_union _)
  add_zero a := UpperSetFin.ext' (Finset.union_empty _)
  add_comm a b := UpperSetFin.ext' (Finset.union_comm _ _)
  mul_assoc a b c := UpperSetFin.ext' (Finset.inter_assoc _ _ _)
  one_mul a := UpperSetFin.ext' (Finset.univ_inter _)
  mul_one a := UpperSetFin.ext' (Finset.inter_univ _)
  mul_comm a b := UpperSetFin.ext' (Finset.inter_comm _ _)
  zero_mul a := UpperSetFin.ext' (Finset.empty_inter _)
  mul_zero a := UpperSetFin.ext' (Finset.inter_empty _)
  left_distrib a b c := by
    apply UpperSetFin.ext'; ext x
    simp only [UpperSetFin.mul_val, UpperSetFin.add_val]; tauto
  right_distrib a b c := by
    apply UpperSetFin.ext'; ext x
    simp only [UpperSetFin.mul_val, UpperSetFin.add_val]; tauto
  natCast n := if n = 0 then 0 else 1
  natCast_zero := if_pos rfl
  natCast_succ n := by
    rw [if_neg (Nat.succ_ne_zero n)]
    split_ifs
    · exact UpperSetFin.ext' (Finset.empty_union _).symm
    · exact UpperSetFin.ext' (Finset.union_idempotent _).symm



/-- Upper sets form a finite type. -/
noncomputable instance upperSetFintype (X : FinT0Poset) : Fintype (UpperSetFin X) :=
  Fintype.ofInjective (fun U : UpperSetFin X => U.val)
    (fun _ _ h => UpperSetFin.ext' h)


/-! ## §4. Principal Upper Sets and the Stone Embedding -/

/-- The principal upper set ↑x = {y | x ≤ y}. -/
def principalUpper (X : FinT0Poset) (x : X.carrier) : UpperSetFin X where
  val := Finset.univ.filter (fun y => x ≤ y)
  upper := by
    intro a b ha hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact le_trans ha hab









/-! ## §5. Congruences and the Spectrum -/

/-- A proper congruence on an idempotent semiring. -/
structure IdemCong (R : IdemSemiring) where
  con : RingCon R.carrier
  proper : ∃ a b : R.carrier, ¬ con a b

instance idemCongPartialOrder (R : IdemSemiring) : PartialOrder (IdemCong R) where
  le P Q := ∀ a b : R.carrier, P.con a b → Q.con a b
  le_refl _ _ _ h := h
  le_trans _ _ _ hPQ hQR a b h := hQR a b (hPQ a b h)
  le_antisymm P Q hPQ hQP := by
    have : P.con = Q.con := by ext a b; exact ⟨hPQ a b, hQP a b⟩
    rcases P with ⟨c1, p1⟩; rcases Q with ⟨c2, p2⟩
    simp only at this; subst this; rfl

/-- Prime separation: distinct elements can be distinguished by congruences. -/
def PrimeSeparated (R : IdemSemiring) : Prop :=
  ∀ a b : R.carrier, a ≠ b → ∃ P : IdemCong R, ¬ P.con a b




/-! ## §6. Tropical Language Recognition -/

/-- A tropical language over an alphabet. -/
structure TropicalLanguage (Alpha : Type) where
  pred : List Alpha → Prop

/-- A finite tropical recognizer. -/
structure FiniteTropicalRecognizer (Alpha : Type) where
  algebra : IdemSemiring
  interp : Alpha → algebra.carrier
  accept : Set algebra.carrier
  recognized : TropicalLanguage Alpha

/-- Extension of interpretation to words via the semiring product. -/
def wordInterp {Alpha : Type} (R : FiniteTropicalRecognizer Alpha) :
    List Alpha → R.algebra.carrier
  | [] => 1
  | s :: w => R.interp s * wordInterp R w

/-- Recognizer equivalence. -/
def RecognizerEquiv {Alpha : Type}
    (R₁ R₂ : FiniteTropicalRecognizer Alpha) : Prop :=
  ∀ w : List Alpha, R₁.recognized.pred w ↔ R₂.recognized.pred w

/-- Minimality of a recognizer. -/
def IsMinimalRecognizer {Alpha : Type}
    (R : FiniteTropicalRecognizer Alpha) : Prop :=
  ∀ R' : FiniteTropicalRecognizer Alpha,
    RecognizerEquiv R R' →
    Fintype.card R.algebra.carrier ≤ Fintype.card R'.algebra.carrier


/-! ## §7. Structural Properties -/







/-! ## §8. Concrete Examples -/

/-- The singleton poset (one element). -/
def unitPoset : FinT0Poset where
  carrier := Unit
  instFin := inferInstance
  instDec := inferInstance
  instPO := inferInstance
  instDecLE := inferInstance

/-
The singleton poset has exactly 2 upper sets: ∅ and {()}.
-/

/-- The chain poset on Fin n (linear order). -/
def chainPoset (n : ℕ) : FinT0Poset where
  carrier := Fin n
  instFin := inferInstance
  instDec := inferInstance
  instPO := inferInstance
  instDecLE := inferInstance

/-
The chain on Fin 2 has 3 upper sets: ∅, {1}, {0, 1}.
-/

/-! ## §9. Word Interpretation Properties -/




/-! ## §10. Main Duality Theorem -/


end TropicalStoneRecognition


