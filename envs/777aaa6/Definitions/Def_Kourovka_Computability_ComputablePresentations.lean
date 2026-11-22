-- Prove2me | Definitions.Def_Kourovka_Computability_ComputablePresentations
-- name    : Kourovka_Computability_ComputablePresentations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:42:27.14337+00:00
-- url     : https://prove2.me/theorems/feba3410-cf29-4bd6-905b-3a0dc87a45f8
-- title:
--   Computable Presentations
-- statement:
--   Definitions and structural lemmas for Computable Presentations, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean

import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
def naturalRelators (p : PresentationCode) : List (FreeGroup ℕ) := p.2.map FreeGroup.mk
def restrictGenerators (n : ℕ) : FreeGroup ℕ →* FreeGroup (Fin n) :=
  FreeGroup.lift fun i => if h : i < n then FreeGroup.of ⟨i, h⟩ else 1
def includeGenerators (n : ℕ) : FreeGroup (Fin n) →* FreeGroup ℕ :=
  FreeGroup.lift fun i => FreeGroup.of i.1
def validInput (input : PresentationCode × List (ℕ × Bool)) : Prop :=
  WellFormed input.1 ∧ ∀ letter ∈ input.2, letter.1 < input.1.1
instance : DecidablePred validInput := fun input =>
  inferInstanceAs (Decidable ((∀ w ∈ input.1.2, ∀ l ∈ w, l.1 < input.1.1) ∧
    ∀ l ∈ input.2, l.1 < input.1.1))
def checkTrivial (input : PresentationCode × List (ℕ × Bool)) (certificate : ℕ) : Bool :=
  decide (validInput input) &&
    ComputableClosure.checkNat (naturalRelators input.1, FreeGroup.mk input.2) certificate
end Kourovka.MetabelianEnumeration.ComputablePresentations


