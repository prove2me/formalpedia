-- Prove2me | Definitions.Def_Kourovka_Presentations_Presentations
-- name    : Kourovka_Presentations_Presentations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:40:31.474698+00:00
-- url     : https://prove2.me/theorems/d851b972-eb60-4d28-b2c0-c74430334f5f
-- title:
--   Presentations
-- statement:
--   Definitions and structural lemmas for Presentations, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/Presentations.lean

import Definitions.Def_Kourovka_Computability_Enumeration
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration
abbrev PresentationCode := ℕ × List (List (ℕ × Bool))
def WellFormed (p : PresentationCode) : Prop :=
  ∀ w ∈ p.2, ∀ letter ∈ w, letter.1 < p.1
def interpretWord (n : ℕ) (w : List (ℕ × Bool)) : FreeGroup (Fin n) :=
  (w.map fun letter => if h : letter.1 < n then
    if letter.2 then FreeGroup.of ⟨letter.1, h⟩ else (FreeGroup.of ⟨letter.1, h⟩)⁻¹
    else 1).prod
def relations (p : PresentationCode) : Set (FreeGroup (Fin p.1)) :=
  {r | r ∈ p.2.map (interpretWord p.1)}
def GroupOf (p : PresentationCode) := PresentedGroup (relations p)
instance (p : PresentationCode) : Group (GroupOf p) :=
  inferInstanceAs (Group (PresentedGroup (relations p)))
def Metabelian (G : Type*) [Group G] : Prop :=
  ∀ a b c d : G, Commute ⁅a, b⁆ ⁅c, d⁆
def decodePresentation (n : ℕ) : PresentationCode :=
  (Encodable.decode (α := PresentationCode) n).getD (0, [])
def DefinesMetabelian (n : ℕ) : Prop :=
  WellFormed (decodePresentation n) ∧ Metabelian (GroupOf (decodePresentation n))
def MainClaim : Prop := REPred DefinesMetabelian
end Kourovka.MetabelianEnumeration


