-- Prove2me | Definitions.Def_Bridges_PosetTheory_MatroidCorrespondence
-- name    : Bridges_PosetTheory_MatroidCorrespondence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:11.507047+00:00
-- url     : https://prove2.me/theorems/20535b4e-fe0a-4277-a7b7-10af3ee3c1e3
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_MatroidCorrespondence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.MatroidCorrespondence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/MatroidCorrespondence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_MatroidMinorFiniteBasis
/-!
# Matroid correspondences as order-theoretic functors

A correspondence between quotient-ordered structures is encoded by a relation whose
fibres extend along the source order.  Universal inverse image then transports lower
classes contravariantly.  This isolates the categorical mechanism behind matroid
correspondences from any particular construction such as deletion or contraction.

The main results prove closure under composition, functoriality on lower classes,
preservation of arbitrary intersections, and an obstruction theorem for matroids.
-/

open Set

namespace MatroidCorrespondence

/-- An order correspondence from `α` to `β`.  The extension law says that a target
witness over a smaller source can be extended above it over every larger source. -/
structure OrderCorrespondence (α β : Type*) [Preorder α] [Preorder β] where
  rel : α → β → Prop
  extend : ∀ {a₀ a₁ b₀}, a₀ ≤ a₁ → rel a₀ b₀ → ∃ b₁, b₀ ≤ b₁ ∧ rel a₁ b₁

namespace OrderCorrespondence

variable {α β γ δ : Type*}
variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

/-- The identity correspondence. -/
def id (α : Type*) [Preorder α] : OrderCorrespondence α α where
  rel := (· = ·)
  extend h hab := ⟨_, hab ▸ h, rfl⟩

/-- Relational composition of order correspondences. -/
def comp (F : OrderCorrespondence α β) (G : OrderCorrespondence β γ) :
    OrderCorrespondence α γ where
  rel a c := ∃ b, F.rel a b ∧ G.rel b c
  extend ha h := by
    rcases h with ⟨b₀, hab₀, hbc₀⟩
    rcases F.extend ha hab₀ with ⟨b₁, hb, hab₁⟩
    rcases G.extend hb hbc₀ with ⟨c₁, hc, hbc₁⟩
    exact ⟨c₁, hc, b₁, hab₁, hbc₁⟩

/-- Universal inverse image of a class along a correspondence. -/
def pull (F : OrderCorrespondence α β) (C : Set β) : Set α :=
  {a | ∀ b, F.rel a b → b ∈ C}






end OrderCorrespondence

section MatroidObstructions

open Matroid MatroidMinorFiniteBasis

variable {α β : Type*}

/-- A matroid correspondence is an order correspondence for the minor orders. -/
abbrev MatroidCorr := OrderCorrespondence (Matroid α) (Matroid β)

/-- The minor correspondence relates a matroid to each of its minors. -/
def minorCorr (α : Type*) : MatroidCorr (α := α) (β := α) where
  rel M N := N ≤m M
  extend hMN hKN := ⟨_, hKN.trans hMN, Matroid.IsMinor.refl⟩




end MatroidObstructions

end MatroidCorrespondence

-- !-- Lab Notes -- !--
-- Hypothesis: the functorial core of matroid correspondence is an extension law
-- for a relation between quotient orders, rather than functionality of that relation.
-- Experiment: universal inverse image was tested against identity, relational
-- composition, arbitrary intersections, and excluded-minor extraction.
-- Analysis: existential direct image has the wrong variance for minor-closed classes;
-- universal inverse image is lower precisely because witnesses extend upward.
-- Critique: representability and Lorentzian support require additional algebraic data
-- and are not asserted here.  The results concern the quotient-order mechanism only.
-- Synthesis: correspondences form an associative relational calculus whose pullbacks
-- act contravariantly on lower classes and inherit finite obstruction bases under WQO.
-- !-- End Lab Notes -- !--


