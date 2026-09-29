-- Prove2me | Definitions.Def_Logic_Multiverse_PMorphismTransfer
-- name    : Logic_Multiverse_PMorphismTransfer
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:59:31.432967+00:00
-- url     : https://prove2.me/theorems/bcb54ffe-7f13-4cac-aed5-b57b12855417
-- title:
--   Aether Catalog definitions — Logic_Multiverse_PMorphismTransfer
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Multiverse.PMorphismTransfer`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Multiverse/PMorphismTransfer.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_S42Independence
/-
# Bounded Morphisms and Transfer between Forcing Frames

A step towards the finite-frame completeness problem for the modal logic of
forcing.  We introduce **bounded morphisms** (p-morphisms) between Kripke frames,
prove the transfer theorem for the semantics of
`Catalog/Logic/Multiverse/S42Independence.lean`, and apply it to the finite
button–switch control frames:

* `msat_pmorphism` — truth is invariant along a bounded morphism;
* `validity_transfer` — validity is inherited by surjective bounded images, so the
  modal logic of a frame is contained in the logic of each of its images;
* `forgetSwitches` — forgetting the switches is a surjective bounded morphism onto
  the pure button order: **switches are semantically free**;
* `cardChain` — the cardinality map is a surjective bounded morphism from the
  `n`-button order onto the `(n+1)`-element chain, so every finite chain is a
  bounded image of a button frame;
* `dot3_valid_of_total` — the linearity axiom `.3` is valid on every total frame;
* `control_logic_strictly_below_chain` — combining the above with the refutation of
  `.3` on two independent buttons: the logic of the control frame is *strictly*
  contained in the logic of the chains it maps onto.
-/

namespace MultiversePMorphism

open BooleanValuedRealization S42Independence

variable {α W W' W'' : Type*}

/-- A **bounded morphism** (p-morphism) of Kripke frames. -/
structure PMorphism (R : W → W → Prop) (R' : W' → W' → Prop) where
  /-- The underlying map of worlds. -/
  toFun : W → W'
  /-- Accessibility is preserved. -/
  forth : ∀ {w v : W}, R w v → R' (toFun w) (toFun v)
  /-- Accessibility is reflected: every successor of an image is the image of a
  successor. -/
  back : ∀ {w : W} {u : W'}, R' (toFun w) u → ∃ v, R w v ∧ toFun v = u

/-- Composition of bounded morphisms. -/
def PMorphism.comp {R : W → W → Prop} {R' : W' → W' → Prop} {R'' : W'' → W'' → Prop}
    (g : PMorphism R' R'') (f : PMorphism R R') : PMorphism R R'' where
  toFun := g.toFun ∘ f.toFun
  forth := fun h => g.forth (f.forth h)
  back := by
    intro w u hu
    obtain ⟨v', hv', rfl⟩ := g.back hu
    obtain ⟨v, hv, rfl⟩ := f.back hv'
    exact ⟨v, hv, rfl⟩



/-! ## Switches are semantically free -/

section Frames

variable {Btn Sw : Type*}

/-- Forgetting the switches is a bounded morphism onto the pure button order. -/
def forgetSwitches :
    PMorphism (cacc (Btn := Btn) (Sw := Sw)) (fun S T : Finset Btn => S ⊆ T) where
  toFun := Prod.fst
  forth := id
  back := fun {w} {u} h => ⟨(u, w.2), h, rfl⟩


/-- The cardinality map is a bounded morphism from the `n`-button order onto the
`(n+1)`-element chain: every finite chain is a bounded image of a button frame. -/
def cardChain (n : ℕ) :
    PMorphism (fun S T : Finset (Fin n) => S ⊆ T) (fun i j : Fin (n + 1) => i ≤ j) where
  toFun := fun S => ⟨S.card, by
    have h := Finset.card_le_univ S
    simp only [Fintype.card_fin] at h
    omega⟩
  forth := fun {S T} h => Finset.card_le_card h
  back := by
    intro S u hu
    have h1 : S.card ≤ (u : ℕ) := hu
    have h2 : (u : ℕ) ≤ Fintype.card (Fin n) := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨T, hST, hT⟩ := Finset.exists_superset_card_eq h1 h2
    exact ⟨T, hST, by ext; simpa using hT⟩


/-- The composite bounded morphism from the full control frame onto a chain. -/
def controlToChain (n : ℕ) (Sw : Type*) :
    PMorphism (cacc (Btn := Fin n) (Sw := Sw)) (fun i j : Fin (n + 1) => i ≤ j) :=
  (cardChain n).comp forgetSwitches


end Frames

/-! ## Linearity is valid on total frames -/

/-- The linearity axiom `.3` for two formulas. -/
def dot3F (p q : MForm α) : MForm α :=
  MForm.disj (.box (.imp (.box p) q)) (.box (.imp (.box q) p))



/-! ## The logic of the control frame is strictly below the logic of its chains -/



end MultiversePMorphism


