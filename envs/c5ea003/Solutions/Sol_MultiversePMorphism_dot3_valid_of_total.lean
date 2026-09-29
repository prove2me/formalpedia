-- Prove2me | solution 1 for MultiversePMorphism.dot3_valid_of_total
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:48:23.121529+00:00
-- url     : https://prove2.me/submissions/0817b393-e00e-4529-81fd-41489db9a09f

-- Sol generated from Logic/Multiverse/PMorphismTransfer.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_PMorphismTransfer
import Definitions.Def_Logic_Multiverse_S42Independence
import Theorems.Thm_S42Independence_msat_box
import Theorems.Thm_S42Independence_msat_disj
import Theorems.Thm_S42Independence_msat_imp
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

open MultiversePMorphism

open BooleanValuedRealization S42Independence

variable {α W W' W'' : Type*}





/-! ## Switches are semantically free -/


variable {Btn Sw : Type*}








/-! ## Linearity is valid on total frames -/




/-! ## The logic of the control frame is strictly below the logic of its chains -/




open MultiversePMorphism in
theorem solution{R : W → W → Prop} (htot : ∀ x y, R x y ∨ R y x)
    (V : α → W → Prop) (p q : MForm α) (w : W) : msat R V (dot3F p q) w := by
  rw [dot3F, msat_disj]
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  simp only [msat_box, msat_imp] at h1 h2
  push_neg at h1 h2
  obtain ⟨v, hwv, hboxp, hnq⟩ := h1
  obtain ⟨u, hwu, hboxq, hnp⟩ := h2
  rcases htot v u with h | h
  · exact hnp (hboxp u h)
  · exact hnq (hboxq v h)
