-- Prove2me | solution 1 for MultiversePMorphism.dot3_fails_buttons
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:46:58.889873+00:00
-- url     : https://prove2.me/submissions/d8f99a71-e13e-430b-9a46-41c75717033d

-- Sol generated from Logic/Multiverse/PMorphismTransfer.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_PMorphismTransfer
import Definitions.Def_Logic_Multiverse_S42Independence
import Theorems.Thm_S42Independence_msat_atom
import Theorems.Thm_S42Independence_msat_disj
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
theorem solution{Btn Sw : Type*} (b₁ b₂ : Btn) (hne : b₁ ≠ b₂)
    (g : Sw → Bool) :
    ¬ msat (cacc (Btn := Btn) (Sw := Sw))
        (fun a w => (if a then b₁ else b₂) ∈ w.1)
        (dot3F (.atom true) (.atom false)) ((∅ : Finset Btn), g) := by
  rw [dot3F, msat_disj]
  rintro (h | h)
  · have hb : msat (cacc (Btn := Btn) (Sw := Sw))
        (fun a w => (if a then b₁ else b₂) ∈ w.1) (.box (.atom true))
        (({b₁} : Finset Btn), g) := fun u hu => hu (Finset.mem_singleton_self b₁)
    have hq := h ({b₁}, g) (Finset.empty_subset _) hb
    simp only [msat_atom, if_neg (Bool.false_ne_true), Finset.mem_singleton] at hq
    exact hne hq.symm
  · have hb : msat (cacc (Btn := Btn) (Sw := Sw))
        (fun a w => (if a then b₁ else b₂) ∈ w.1) (.box (.atom false))
        (({b₂} : Finset Btn), g) := fun u hu => hu (Finset.mem_singleton_self b₂)
    have hq := h ({b₂}, g) (Finset.empty_subset _) hb
    simp only [msat_atom, Finset.mem_singleton] at hq
    exact hne hq
