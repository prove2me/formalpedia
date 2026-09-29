-- Prove2me | Theorems.Thm_MultiversePMorphism_dot3_fails_buttons
-- name    : MultiversePMorphism.dot3_fails_buttons
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:40:24.621567+00:00
-- url     : https://prove2.me/theorems/252ead4e-944b-4a93-8412-e21055753e79
-- title:
--   The `.3` instance refuted by two independent buttons, for an arbitrary button
-- statement:
--   The `.3` instance refuted by two independent buttons, for an arbitrary button
--   type: the valuation reads the atom `true` as "button `b₁` pushed" and `false` as
--   "button `b₂` pushed".
--
--   ```lean
--   theorem MultiversePMorphism.dot3_fails_buttons{Btn Sw : Type*} (b₁ b₂ : Btn) (hne : b₁ ≠ b₂)
--       (g : Sw → Bool) :
--       ¬ msat (cacc (Btn := Btn) (Sw := Sw))
--           (fun a w => (if a then b₁ else b₂) ∈ w.1)
--           (dot3F (.atom true) (.atom false)) ((∅ : Finset Btn), g) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Multiverse/PMorphismTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Multiverse/PMorphismTransfer.lean#L161

-- Thm stub generated from Logic/Multiverse/PMorphismTransfer.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_PMorphismTransfer
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

open MultiversePMorphism

open BooleanValuedRealization S42Independence

variable {α W W' W'' : Type*}





/-! ## Switches are semantically free -/


variable {Btn Sw : Type*}








/-! ## Linearity is valid on total frames -/




/-! ## The logic of the control frame is strictly below the logic of its chains -/

theorem MultiversePMorphism.dot3_fails_buttons{Btn Sw : Type*} (b₁ b₂ : Btn) (hne : b₁ ≠ b₂)
    (g : Sw → Bool) :
    ¬ msat (cacc (Btn := Btn) (Sw := Sw))
        (fun a w => (if a then b₁ else b₂) ∈ w.1)
        (dot3F (.atom true) (.atom false)) ((∅ : Finset Btn), g) := by sorry
