-- Prove2me | Theorems.Thm_MultiversePMorphism_control_logic_strictly_below_chain
-- name    : MultiversePMorphism.control_logic_strictly_below_chain
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:02.828586+00:00
-- url     : https://prove2.me/theorems/c539c1a9-1141-4e0a-a9ba-0a6a4926832e
-- title:
--   Strict containment.
-- statement:
--   **Strict containment.**  The modal logic of the `n`-button control frame
--   (`n ≥ 2`) is contained in the logic of the `(n+1)`-chain, and the containment is
--   strict: the linearity axiom `.3` is valid on the chain but refuted on the frame.
--   The bounded morphism `controlToChain` therefore cannot be inverted, and no
--   linearity principle can be added to the logic of forcing.
--
--   ```lean
--   theorem MultiversePMorphism.control_logic_strictly_below_chain(n : ℕ) (hn : 2 ≤ n) (Sw : Type*) :
--       (∀ p : MForm Bool,
--           (∀ (V : Bool → CWorld (Fin n) Sw → Prop) (w : CWorld (Fin n) Sw),
--               msat cacc V p w) →
--           ∀ (V' : Bool → Fin (n + 1) → Prop) (i : Fin (n + 1)), msat (· ≤ ·) V' p i) ∧
--       (∃ p : MForm Bool,
--           (∀ (V' : Bool → Fin (n + 1) → Prop) (i : Fin (n + 1)), msat (· ≤ ·) V' p i) ∧
--           ¬ ∀ (V : Bool → CWorld (Fin n) Sw → Prop) (w : CWorld (Fin n) Sw),
--               msat cacc V p w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Multiverse/PMorphismTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Multiverse/PMorphismTransfer.lean#L184

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

theorem MultiversePMorphism.control_logic_strictly_below_chain(n : ℕ) (hn : 2 ≤ n) (Sw : Type*) :
    (∀ p : MForm Bool,
        (∀ (V : Bool → CWorld (Fin n) Sw → Prop) (w : CWorld (Fin n) Sw),
            msat cacc V p w) →
        ∀ (V' : Bool → Fin (n + 1) → Prop) (i : Fin (n + 1)), msat (· ≤ ·) V' p i) ∧
    (∃ p : MForm Bool,
        (∀ (V' : Bool → Fin (n + 1) → Prop) (i : Fin (n + 1)), msat (· ≤ ·) V' p i) ∧
        ¬ ∀ (V : Bool → CWorld (Fin n) Sw → Prop) (w : CWorld (Fin n) Sw),
            msat cacc V p w) := by sorry
