-- Prove2me | Theorems.Thm_MultiversePMorphism_msat_pmorphism
-- name    : MultiversePMorphism.msat_pmorphism
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:40:45.497845+00:00
-- url     : https://prove2.me/theorems/735e7cae-9f66-4ebe-ac8f-dcd82d7bc4a7
-- title:
--   Transfer theorem.
-- statement:
--   **Transfer theorem.**  A modal formula holds at a world iff it holds at its
--   image under a bounded morphism, for the pulled-back valuation.
--
--   ```lean
--   theorem MultiversePMorphism.msat_pmorphism{R : W → W → Prop} {R' : W' → W' → Prop}
--       (f : PMorphism R R') (V' : α → W' → Prop) (p : MForm α) (w : W) :
--       msat R (fun a x => V' a (f.toFun x)) p w ↔ msat R' V' p (f.toFun w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Multiverse/PMorphismTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Multiverse/PMorphismTransfer.lean#L51

-- Thm stub generated from Logic/Multiverse/PMorphismTransfer.lean
import Mathlib
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

theorem MultiversePMorphism.msat_pmorphism{R : W → W → Prop} {R' : W' → W' → Prop}
    (f : PMorphism R R') (V' : α → W' → Prop) (p : MForm α) (w : W) :
    msat R (fun a x => V' a (f.toFun x)) p w ↔ msat R' V' p (f.toFun w) := by sorry
