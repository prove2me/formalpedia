-- Prove2me | solution 1 for MultiversePMorphism.msat_pmorphism
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:48:23.625797+00:00
-- url     : https://prove2.me/submissions/202a81c8-5713-4fdd-a14a-31dbdef44eea

-- Sol generated from Logic/Multiverse/PMorphismTransfer.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_PMorphismTransfer
import Definitions.Def_Logic_Multiverse_S42Independence
import Theorems.Thm_S42Independence_msat_box
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
theorem solution{R : W → W → Prop} {R' : W' → W' → Prop}
    (f : PMorphism R R') (V' : α → W' → Prop) (p : MForm α) (w : W) :
    msat R (fun a x => V' a (f.toFun x)) p w ↔ msat R' V' p (f.toFun w) := by
  induction p generalizing w with
  | atom a => exact Iff.rfl
  | fls => exact Iff.rfl
  | imp p q ih1 ih2 => simp only [msat_imp, ih1, ih2]
  | box p ih =>
      simp only [msat_box]
      constructor
      · intro h u hu
        obtain ⟨v, hv, rfl⟩ := f.back hu
        exact (ih v).1 (h v hv)
      · intro h v hv
        exact (ih v).2 (h _ (f.forth hv))
