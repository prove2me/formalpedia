-- Prove2me | solution 1 for MultiversePMorphism.control_logic_strictly_below_chain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:50:31.628974+00:00
-- url     : https://prove2.me/submissions/3aa26750-d7e0-481c-9dfd-95b2d558739b

-- Sol generated from Logic/Multiverse/PMorphismTransfer.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_PMorphismTransfer
import Definitions.Def_Logic_Multiverse_S42Independence
import Theorems.Thm_MultiversePMorphism_dot3_fails_buttons
import Theorems.Thm_MultiversePMorphism_dot3_valid_of_total
import Theorems.Thm_MultiversePMorphism_msat_pmorphism
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




/-- **Validity transfer.**  The modal logic of a frame is contained in the logic of
any of its surjective bounded images. -/
theorem validity_transfer {R : W → W → Prop} {R' : W' → W' → Prop}
    (f : PMorphism R R') (hsurj : Function.Surjective f.toFun) {p : MForm α}
    (h : ∀ (V : α → W → Prop) (w : W), msat R V p w) :
    ∀ (V' : α → W' → Prop) (u : W'), msat R' V' p u := by
  intro V' u
  obtain ⟨w, rfl⟩ := hsurj u
  exact (msat_pmorphism f V' p w).1 (h _ w)

/-! ## Switches are semantically free -/


variable {Btn Sw : Type*}


theorem forgetSwitches_surjective :
    Function.Surjective (forgetSwitches (Btn := Btn) (Sw := Sw)).toFun :=
  fun S => ⟨(S, fun _ => false), rfl⟩


theorem cardChain_surjective (n : ℕ) : Function.Surjective (cardChain n).toFun := by
  intro u
  have h2 : (u : ℕ) ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨T, _, hT⟩ :=
    Finset.exists_superset_card_eq (s := (∅ : Finset (Fin n))) (by simp) h2
  exact ⟨T, by ext; simpa using hT⟩


theorem controlToChain_surjective (n : ℕ) (Sw : Type*) :
    Function.Surjective (controlToChain n Sw).toFun :=
  (cardChain_surjective n).comp (forgetSwitches_surjective)


/-! ## Linearity is valid on total frames -/



/-- Chains are total. -/
theorem chain_total (n : ℕ) : ∀ i j : Fin (n + 1), i ≤ j ∨ j ≤ i :=
  fun i j => le_total i j

/-! ## The logic of the control frame is strictly below the logic of its chains -/




open MultiversePMorphism in
theorem solution(n : ℕ) (hn : 2 ≤ n) (Sw : Type*) :
    (∀ p : MForm Bool,
        (∀ (V : Bool → CWorld (Fin n) Sw → Prop) (w : CWorld (Fin n) Sw),
            msat cacc V p w) →
        ∀ (V' : Bool → Fin (n + 1) → Prop) (i : Fin (n + 1)), msat (· ≤ ·) V' p i) ∧
    (∃ p : MForm Bool,
        (∀ (V' : Bool → Fin (n + 1) → Prop) (i : Fin (n + 1)), msat (· ≤ ·) V' p i) ∧
        ¬ ∀ (V : Bool → CWorld (Fin n) Sw → Prop) (w : CWorld (Fin n) Sw),
            msat cacc V p w) := by
  constructor
  · intro p hp
    exact validity_transfer (controlToChain n Sw) (controlToChain_surjective n Sw) hp
  · refine ⟨dot3F (.atom true) (.atom false), ?_, ?_⟩
    · intro V' i
      exact dot3_valid_of_total (chain_total n) V' _ _ i
    · intro hall
      have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
        simp [Fin.ext_iff]
      exact dot3_fails_buttons (Sw := Sw) ⟨0, by omega⟩ ⟨1, by omega⟩ h0
        (fun _ => false) (hall _ _)
