-- Prove2me | solution 1 for S42Independence.five_fails_ctrl
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:25:54.631417+00:00
-- url     : https://prove2.me/submissions/f2f60b5f-3c15-4361-b13d-e46482e78d30

-- Sol generated from Logic/Multiverse/S42Independence.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_InvariantFragment
import Definitions.Def_Logic_Multiverse_S42Independence
import Theorems.Thm_S42Independence_msat_atom
import Theorems.Thm_S42Independence_msat_box
/-
# `S4.2` Soundness for Directed Preorders, and Independence of `5` and `.3`

This file completes the calibration begun in
`Catalog/Logic/Multiverse/InvariantFragment.lean` by supplying the *deductive*
half of Direction 2 of the multiverse programme.

We define a modal language, its Kripke semantics, and a Hilbert calculus for
**`S4.2`** (classical propositional logic together with `K`, `T`, `4` and the
directedness axiom `.2`, closed under modus ponens and necessitation), and prove:

* `S42_sound` — **every theorem of `S4.2` is valid on every directed preorder**
  (induction on derivations; the `.2` case is exactly where directedness is used);
* `five_not_derivable` — the axiom `5` (`◇p → □◇p`) is **not** derivable in `S4.2`,
  because it fails on the finite button–switch forcing frame of the realization
  file, which *is* a directed preorder;
* `dot3_not_derivable` — the linearity axiom `.3`
  (`□(□p → q) ∨ □(□q → p)`) is **not** derivable in `S4.2` either: two independent
  buttons refute it.

Together with `BooleanValuedRealization.cacc_dot2` (soundness of `.2` on the frame)
and `MultiverseInvariantFragment.directed_of_dot2` (its exact semantic content),
this shows the modal logic of the finite pre-Boolean forcing frames contains `S4.2`
and is strictly below both `S5` and `S4.3`.
-/

open S42Independence

open BooleanValuedRealization MultiverseInvariantFragment

/-! ## The modal language and its Kripke semantics -/


open MForm
variable {α : Type*}



variable {α W : Type*}


@[simp] theorem msat_neg (R : W → W → Prop) (V : α → W → Prop) (p : MForm α) (w : W) :
    msat R V p.neg w ↔ ¬ msat R V p w := Iff.rfl

/-- Semantics of possibility: `◇p` holds at `w` iff `p` holds at some successor. -/
@[simp] theorem msat_dia (R : W → W → Prop) (V : α → W → Prop) (p : MForm α) (w : W) :
    msat R V p.dia w ↔ ∃ v, R w v ∧ msat R V p v := by
  simp only [MForm.dia, msat_neg, msat_box]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h fun v hv => hc v hv
  · rintro ⟨v, hv, hp⟩ h
    exact h v hv hp


/-! ## The Hilbert calculus `S4.2` -/




/-! ## The finite control frame as a directed preorder -/





/-! ## Independence of `5` -/



/-! ## Independence of `.3` -/






open S42Independence in
theorem solution:
    ¬ msat ctrlFrame.rel Vunpushed
        (.imp (MForm.dia (.atom true)) (.box (MForm.dia (.atom true)))) w₀ := by
  intro h
  have hdia : msat ctrlFrame.rel Vunpushed (MForm.dia (.atom true)) w₀ := by
    rw [msat_dia]
    exact ⟨w₀, subset_rfl, by simp [w₀, Vunpushed]⟩
  have hbox := h hdia
  have hpushed : ctrlFrame.rel w₀ (({true} : Finset Bool), fun _ => false) :=
    Finset.empty_subset _
  have := hbox _ hpushed
  rw [msat_dia] at this
  obtain ⟨u, hu, hpu⟩ := this
  exact hpu (hu (Finset.mem_singleton_self true))
