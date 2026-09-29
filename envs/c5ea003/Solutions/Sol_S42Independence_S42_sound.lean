-- Prove2me | solution 1 for S42Independence.S42_sound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:25:53.53545+00:00
-- url     : https://prove2.me/submissions/dda378e0-3b0e-4f47-8e9d-1133ea63b30c

-- Sol generated from Logic/Multiverse/S42Independence.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_InvariantFragment
import Definitions.Def_Logic_Multiverse_S42Independence
import Theorems.Thm_S42Independence_msat_box
import Theorems.Thm_S42Independence_msat_imp
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
theorem solution(F : DirectedPreorder W) {p : MForm α} (h : S42 p) :
    ∀ (V : α → W → Prop) (w : W), msat F.rel V p w := by
  induction h with
  | ax1 p q => intro V w; simp only [msat_imp]; tauto
  | ax2 p q r => intro V w; simp only [msat_imp]; tauto
  | ax3 p => intro V w; simp only [msat_imp, msat_neg]; tauto
  | axK p q => intro V w hpq hp v hv; exact hpq v hv (hp v hv)
  | axT p => intro V w hp; exact hp w (F.refl w)
  | ax4 p => intro V w hp v hwv u hvu; exact hp u (F.trans hwv hvu)
  | axDot2 p =>
      intro V w hdia v hwv
      rw [msat_dia] at hdia
      obtain ⟨t, hwt, hbox⟩ := hdia
      obtain ⟨u, htu, hvu⟩ := F.dir w t v hwt hwv
      rw [msat_dia]
      exact ⟨u, hvu, hbox u htu⟩
  | mp _ _ ih1 ih2 => intro V w; exact ih1 V w (ih2 V w)
  | nec _ ih => intro V w v _; exact ih V v
