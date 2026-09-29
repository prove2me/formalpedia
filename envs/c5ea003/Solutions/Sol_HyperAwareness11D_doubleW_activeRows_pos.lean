-- Prove2me | solution 1 for HyperAwareness11D.doubleW_activeRows_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:17:17.607032+00:00
-- url     : https://prove2.me/submissions/8fdb5ead-71e4-410d-9af3-3329c57557c9

-- Sol generated from MachineLearning/HyperAwareness11D/BalancedFrame.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
import Theorems.Thm_HyperAwareness11D_preAct_doubleW_inl
import Theorems.Thm_HyperAwareness11D_preAct_doubleW_inr

/-!
# Hyper-Awareness IV: rigidity at the optimum — width-`22` layers are perfectly balanced

`Injectivity.lean` shows that a lossless ReLU perception layer on `ℝ¹¹` needs at least `22`
units and that `22` suffice.  This file shows that architectures *at* the optimum are
extremely rigid: no slack is left anywhere.

## Main results

* `HyperAwareness11D.balanced_activation_at_optimum` — if an injective ReLU layer on `ℝⁿ` has
  exactly `2n` units, then there are two percepts whose active unit sets **partition** the
  units into two blocks of size exactly `n`.
* `HyperAwareness11D.every_unit_essential` — consequently *every* unit of a width-optimal
  lossless layer has a nonzero weight row: there are no dead or constant units, no
  redundancy, and no unit can be deleted.
* `HyperAwareness11D.balanced_activation_11` / `every_unit_essential_11` — the statements in
  the mission's dimension: a `22`-unit lossless 11-dimensional perception layer splits, at
  suitable antipodal percepts, into two perfectly balanced halves of `11` active units.

Interpretation: at the information-theoretic optimum the layer behaves exactly like the
canonical positive/negative split — half the units carry the "positive half" of the percept
and half carry the "negative half" — even though no such structure was assumed.
-/

open HyperAwareness11D

open Finset

noncomputable section

open scoped Classical

variable {ι : Type*} {n : ℕ}








open HyperAwareness11D in
theorem solution(x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (i : Fin n ⊕ Fin n) :
    i ∈ ActiveRows (doubleW n) 0 x ↔ ∃ k, i = Sum.inl k := by
  classical
  simp only [ActiveRows, Finset.mem_filter, Finset.mem_univ, true_and]
  cases i with
  | inl k =>
    constructor
    · intro _; exact ⟨k, rfl⟩
    · intro _
      refine ⟨by simpa [preAct_doubleW_inl] using hx k, ⟨k, ?_⟩⟩
      simp [doubleW]
  | inr k =>
    constructor
    · rintro ⟨hpos, -⟩
      rw [preAct_doubleW_inr] at hpos
      exact absurd hpos (by simpa using (hx k).le)
    · rintro ⟨k', hk'⟩
      exact absurd hk' (by simp)
