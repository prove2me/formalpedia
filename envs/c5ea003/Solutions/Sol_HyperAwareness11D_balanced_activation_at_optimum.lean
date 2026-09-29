-- Prove2me | solution 1 for HyperAwareness11D.balanced_activation_at_optimum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:15:16.595978+00:00
-- url     : https://prove2.me/submissions/17bdd126-dbef-47ad-9789-f5d6485a8a12

-- Sol generated from MachineLearning/HyperAwareness11D/BalancedFrame.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
import Theorems.Thm_HyperAwareness11D_exists_antipodal_probes

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
theorem solution[Fintype ι] (W : ι → Fin n → ℝ) (b : ι → ℝ)
    (hinj : Function.Injective (reluLayer W b)) (hcard : Fintype.card ι = 2 * n) :
    ∃ x y : Fin n → ℝ,
      (ActiveRows W b x).card = n ∧ (ActiveRows W b y).card = n ∧
      Disjoint (ActiveRows W b x) (ActiveRows W b y) ∧
      ∀ i, i ∈ ActiveRows W b x ∨ i ∈ ActiveRows W b y := by
  classical
  obtain ⟨x, y, hx, hy, hdisj⟩ := exists_antipodal_probes W b hinj
  have hunion : (ActiveRows W b x ∪ ActiveRows W b y).card
      = (ActiveRows W b x).card + (ActiveRows W b y).card :=
    Finset.card_union_of_disjoint hdisj
  have hle : (ActiveRows W b x ∪ ActiveRows W b y).card ≤ Fintype.card ι :=
    Finset.card_le_univ _
  have hcx : (ActiveRows W b x).card = n := by omega
  have hcy : (ActiveRows W b y).card = n := by omega
  refine ⟨x, y, hcx, hcy, hdisj, ?_⟩
  have huniv : ActiveRows W b x ∪ ActiveRows W b y = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    omega
  intro i
  have : i ∈ ActiveRows W b x ∪ ActiveRows W b y := by rw [huniv]; exact Finset.mem_univ i
  exact Finset.mem_union.mp this
