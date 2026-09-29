-- Prove2me | Theorems.Thm_HyperAwareness11D_doubleW_activeRows_pos
-- name    : HyperAwareness11D.doubleW_activeRows_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:37:35.439043+00:00
-- url     : https://prove2.me/theorems/d9697776-ee4f-45fa-bb63-94f839feae8f
-- title:
--   The canonical optimum realises the balanced pattern concretely: at an all-positive
-- statement:
--   The canonical optimum realises the balanced pattern concretely: at an all-positive
--   percept the active units are exactly the "positive half" of the split layer.
--
--   ```lean
--   theorem HyperAwareness11D.doubleW_activeRows_pos(x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (i : Fin n ⊕ Fin n) :
--       i ∈ ActiveRows (doubleW n) 0 x ↔ ∃ k, i = Sum.inl k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HyperAwareness11D/BalancedFrame.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HyperAwareness11D/BalancedFrame.lean#L91

-- Thm stub generated from MachineLearning/HyperAwareness11D/BalancedFrame.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity

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

theorem HyperAwareness11D.doubleW_activeRows_pos(x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (i : Fin n ⊕ Fin n) :
    i ∈ ActiveRows (doubleW n) 0 x ↔ ∃ k, i = Sum.inl k := by sorry
