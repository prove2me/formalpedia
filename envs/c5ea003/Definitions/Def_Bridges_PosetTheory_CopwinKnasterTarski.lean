-- Prove2me | Definitions.Def_Bridges_PosetTheory_CopwinKnasterTarski
-- name    : Bridges_PosetTheory_CopwinKnasterTarski
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:29.908423+00:00
-- url     : https://prove2.me/theorems/fad50e09-f268-441b-8cfd-c40e170e5cbe
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_CopwinKnasterTarski
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.CopwinKnasterTarski`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/CopwinKnasterTarski.lean by skeleton subtraction
import Mathlib
/-
# A bridge: finite cop-win pruning ↔ Knaster–Tarski greatest fixed points

Implementations of the `k`-copwin recognition algorithm repeatedly *prune* a
finite candidate set of positions, deleting those that fail a local survival
test.  Two facts drive every such implementation:

* each round returns a **subset** of the current state space (the update is
  *contracting*), and
* refining the input can only refine the output (the update is *monotone*).

Under these two hypotheses the algorithm terminates and returns a distinguished
fixed candidate set.  This file proves that this *algorithmic* object is exactly
an *order-theoretic* object from lattice theory: the **greatest fixed point**
(à la Knaster–Tarski) of an associated monotone endomorphism of the complete
lattice `Set α`.

This is a genuine cross-domain bridge:

* **Left side (combinatorics / algorithm termination).**  A contracting update
  `F : Finset α → Finset α` iterated by `rounds` reaches a fixed point in at
  most `|S|` steps (`exists_fixed_round_le_card`), and that fixed point is the
  greatest fixed candidate set below `S` (`exists_greatest_fixed_kernel`).

* **Right side (order theory / fixed-point theory).**  On the complete lattice
  `Set α`, the map `G F S` is a bona fide `OrderHom`, and Mathlib's
  `OrderHom.gfp` gives its greatest fixed point via Knaster–Tarski.

* **The bridge.**  `gfp_eq_kernel` shows the coercion of the algorithmic kernel
  equals `OrderHom.gfp (G F S)`, and `gfp_computed_by_finite_iteration`
  strengthens this to: the abstract greatest fixed point is *computed* by the
  concrete finite pruning loop within `|S|` rounds.

The file is self-contained (depends only on Mathlib).
-/


open Classical Finset

namespace CopwinKT

variable {α : Type*}

/-! ### The algorithmic side: finite pruning -/

/-- Iteration of one pruning round. -/
def rounds (F : Finset α → Finset α) : ℕ → Finset α → Finset α
  | 0, S => S
  | n + 1, S => F (rounds F n S)

/-- A contracting update never introduces a candidate. -/
def Contracting (F : Finset α → Finset α) : Prop := ∀ S, F S ⊆ S

/-- A monotone update preserves inclusion of candidate sets. -/
def MonotoneUpdate (F : Finset α → Finset α) : Prop := ∀ ⦃S T⦄, S ⊆ T → F S ⊆ F T







/-! ### The order-theoretic side: a monotone map on the complete lattice `Set α` -/

/-- The pruning update lifted to a monotone endomorphism of the complete
lattice `Set α`: it restricts a set of vertices to the finite candidates in `S`,
then applies the finite update. -/
noncomputable def G (F : Finset α → Finset α) (S : Finset α) (hmono : MonotoneUpdate F) :
    Set α →o Set α where
  toFun X := ↑(F (S.filter (fun a => a ∈ X)))
  monotone' := by
    intro X Y hXY
    apply Finset.coe_subset.mpr
    apply hmono
    intro a ha
    rw [Finset.mem_filter] at *
    exact ⟨ha.1, hXY ha.2⟩



/-! ### The bridge -/



/-! ### A concrete instance -/


end CopwinKT


