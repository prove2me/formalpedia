-- Prove2me | Theorems.Thm_CopwinKT_gfp_eq_kernel
-- name    : CopwinKT.gfp_eq_kernel
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:41:33.776372+00:00
-- url     : https://prove2.me/theorems/21c6fdae-cc39-4cc8-8bb7-70782b614f2d
-- title:
--   Cross-domain bridge.
-- statement:
--   **Cross-domain bridge.** For a contracting, monotone finite pruning update
--   `F` and finite candidate set `S`, the coercion of the greatest fixed kernel `K`
--   equals the Knaster–Tarski greatest fixed point of the associated monotone map on
--   the complete lattice `Set α`.
--
--   Thus the *algorithmic* object produced by finite cop-win pruning coincides with
--   the *order-theoretic* `OrderHom.gfp`.
--
--   ```lean
--   theorem CopwinKT.gfp_eq_kernel(F : Finset α → Finset α) (hcontract : Contracting F)
--       (hmono : MonotoneUpdate F) (S : Finset α)
--       {K : Finset α} (hKS : K ⊆ S) (hKfix : F K = K)
--       (hKmax : ∀ T ⊆ S, F T = T → T ⊆ K) :
--       OrderHom.gfp (G F S hmono) = (↑K : Set α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/CopwinKnasterTarski.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/CopwinKnasterTarski.lean#L136

-- Thm stub generated from Bridges/PosetTheory/CopwinKnasterTarski.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_CopwinKnasterTarski
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

open CopwinKT

variable {α : Type*}

/-! ### The algorithmic side: finite pruning -/










/-! ### The order-theoretic side: a monotone map on the complete lattice `Set α` -/




/-! ### The bridge -/

theorem CopwinKT.gfp_eq_kernel(F : Finset α → Finset α) (hcontract : Contracting F)
    (hmono : MonotoneUpdate F) (S : Finset α)
    {K : Finset α} (hKS : K ⊆ S) (hKfix : F K = K)
    (hKmax : ∀ T ⊆ S, F T = T → T ⊆ K) :
    OrderHom.gfp (G F S hmono) = (↑K : Set α) := by sorry
