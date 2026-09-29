-- Prove2me | Theorems.Thm_TwoTreeClosure_residue_dial_letterBlind
-- name    : TwoTreeClosure.residue_dial_letterBlind
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:25:48.826347+00:00
-- url     : https://prove2.me/theorems/20ca84a1-cb76-49f0-891f-8250e4658e70
-- title:
--   No residue dial computes the ascent letter.
-- statement:
--   **No residue dial computes the ascent letter.**  For every modulus `M ≥ 1`, no
--   function of the hypotenuse's residue mod `M` agrees with the ascent letter on all
--   nodes.  (Applies verbatim to the Gauss-sum dial modulus `M = 720720`.)
--
--   ```lean
--   theorem TwoTreeClosure.residue_dial_letterBlind(M : ℕ) (hM : 1 ≤ M) (g : ℕ → Letter) :
--       ¬ (∀ m n, IsNode m n → g (hyp m n % M) = letterOf m n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TwoTreeClosure/TreeCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TwoTreeClosure/TreeCore.lean#L311

-- Thm stub generated from Bridges/TwoTreeClosure/TreeCore.lean
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore

/-!
# The Berggren / Price tree of primitive Pythagorean triples: nodes, letters, blindness

This file develops the ternary Berggren tree in its Price coordinates: nodes are
pairs `(m, n)` with `m > n ≥ 1`, `gcd m n = 1` and `m + n` odd, the root is `(2,1)`,
and the three children of `(m, n)` are

* `A : (m, n) ↦ (2m - n, m)`,
* `B : (m, n) ↦ (2m + n, m)`,
* `C : (m, n) ↦ (m + 2n, n)`.

The triple attached to a node is `(m² - n², 2mn, m² + n²)`.

Main results.

* `isNode_childA/B/C`, `parent_*` : the tree is well defined and every non-root node
  has a unique parent, given by the *ascent letter* `letterOf`.
* `isNode.inTree` : **coverage** — every node in the arithmetic sense is reachable
  from the root `(2,1)`; the letter of a node is exactly the branch taken by its parent.
* `letterOf_blind_of_residue` : **residue dials are blind.**  For *every* modulus
  `M ≥ 1` and every scale `t ≥ 1` there are three nodes with hypotenuses all
  congruent to `1 mod M` and with the three distinct ascent letters.  Hence no
  function of `hyp mod M` computes the ascent letter (`residue_dial_letterBlind`),
  in particular no Gauss-sum style dial on `N mod 720720`.
* `letterOf_blind_of_magnitude` : **magnitude mirrors are blind.**  There is an
  infinite family of hypotenuses realised by two different nodes with *different*
  letters, e.g. `505 = 19² + 12² = 21² + 8² = 5 · 101`.  Hence no function of the
  hypotenuse itself — monotone or not — computes the ascent letter
  (`magnitude_probe_letterBlind`).
* `parityProfile_constant` : structural sensors (leg parities, Lorentz form) are
  *exactly* constant on the tree, so they are blind for trivial reasons.
-/

open TwoTreeClosure

/-! ### Nodes -/







/-! ### Children -/








/-! ### Ascent letters -/






/-! ### Reachability from the root, and coverage -/








/-! ### Blindness -/


/-! #### Strength 1–2: residue dials -/

theorem TwoTreeClosure.residue_dial_letterBlind(M : ℕ) (hM : 1 ≤ M) (g : ℕ → Letter) :
    ¬ (∀ m n, IsNode m n → g (hyp m n % M) = letterOf m n) := by sorry
