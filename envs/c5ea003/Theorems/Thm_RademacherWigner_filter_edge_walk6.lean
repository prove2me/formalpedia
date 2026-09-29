-- Prove2me | Theorems.Thm_RademacherWigner_filter_edge_walk6
-- name    : RademacherWigner.filter_edge_walk6
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:04:27.062319+00:00
-- url     : https://prove2.me/theorems/94725950-ae56-41ab-a359-a0a01079bc23
-- title:
--   If none of the five later steps of a closed 6-walk repeats its first edge
-- statement:
--   If none of the five later steps of a closed 6-walk repeats its first edge
--   `{i,j}`, then that edge is traversed exactly once.
--
--   ```lean
--   theorem RademacherWigner.filter_edge_walk6{i j k l m n : Fin N}
--       (e2 : edgeOf j k ≠ edgeOf i j) (e3 : edgeOf k l ≠ edgeOf i j)
--       (e4 : edgeOf l m ≠ edgeOf i j) (e5 : edgeOf m n ≠ edgeOf i j)
--       (e6 : edgeOf n i ≠ edgeOf i j) :
--       ((Finset.range 6).filter fun t =>
--           edgeOf (walk6 i j k l m n t) (walk6 i j k l m n (t + 1)) = edgeOf i j) = {0} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerWalkParity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerWalkParity.lean#L136

-- Thm stub generated from Probability/WignerWalkParity.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerWalkParity
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The sign-flip involution at arbitrary order: parity of edge multiplicities

`Probability.WignerRademacherEnsemble` kills the expectation of a closed **4**-walk
whose first edge is traversed exactly once, by flipping the Rademacher variable
attached to that edge.  This file isolates the mechanism and proves it at
**arbitrary order**, for an arbitrary walk of arbitrary length:

* `RademacherWigner.prod_entry_flipEdge` — flipping the sign of one edge `p`
  multiplies the product of matrix entries along a walk by `(-1)^c`, where `c` is
  the number of steps of the walk that traverse `p`;
* `RademacherWigner.expect_prod_entry_eq_zero` — hence, if some edge is traversed
  an **odd** number of times, the ensemble average of the walk monomial is `0`.

This is the exact combinatorial reason why only walks whose edge multiset has all
multiplicities even survive in `E [ tr W^m ]`, which is the input to the
moment-method proof of the semicircle law at every order.  Two instantiations are
given: the length-four case, which reproves
`RademacherWigner.expect_term_eq_zero`, and the length-six case, which is the first
case not covered by the earlier files (and the first step towards the exact sixth
trace moment).
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}

/-! ### Edge multiplicities along a walk -/






/-! ### The closed four-walk, revisited -/





/-! ### The closed six-walk -/

theorem RademacherWigner.filter_edge_walk6{i j k l m n : Fin N}
    (e2 : edgeOf j k ≠ edgeOf i j) (e3 : edgeOf k l ≠ edgeOf i j)
    (e4 : edgeOf l m ≠ edgeOf i j) (e5 : edgeOf m n ≠ edgeOf i j)
    (e6 : edgeOf n i ≠ edgeOf i j) :
    ((Finset.range 6).filter fun t =>
        edgeOf (walk6 i j k l m n t) (walk6 i j k l m n (t + 1)) = edgeOf i j) = {0} := by sorry
