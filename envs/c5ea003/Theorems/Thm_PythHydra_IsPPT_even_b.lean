-- Prove2me | Theorems.Thm_PythHydra_IsPPT_even_b
-- name    : PythHydra.IsPPT.even_b
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:29:55.610099+00:00
-- url     : https://prove2.me/theorems/55c39b80-fe85-47ab-9ba4-8963d0924c5c
-- title:
--   Even b
-- statement:
--   Formal statement of `PythHydra.IsPPT.even_b` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PythHydra.IsPPT.even_b{a b c : ℤ} (h : IsPPT a b c) : Even b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PythagoreanHydra/BerggrenDescent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PythagoreanHydra/BerggrenDescent.lean#L106

-- Thm stub generated from Geometry/PythagoreanHydra/BerggrenDescent.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent

/-!
# The Berggren descent: a complete classification of the Berggren tree

This file develops, from scratch but following the naming of the catalog module
`Catalog/Bridges/BerggrenTrees/BerggrenPythagoreanCore.lean` (definitions `IsPythag`,
`bergA`, `bergB`, `bergC`, `invA`, `invB`, `invC`), the *descent* half of the Berggren
theory, which that module leaves open (its `parent_exists` is commented out there
because the required case analysis was missing).

The main results are:

* `PythHydra.parent` — a single, uniform **parent map** `(a,b,c) ↦ (|u|, |v|, 3c-2a-2b)`
  with `u = a + 2b - 2c`, `v = 2a + b - 2c`.
* `PythHydra.parent_eq_inv` — the parent map *is* one of the three inverse Berggren
  moves `invA`, `invB`, `invC`; which one is decided by the signs of `u` and `v`.
* `PythHydra.parent_isPPT`, `PythHydra.parent_hyp_lt` — the parent of a primitive
  triple is primitive, with strictly smaller hypotenuse: the descent is well-founded.
* `PythHydra.reach_iff_isPPT` — **classification**: the Berggren tree rooted at
  `(3,4,5)` consists of exactly the primitive Pythagorean triples with odd first leg.
* `PythHydra.decidableReach` — consequently membership in the Berggren tree is
  *decidable* (by an elementary arithmetic test), which is the negative answer to the
  "Matiyasevich phenomenon on the tree" front of the research mission.
-/

open PythHydra












/-! ### Elementary consequences of primitivity -/

theorem PythHydra.IsPPT.even_b{a b c : ℤ} (h : IsPPT a b c) : Even b := by sorry
