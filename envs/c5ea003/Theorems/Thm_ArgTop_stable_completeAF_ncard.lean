-- Prove2me | Theorems.Thm_ArgTop_stable_completeAF_ncard
-- name    : ArgTop.stable_completeAF_ncard
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-14T01:22:21.987312+00:00
-- url     : https://prove2.me/theorems/b544753c-732c-499b-a016-f551b0e10179
-- title:
--   There are exactly `n` stable extensions of the complete conflict graph on
-- statement:
--   There are exactly `n` stable extensions of the complete conflict graph on
--   `n ≥ 1` arguments.
--
--   ```lean
--   theorem ArgTop.stable_completeAF_ncard(n : ℕ) (hn : 0 < n) :
--       Set.ncard {S : Set (Fin n) | Stable (completeAF n) S} = n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ArgumentationStable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ArgumentationStable.lean#L280

-- Thm stub generated from Novelty/ArgumentationStable.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationStable

/-!
# The topology of argumentation, V: stable extensions and the stable/preferred/Euler chain

This file is **self-contained** (it re-declares the basic Dung semantics) and
deepens the theory begun in `ArgumentationCore`, `ArgumentationExtensions`,
`ArgumentationSimplicial` and `ArgumentationSymmetric` by developing the
strongest of the classical *extension-based* semantics — the **stable
extension** — and situating it inside the full hierarchy

  `stable ⟹ preferred ⟹ complete ⟹ admissible ⟹ conflict-free`.

A set `S` is a **stable extension** when it is conflict-free and *attacks every
argument it does not contain* (`∀ a ∉ S, ∃ b ∈ S, R b a`).  Stable extensions are
the "no abstention" positions: every argument is either accepted or explicitly
defeated.

## The chain of results

* `stable_defends`     — a stable set defends each of its members;
* `stable_admissible`  — every stable extension is admissible;
* `stable_complete`    — every stable extension is complete (closed under defense);
* `stable_preferred`   — **every stable extension is preferred** (maximal admissible);
* `stable_maximalConflictFree` — every stable extension is a *facet* of `K(AF)`;
* `groundedExt_subset_stable` — the grounded extension is contained in every
  stable extension (skeptical ⊆ every stable position).

## The symmetric bridge and the Euler correspondence

For **symmetric irreflexive** frameworks (the model of two-sided disagreement)
we prove the exact collapse

* `maximalConflictFree_stable_of_symmetric` and hence
* `stable_iff_preferred_of_symmetric_irrefl` — **stable = preferred = facet** of
  the conflict-free complex `K(AF)`.

Specialising to the **complete conflict graph** `completeAF n` (which is
symmetric and irreflexive) we obtain, entirely self-contained:

* `stable_completeAF_iff` — the stable extensions are exactly the singletons;
* `stable_completeAF_ncard` — there are exactly `n` of them;
* `euler_eq_stable_completeAF` — **the Euler characteristic of `K(AF)` equals the
  number of stable extensions** (for `n ≥ 1`), extending the Euler/semantics
  bridge of `ArgumentationSymmetric` from preferred to stable extensions.
-/

open ArgTop

-- open removed: section is not a namespace

variable {A : Type*} (R : A → A → Prop)

/-! ## Basic Dung semantics (self-contained) -/











/-! ## The stable hierarchy -/






/-! ## The grounded extension is below every stable extension -/





/-! ## Symmetric frameworks: stable = preferred = facet -/







/-! ## The complete conflict graph: stable count and the Euler bridge -/

open ArgTop

-- open removed: section is not a namespace

theorem ArgTop.stable_completeAF_ncard(n : ℕ) (hn : 0 < n) :
    Set.ncard {S : Set (Fin n) | Stable (completeAF n) S} = n := by sorry
