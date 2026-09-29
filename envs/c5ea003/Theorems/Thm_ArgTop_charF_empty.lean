-- Prove2me | Theorems.Thm_ArgTop_charF_empty
-- name    : ArgTop.charF_empty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:58:12.334912+00:00
-- url     : https://prove2.me/theorems/cc7835ed-0fe8-4762-af5a-d816072614e9
-- title:
--   `charF ∅` is the set of *unattacked* arguments.
-- statement:
--   `charF ∅` is the set of *unattacked* arguments.
--
--   ```lean
--   theorem ArgTop.charF_empty(R : A → A → Prop) : charF R (∅ : Set A) = {a | ∀ b, ¬ R b a} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ArgumentationCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ArgumentationCore.lean#L87

-- Thm stub generated from Novelty/ArgumentationSymmetric.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationSymmetric

/-!
# The topology of argumentation, IV: symmetric frameworks, naive extensions, and the Euler bridge

This file continues the study of the *conflict-free complex* `K(AF)` of a Dung
argumentation framework `(A, R)` begun in `ArgumentationCore`.  It isolates the
class of **symmetric** frameworks — those where attacks come in pairs
(`R a b → R b a`), the natural setting for mutual disagreement — and establishes
the precise dictionary between the *semantics* of the framework and the
*combinatorial topology* of its complex.

## Main results

* `conflictFree_admissible_of_symmetric` — in a symmetric framework every
  conflict-free set is admissible: each argument defends *itself*, because an
  attacker is always attacked back.  Hence `admissible_iff_conflictFree_of_symmetric`.
* `preferred_iff_maximalConflictFree_of_symmetric` — the **preferred extensions
  of a symmetric framework are exactly the maximal conflict-free sets**, i.e. the
  *facets* of the complex `K(AF)` (its inclusion-maximal faces).  This is the
  key identification of a *semantic* notion (preferred = maximal credulous
  position) with a *topological* one (facet of the independence complex).
* `groundedExt_eq_unattacked_of_symmetric` — the grounded (skeptical) extension
  of a symmetric framework is precisely the set of *unattacked* arguments, the
  isolated vertices of the conflict graph.

## The complete conflict graph and the Euler bridge

For the **complete conflict graph** `completeAF n` on `n` arguments (every two
distinct arguments attack each other), the complex `K(AF)` is `n` isolated
points.  We prove:

* `conflictFree_completeAF_iff` — conflict-free = subsingleton;
* `preferred_completeAF_iff` — preferred extensions are exactly the singletons;
* `preferred_completeAF_ncard` — there are exactly `n` of them;
* `euler_completeAF` — the Euler characteristic of `K(AF)` equals `n`;
* `euler_eq_preferred_completeAF` — **the Euler characteristic equals the number
  of preferred extensions** (for `n ≥ 1`).

This is the *correct* Euler/semantics bridge: the naive identity refuted in
`ArgumentationSimplicial` is replaced, on the symmetric side, by an exact match
between `χ(K(AF))` and the count of maximal independent sets.  The hypothesis
`n ≥ 1` is sharp — see the boundary remark `euler_ne_preferred_completeAF_zero`.
-/

open ArgTop

open Finset

variable {A : Type*} {R : A → A → Prop}

/-! ## Basic Dung semantics (self-contained)

We re-declare the core notions of the conflict-free complex so that this file
compiles independently. -/

theorem ArgTop.charF_empty(R : A → A → Prop) : charF R (∅ : Set A) = {a | ∀ b, ¬ R b a} := by sorry
