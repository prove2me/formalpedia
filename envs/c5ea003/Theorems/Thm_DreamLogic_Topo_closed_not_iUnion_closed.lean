-- Prove2me | Theorems.Thm_DreamLogic_Topo_closed_not_iUnion_closed
-- name    : DreamLogic.Topo.closed_not_iUnion_closed
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:19:56.206306+00:00
-- url     : https://prove2.me/theorems/7882dee4-4fc1-4157-8fb6-468cb33ba62e
-- title:
--   The structural root of paraconsistency.
-- statement:
--   **The structural root of paraconsistency.** Closed sets are not closed under arbitrary
--   union: the closed intervals `[1/(n+1), 1]` union to the half-open interval `(0,1]`, which is
--   not closed. Logically, this is the failure of infinite disjunction to preserve truth that
--   underlies non-explosion.
--
--   ```lean
--   theorem DreamLogic.Topo.closed_not_iUnion_closed:
--       ∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ ¬ IsClosed (⋃ n, F n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DreamLogic/ClosedSetTopology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DreamLogic/ClosedSetTopology.lean#L91

-- Thm stub generated from Logic/DreamLogic/ClosedSetTopology.lean
import Mathlib
import Definitions.Def_Logic_DreamLogic_ClosedSetTopology

/-!
# Dream Logic II — Closed-Set Semantics and the Failure of Arbitrary Union

This file gives the *topological* face of dream logic. In the standard intuitionistic
topological semantics, propositions are **open** sets and negation is the interior of the
complement; the law of non-contradiction holds and excluded middle fails. Dream logic is the
exact dual: propositions are **closed** sets and negation is the *closure of the complement*,

  `pneg A = closure Aᶜ`.

In this closed-set semantics contradictions genuinely coexist — a set and its negation can
overlap on their shared boundary — and the structural obstruction that makes the logic
paraconsistent is precisely that **closed sets are not closed under arbitrary union**.

## Main results

* `isClosed_pneg` — the paraconsistent negation of any set is a legitimate (closed) proposition.
* `lem_closed_holds` — the law of excluded middle *survives* for closed propositions:
  `A ∪ pneg A = univ`.
* `contradiction_coexists` — the law of non-contradiction *fails*: there is a closed set
  meeting its own negation, an "impossible object" living on the boundary.
* `closed_not_iUnion_closed` — the structural root of paraconsistency: a countable family of
  closed sets whose union fails to be closed.
* `frontier_is_glut` — boundary points are exactly the gluts: they lie in a closed set and in
  its paraconsistent negation simultaneously.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Dream logic should be modelled by *closed* subsets of a
topological space with `pneg A = closure Aᶜ`. If so, the impossible objects of the algebraic
model must appear as concrete geometric objects, and the paraconsistency must be traceable to
a specific topological failure — the non-closure of arbitrary unions of closed sets.

Experiment (Experimenter): Work over `ℝ` with its order topology. Take the model proposition
`A = [0,1]`. Compute `pneg A`, its overlap with `A`, and test excluded middle and
non-contradiction. Separately, build the family `[1/(n+1), 1]` and evaluate its union.

Analysis (Analyst): `A ∩ pneg A` is exactly the topological frontier `{0,1}` — the boundary
points are the gluts. Excluded middle holds trivially because `Aᶜ ⊆ pneg A`. The union
`⋃ₙ [1/(n+1),1] = (0,1]` is *not* closed: the infimum `0` is a limit point outside it. This
missing closure is the same phenomenon that, read logically, blocks the inference "if a
contradiction holds then everything holds" — infinite disjunction does not preserve truth.

Critique (Critic): The coexistence witness is a nonempty overlap given by an explicit point,
so the theorem is not vacuous. The union counterexample uses a genuine limit argument
(`closure (0,1] = [0,1]`), not a definitional trick. All statements quantify over honest
objects of `ℝ` and are proved with real topological lemmas (`closure_Ioc`, `closure_Iio`,
`isClosed_Icc`).

Synthesis (PI): The closed-set model realizes the algebraic dream logic geometrically:
gluts are boundary points, and the paraconsistency is the shadow of arbitrary unions of
closed sets escaping closedness. The bridge to the four-valued algebra is made explicit in
`Correspondence.lean`.
-/

open DreamLogic.Topo

open Set

theorem DreamLogic.Topo.closed_not_iUnion_closed:
    ∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ ¬ IsClosed (⋃ n, F n) := by sorry
