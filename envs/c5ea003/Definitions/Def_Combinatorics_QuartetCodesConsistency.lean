-- Prove2me | Definitions.Def_Combinatorics_QuartetCodesConsistency
-- name    : Combinatorics_QuartetCodesConsistency
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:47:04.375125+00:00
-- url     : https://prove2.me/theorems/5b608241-5da3-45e6-893f-b329b0d13429
-- title:
--   Aether Catalog definitions — Combinatorics_QuartetCodesConsistency
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.QuartetCodesConsistency`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/QuartetCodesConsistency.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes

/-!
# Local consistency: the quartet code of a tree obeys parity-check style rules

The lower bound of `Combinatorics.QuartetCodes` counts *leaf orders*, not arbitrary points of the
ternary signature space `(quadruples) → Fin 3`.  This file makes the difference precise: the
signatures that actually come from a tree satisfy local constraints on overlapping quadruples —
the exact analogue of local parity checks of a code — and, already on five leaves, only `15` of
the `3^5 = 243` ternary words are realisable.

Three sample five-leaf rules are proved:

* `qcode_zero_trans` — a cherry propagates: `ab|cd` and `ab|ce` force `ab|de`;
* `qcode_zero_one_rule` — `ab|cd` and `ac|be` force `ae|cd` (type `2` on `a c d e`);
* `qcode_zero_two_rule` — `ab|cd` and `ae|bc` force `be|cd` (type `2` on `b c d e`).

and one forbidden configuration is derived from the first rule.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Tree-realisable quartet signatures form a *constrained* subcode; the constraints are local (they
involve five leaves at a time) and should already cut the code down to a vanishing fraction of the
ternary cube.

## Experiment (Experimenter)
A brute-force scan of all `120` leaf orders on five leaves and all `3 · 3` premise pairs on the
overlapping quadruples produced `210` valid two-premise implications; three representatives were
selected and formalised.  The scan also produced the exact number of realisable five-leaf
signatures, `15`, which is `5!/8` — the number of caterpillar *trees* (each tree arises from `8`
leaf orders: reverse the order, swap the first two leaves, swap the last two).

## Analysis (Analyst)
The count `15 = 5!/8 ≪ 243` shows that the tree code has rate `log₃ 15 / 5 ≈ 0.55` on five leaves
and that any packing bound computed in the *unconstrained* ternary cube is far off; the
first-moment argument of the lower-bound file is carried out inside the constrained code, which is
why it survives.

## Critique (Critic)
The three rules are proved by unfolding the code characterisations and `omega`; they are genuine
implications between distinct quadruples, not restatements of the trichotomy.  The exhaustive
five-leaf count is a kernel computation (`decide`), used only for the concrete datum `15`.
-/

open Finset

namespace QuartetCodes

section LocalRules

variable {n : ℕ} {π : Equiv.Perm (Fin n)} {a b c d e : Fin n}





end LocalRules

/-! ## The five-leaf code, counted exactly -/

section FiveLeafCode

/-- The five quadruples of a five-leaf set, as ordered tuples. -/
def quads5 : List (Fin 5 × Fin 5 × Fin 5 × Fin 5) :=
  [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 3, 4), (0, 2, 3, 4), (1, 2, 3, 4)]

/-- The quartet signature of a five-leaf caterpillar: a ternary word of length five. -/
def sig5 (π : Equiv.Perm (Fin 5)) : List (Fin 3) :=
  quads5.map (fun q => qcode π q.1 q.2.1 q.2.2.1 q.2.2.2)




end FiveLeafCode

end QuartetCodes


