-- Prove2me | Theorems.Thm_BooleanCubicFormOrbits_card_le_numOrbits_mul_card_group
-- name    : BooleanCubicFormOrbits.card_le_numOrbits_mul_card_group
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:05:36.555095+00:00
-- url     : https://prove2.me/theorems/988c9f4c-80ff-4f7b-a3ca-fc051623b578
-- title:
--   Orbit–counting inequality.
-- statement:
--   **Orbit–counting inequality.**  For a finite group `G` acting on a finite set `X`, the
--   number of forms is at most the number of orbits times the order of the group.  Equivalently,
--   the number of orbits is at least `|X| / |G|`.  The proof partitions `X` into its orbits and
--   bounds each orbit size by `|G|` via orbit–stabilizer.
--
--   ```lean
--   theorem BooleanCubicFormOrbits.card_le_numOrbits_mul_card_group    (G X : Type*) [Group G] [Fintype G] [MulAction G X] [Fintype X]
--       [Fintype (orbitRel.Quotient G X)] :
--       Fintype.card X ≤ Fintype.card (orbitRel.Quotient G X) * Fintype.card G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BooleanCubicFormOrbits.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BooleanCubicFormOrbits.lean#L84

-- Thm stub generated from Novelty/BooleanCubicFormOrbits.lean
import Mathlib
import Definitions.Def_Novelty_BooleanCubicFormOrbits

/-!
# Structural bounds on the orbit count of Boolean cubic forms under the general linear group

A *Boolean cubic form* in `n` variables over the two–element field is a squarefree
homogeneous polynomial of degree three, i.e. a `GF(2)`-linear combination of the
monomials `x_i x_j x_k` with `i, j, k` distinct.  Such a form is determined by its
coefficient vector, one bit for each three–element subset of the variable set, so the
space of Boolean cubic forms in `n` variables is a `GF(2)`-vector space of dimension
`C(n, 3)`.  The general linear group `GL(n, 2)` acts on this space by linear substitution
of the variables, and a central classification problem asks for the number of orbits of
this action.

For `n = 10` the coefficient space has dimension `C(10, 3) = 120`, so there are `2^120`
Boolean cubic forms in ten variables and `|GL(10, 2)| = 366440137299948128422802227200`
substitutions.  It has been proposed that the number of *nonzero* orbits is exactly
`3 691 560`.

This file establishes a rigorous, purely structural lower bound on that number and shows
that the proposed value is consistent with it and, in fact, remarkably close to it.  The
argument is the orbit–counting (pigeonhole) principle: the space is partitioned into
orbits, each of size at most the order of the group, so the number of orbits is at least
`⌈(number of forms) / |GL(10, 2)|⌉`.  Carrying out the arithmetic yields

  number of nonzero orbits ≥ 3 627 409,

which lies within `1.77%` of the proposed count `3 691 560`.  The gap of exactly
`64 151` orbits measures the aggregate excess of forms that lie in *non-free* orbits
(forms with a nontrivial stabilizer): if every nonzero form had trivial stabilizer, the
bound would be tight.

The main results are:

* `card_le_numOrbits_mul_card_group` — the fundamental orbit–counting inequality for any
  finite group acting on a finite set.
* `card_pred_le` — the sharper inequality obtained by isolating a fixed point (here the
  zero form).
* `card_GL10` — the order of `GL(10, 2)`.
* `card_boolCubic10` — the number of Boolean cubic forms in ten variables is `2^120`.
* `nonzero_orbits_lower_bound` / `gl10_boolCubic_bound` — the structural lower bound
  `3 627 409` on the number of nonzero orbits.
* `total_orbits_lower_bound` — the companion bound on the total number of orbits.
* `proposed_count_consistent` — the proposed value `3 691 560` lies between the proven
  lower bound and the total number of forms, with an explicit excess of `64 151`.

-- !-- Lab Notes -- !--
Hypothesis: The number of `GL(10,2)`-orbits of Boolean cubic forms in ten variables is
finite and admits a sharp, computable lower bound from first principles, and the proposed
value `3 691 560` should be consistent with it.

Experiment: Model the form space by its coefficient vectors (functions from the set of
three–element subsets of a ten–element index set to `GF(2)`) and the group as `GL(10,2)`.
Prove the orbit–counting inequality abstractly, compute the two cardinalities
(`|GL(10,2)|` via the finite–field order formula, `2^120` via the count of three–subsets),
and combine them arithmetically.

Analysis: The pigeonhole bound gives `⌈(2^120 - 1)/|GL(10,2)|⌉ = 3 627 409` nonzero
orbits.  Isolating the zero form (a global fixed point) sharpens the count by removing one
singleton orbit before dividing, which is what lets the bound reach `3 627 409` rather than
one less.  The proposed count `3 691 560` exceeds the bound by exactly `64 151` — the
"defect" attributable to forms lying in orbits shorter than `|GL(10,2)|`.

Critique: The bound is *not* trivial: it depends on the exact group order (a thirty–digit
number obtained from the general linear group cardinality formula) and the exact dimension
`C(10,3) = 120`.  Every main theorem uses genuine structural input (a summation over the
orbit partition, orbit–stabilizer divisibility, and integer arithmetic on large literals).
The exact orbit count itself is beyond a closed–form derivation and is left as a conjecture
in the future–directions note; what is proven here is the tight two–sided window in which it
must lie.

Synthesis: A single orbit–counting inequality, instantiated with two exact cardinalities,
pins the number of nonzero orbits of Boolean cubic forms in ten variables to the interval
`[3 627 409, 2^120 - 1]` and certifies that the proposed value `3 691 560` sits inside it,
within `1.77%` of the lower endpoint.
-/

open MulAction Matrix
open scoped BigOperators

open BooleanCubicFormOrbits

/-! ## The abstract orbit–counting inequalities -/

theorem BooleanCubicFormOrbits.card_le_numOrbits_mul_card_group    (G X : Type*) [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [Fintype (orbitRel.Quotient G X)] :
    Fintype.card X ≤ Fintype.card (orbitRel.Quotient G X) * Fintype.card G := by sorry
