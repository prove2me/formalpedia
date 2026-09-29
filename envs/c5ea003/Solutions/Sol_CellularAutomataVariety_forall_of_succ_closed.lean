-- Prove2me | solution 1 for CellularAutomataVariety.forall_of_succ_closed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:48.097198+00:00
-- url     : https://prove2.me/submissions/ae7ac2ce-d3cc-431a-a851-a3d1a32f4339

-- Sol generated from Applications/CellularAutomataVariety/Basic.lean
import Mathlib
import Definitions.Def_Applications_CellularAutomataVariety_Basic

/-!
# Elementary cellular automata as algebraic varieties over the binary field

An *elementary cellular automaton* (ECA) updates a one-dimensional binary array
using a fixed function of each cell together with its two nearest neighbours.
Writing the alphabet as the binary field `GF(2) = ZMod 2`, a configuration on a
cyclic lattice of length `n` is a function `s : ZMod n → GF(2)`, and every one of
the `256` local rules is a polynomial map of degree at most three:
`g(a,b,c)` is the unique multilinear `GF(2)`-polynomial reproducing the rule's
truth table.  The *fixed-point set* `V(g) = { s : step g s = s }` is then the
`GF(2)`-points of an affine variety, cut out by the `n` cubic equations
`s i = g (s (i-1), s i, s (i+1))`.

This file develops that dictionary and, in particular, computes the fixed-point
varieties of several landmark rules exactly:

* **Rule 0** (the null rule): a single point, `V = {0}` (dimension `0`).
* **Rule 204** (the identity rule): the whole space, `V = GF(2)^n` (dimension `n`).
* **Rule 51** (global complement): the empty variety.
* **Rule 170 / 240** (the two shift rules): the diagonal line of constant
  configurations (dimension `1`).
* **Rules 90 and 150** (the additive rules): linear subspaces, cut out
  respectively by the Fibonacci recurrence `s(i+1) = s i + s(i-1)` and by
  two-periodicity `s(i+2) = s i`.
* **Rule 110** (the Turing-complete rule): a single point, `V = {0}`
  (dimension `0`).

The last computation is the central finding.  It shows that the naïve conjecture
"dynamical complexity equals fixed-point dimension" is *false*, and in the
strongest possible way: the computationally universal Rule 110 has the *smallest*
possible fixed-point variety, while the dynamically trivial identity Rule 204 has
the *largest*.

-- !-- Lab Notes -- !--

HYPOTHESIS (Hypothesizer).  Reading each ECA as a degree-≤3 polynomial map over
`GF(2)`, its fixed points form an algebraic variety `V(g)`.  Bold conjecture
(from the mission brief): `dim V(g)` tracks Wolfram's complexity class, so that
the Turing-complete Rule 110 attains the maximal dimension `n`.

EXPERIMENT (Experimenter).  We computed `|V(g)|` for the additive and landmark
rules on cyclic lattices up to length `14`.  Rule 204 gives `2^n` (full space);
Rule 90 gives `4` when `3 ∣ n` and `1` otherwise (the Fibonacci/Pisano period
`3` over `GF(2)`); Rule 150 gives `4` for even `n` and `2` for odd `n`
(two-periodicity); Rule 110 gives `1` for every tested length.

ANALYSIS (Analyst).  The additive rules are exactly the ones whose variety is a
*linear* subspace — they are the tractable, "Class-2" world, and their dimension
is governed by elementary number theory (Pisano periods, parities).  Rule 110 is
genuinely cubic, and its variety collapses to the origin.

CRITIQUE (Critic).  The brief's conjecture is refuted, not confirmed: Rule 110
(Class 4) has dimension `0`, Rule 204 (Class 2) has dimension `n`.  The corrected,
provable statement is a precise classification of the additive varieties plus the
`rule110_fixed_iff_zero` collapse theorem.  No result below is `True`, a
definitional `rfl`, or a bare `decide`; the counting corollaries are explicitly
labelled as computational evidence.

SYNTHESIS (Principal Investigator).  "An ECA is an algebraic variety" is correct;
"its dimension measures its complexity" is not.  The honest invariant separating
additive from universal rules is *linearity of the variety*, not its dimension.
-/

open CellularAutomataVariety





/-! ## The landmark local rules, as `GF(2)`-polynomials -/


/-! ## A propagation lemma on the cycle

Adding `1` generates `ZMod n`, so any property inherited from a cell to its right
neighbour and holding somewhere holds everywhere. -/


/-! ## Rule 0 — a single point (dimension 0) -/


/-! ## Rule 204 — the whole space (dimension n) -/


/-! ## Rule 51 — the empty variety -/


/-! ## Rules 170 and 240 — the constant line (dimension 1) -/



/-! ## Rule 90 — a linear variety cut out by the Fibonacci recurrence -/






/-! ## Rule 150 — a linear variety cut out by two-periodicity -/






/-! ## Rule 110 — the collapse to a single point (dimension 0)

The central theorem.  Despite being computationally universal, Rule 110 has the
*smallest possible* fixed-point variety: a single point. -/





open CellularAutomataVariety in
theorem solution{n : ℕ} [NeZero n] (P : ZMod n → Prop)
    (hstep : ∀ i, P i → P (i + 1)) {i0 : ZMod n} (h0 : P i0) : ∀ j, P j := by
  have hnat : ∀ k : ℕ, P (i0 + (k : ZMod n)) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ m ih =>
        have hm := hstep _ ih
        have e : (i0 + ((m + 1 : ℕ) : ZMod n)) = (i0 + (m : ZMod n)) + 1 := by push_cast; ring
        rw [e]; exact hm
  intro j
  have hj : j = i0 + ((j - i0).val : ZMod n) := by
    rw [ZMod.natCast_val, ZMod.cast_id]; ring
  rw [hj]; exact hnat _
