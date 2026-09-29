-- Prove2me | Definitions.Def_Applications_CellularAutomataVariety_Basic
-- name    : Applications_CellularAutomataVariety_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:19.38034+00:00
-- url     : https://prove2.me/theorems/c6bbc204-22a6-47b8-98fe-30224b74be0c
-- title:
--   Aether Catalog definitions — Applications_CellularAutomataVariety_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CellularAutomataVariety.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CellularAutomataVariety/Basic.lean by skeleton subtraction
import Mathlib

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

namespace CellularAutomataVariety

/-- The binary field `GF(2)`, the alphabet of an elementary cellular automaton. -/
abbrev Cell := ZMod 2

/-- A configuration on the cyclic lattice `ZMod n`. -/
abbrev Config (n : ℕ) := ZMod n → Cell

/-- The synchronous global update induced by a local rule `g` of the left
neighbour, the cell, and the right neighbour.  Indices are taken modulo `n`, so
the lattice is a cycle. -/
def step {n : ℕ} (g : Cell → Cell → Cell → Cell) (s : Config n) : Config n :=
  fun i => g (s (i - 1)) (s i) (s (i + 1))

/-- A configuration is *fixed* when the automaton leaves it unchanged; the set of
fixed configurations is the `GF(2)`-points of the fixed-point variety `V(g)`. -/
def IsFixed {n : ℕ} (g : Cell → Cell → Cell → Cell) (s : Config n) : Prop :=
  step g s = s

/-! ## The landmark local rules, as `GF(2)`-polynomials -/

/-- Rule 0: the constant `0` map. -/
def rule0 : Cell → Cell → Cell → Cell := fun _ _ _ => 0
/-- Rule 204: the identity rule `g(a,b,c) = b`. -/
def rule204 : Cell → Cell → Cell → Cell := fun _ b _ => b
/-- Rule 51: the global complement `g(a,b,c) = b + 1`. -/
def rule51 : Cell → Cell → Cell → Cell := fun _ b _ => b + 1
/-- Rule 170: the left shift `g(a,b,c) = c`. -/
def rule170 : Cell → Cell → Cell → Cell := fun _ _ c => c
/-- Rule 240: the right shift `g(a,b,c) = a`. -/
def rule240 : Cell → Cell → Cell → Cell := fun a _ _ => a
/-- Rule 90: the additive rule `g(a,b,c) = a + c`. -/
def rule90 : Cell → Cell → Cell → Cell := fun a _ c => a + c
/-- Rule 150: the additive rule `g(a,b,c) = a + b + c`. -/
def rule150 : Cell → Cell → Cell → Cell := fun a b c => a + b + c
/-- Rule 110: the Turing-complete rule.  Its multilinear `GF(2)`-polynomial is
`g(a,b,c) = b + c + b·c + a·b·c`, a genuine cubic. -/
def rule110 : Cell → Cell → Cell → Cell := fun a b c => b + c + b * c + a * b * c

/-! ## A propagation lemma on the cycle

Adding `1` generates `ZMod n`, so any property inherited from a cell to its right
neighbour and holding somewhere holds everywhere. -/


/-! ## Rule 0 — a single point (dimension 0) -/


/-! ## Rule 204 — the whole space (dimension n) -/


/-! ## Rule 51 — the empty variety -/


/-! ## Rules 170 and 240 — the constant line (dimension 1) -/



/-! ## Rule 90 — a linear variety cut out by the Fibonacci recurrence -/

/-- The update of Rule 90 as a `GF(2)`-linear endomorphism of configuration
space. -/
def step90L (n : ℕ) : Config n →ₗ[Cell] Config n where
  toFun s := fun i => s (i - 1) + s (i + 1)
  map_add' s t := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c s := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring


/-- The fixed-point variety of Rule 90 is the linear subspace `ker(step90L - id)`. -/
def Fixed90 (n : ℕ) : Submodule Cell (Config n) :=
  LinearMap.ker (step90L n - LinearMap.id)



/-! ## Rule 150 — a linear variety cut out by two-periodicity -/

/-- The update of Rule 150 as a `GF(2)`-linear endomorphism. -/
def step150L (n : ℕ) : Config n →ₗ[Cell] Config n where
  toFun s := fun i => s (i - 1) + s i + s (i + 1)
  map_add' s t := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c s := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring


/-- The fixed-point variety of Rule 150 is the linear subspace
`ker(step150L - id)`. -/
def Fixed150 (n : ℕ) : Submodule Cell (Config n) :=
  LinearMap.ker (step150L n - LinearMap.id)



/-! ## Rule 110 — the collapse to a single point (dimension 0)

The central theorem.  Despite being computationally universal, Rule 110 has the
*smallest possible* fixed-point variety: a single point. -/




end CellularAutomataVariety


