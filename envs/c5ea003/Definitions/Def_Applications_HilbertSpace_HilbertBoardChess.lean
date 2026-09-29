-- Prove2me | Definitions.Def_Applications_HilbertSpace_HilbertBoardChess
-- name    : Applications_HilbertSpace_HilbertBoardChess
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:49.125752+00:00
-- url     : https://prove2.me/theorems/34f03b08-a595-4228-994b-53d3082d8027
-- title:
--   Aether Catalog definitions — Applications_HilbertSpace_HilbertBoardChess
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.HilbertSpace.HilbertBoardChess`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/HilbertSpace/HilbertBoardChess.lean by skeleton subtraction
import Mathlib

/-!
# Winning on the Hilbert Board: King Escape in Every Dimension

We lift the theory of *infinite-board chess* from the classical plane `ℤ × ℤ` to
the **`d`-dimensional Hilbert board** `ℤ^{d+2}`, the natural setting for
"infinite-dimensional chess".  Passing from two to arbitrarily many spatial
dimensions only *helps* the fleeing king: the more directions there are, the more
room to run.  We make this precise.

## Model

Fix a dimension parameter `d : ℕ`; the board is `Sq d := Fin (d + 2) → ℤ`, so it
always has at least two coordinate axes.

* Two squares are **king-adjacent** (`kingAdj`) when they are distinct and every
  coordinate differs by at most one — the Chebyshev unit ball, i.e. the
  `3^{d+2} - 1` neighbours of a chess king.
* A **rook** on `r` **attacks** `s` (`rookAttacks`) when `s ≠ r` and `s` agrees
  with `r` in **all but one** coordinate: the rook sweeps a full axis-parallel
  line through its own square.  A rook does not attack its own square, so an
  undefended checker may always be captured.
* A finite rook army `R` **checkmates** the king (`Checkmated`) when the king is
  in check and every king-adjacent square is attacked.

## Main results

* `king_escape_single_rook`, `king_escapes_forever`: against a lone rook the king
  always has an explicit safe step (`gStep`), and hence an *infinite* legal
  escape run, in every dimension `d + 2 ≥ 2`.
* `single_rook_no_mate`: a lone rook can never checkmate, in any dimension.
* `exists_safe_square`, `infinitely_many_safe`: any finite army leaves
  infinitely many completely unattacked squares — finitely many lines cannot
  cover a plane, a fortiori a higher-dimensional board.
* `single_rook_never_traps`: in the language of combinatorial game theory the
  lone-rook position is **not accessible** for the pursuit relation, so it carries
  *no ordinal game value*: the transfinite signature of an unbreakable fortress,
  now established uniformly across all dimensions.
* `one_dim_two_rooks_mate`: the **boundary case**.  In a single dimension a rook
  attacks every other square, so two mutually defending rooks *do* checkmate the
  king — a phenomenon impossible in dimension `≥ 2`.  The escape is genuinely a
  higher-dimensional effect.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The planar escape results should be *dimension-robust*:
adding axes cannot help the pursuer.  Boldly, we conjectured the entire
lone-rook fortress — geometric escape, infinite run, and transfinite
inaccessibility — survives verbatim on `ℤ^{d+2}` for every `d`, while collapsing
in dimension one.

Experiment (Experimenter): We generalised the coordinatewise escape map `escC`
to `gStep r p := fun i => escC (p i) (r i)`, which moves *every* coordinate away
from the rook at once (a legal king step in the Chebyshev metric).  The image
disagrees with the rook in *all* coordinates, so it cannot lie on any single
axis-line through the rook; hence it is unattacked.  Iterating yields the
infinite run, and the same accessibility argument as in the plane shows the
position has no ordinal rank.  For the safe-square count we avoided the rooks'
projections on the first two axes, leaving an infinite family of safe squares.

Analysis (Analyst): The proofs are "true and structural": the sole obstruction to
mate is again the missing boundary, captured by "finitely many lines miss a
plane".  The dimension enters only through the existence of *two distinct axes*
(`i0 ≠ i1`), which is exactly what fails in dimension one — pinpointing the
threshold.

Critique (Critic): We verified that the escape square is genuinely empty (off
every axis-line through the rook) and that `Checkmated` still permits capturing a
lone checker.  The one-dimensional boundary theorems confirm the hypotheses are
sharp: with a single axis two mutually defending rooks deliver mate.

Synthesis (PI): "The king always escapes" is a phenomenon of dimension `≥ 2`,
robust to *unboundedly many* extra dimensions, and its honest invariant remains
the accessibility rank of the pursuit relation — an ordinal that, for the
lone-rook fortress, does not exist.
-/

namespace HilbertBoardChess

/-! ## The Hilbert board in dimension `d + 2` -/

/-- A square of the `(d+2)`-dimensional board. -/
abbrev Sq (d : ℕ) := Fin (d + 2) → ℤ

/-- Two squares are king-adjacent: distinct, Chebyshev distance one. -/
def kingAdj {d : ℕ} (p q : Sq d) : Prop := p ≠ q ∧ ∀ i, |p i - q i| ≤ 1

/-- A rook on `r` attacks `s` if `s ≠ r` and they agree in all but one
coordinate (the rook sweeps one axis-parallel line). -/
def rookAttacks {d : ℕ} (r s : Sq d) : Prop :=
  s ≠ r ∧ ∃ j, ∀ i, i ≠ j → s i = r i

/-- Some rook of the army `R` attacks `s`. -/
def attackedBy {d : ℕ} (R : Finset (Sq d)) (s : Sq d) : Prop :=
  ∃ r ∈ R, rookAttacks r s



/-! ## The single-rook escape map -/

/-- Escape coordinate: from `a`, step to a neighbour distinct from the rook's
coordinate `c`.  Always lands on `a - 1` or `a + 1`. -/
def escC (a c : ℤ) : ℤ := if c = a + 1 then a - 1 else a + 1


/-- The king's explicit escape step: move every coordinate away from the rook. -/
def gStep {d : ℕ} (r p : Sq d) : Sq d := fun i => escC (p i) (r i)


/-! ## The infinite escape run -/



/-! ## Finitely many rooks cannot cover the board -/



/-! ## Checkmate: the lone rook never mates -/

/-- The king at `k` is **checkmated** by `R`: in check, with every adjacent
square attacked. -/
def Checkmated {d : ℕ} (R : Finset (Sq d)) (k : Sq d) : Prop :=
  attackedBy R k ∧ ∀ s, kingAdj k s → attackedBy R s


/-! ## The ordinal game value: the lone-rook king is inaccessible -/

/-- The king can safely step from `p` to `q` against rook `r`. -/
def KingStep {d : ℕ} (r p q : Sq d) : Prop := kingAdj p q ∧ ¬ rookAttacks r q

/-- The pursuit against `r` **traps** the king at `k` when `k` is accessible for
the safe-move relation: every play terminates and the position carries an
ordinal game value (its accessibility rank). -/
def AttackerWins {d : ℕ} (r k : Sq d) : Prop :=
  Acc (fun q p => KingStep r p q) k



/-! ## Boundary case: the one-dimensional line

Modelling the line as `ℤ`, a rook attacks *every* other square (with a single
axis, "agree in all but one coordinate" imposes no constraint).  The dimension
threshold now appears crisply: two rooks that would *never* mate on the plane
**do** mate on the line, because each checker is defended by the other. -/

/-- Adjacency on the one-dimensional line. -/
def kingAdj1 (p q : ℤ) : Prop := p ≠ q ∧ |p - q| ≤ 1

/-- On the line a rook attacks every square other than its own. -/
def rookAttacks1 (r s : ℤ) : Prop := s ≠ r

/-- Some rook of `R` attacks `s` on the line. -/
def attackedBy1 (R : Finset ℤ) (s : ℤ) : Prop := ∃ r ∈ R, rookAttacks1 r s

/-- Checkmate on the line. -/
def Checkmated1 (R : Finset ℤ) (k : ℤ) : Prop :=
    attackedBy1 R k ∧ ∀ s, kingAdj1 k s → attackedBy1 R s


/-! ## Examples, generalizations, and boundaries

**Examples.**  Concrete instantiations of the definitions and theorems. -/

-- The three-dimensional board (`d = 1`, i.e. `ℤ^3`).
-- On `ℤ^3`, the origin steps to the all-ones square to flee a rook at the origin.
-- A concrete safe square exists against any finite army on `ℤ^2`.
/-
**Generalization.**  The escape argument depends on the ambient dimension only
through the existence of two distinct axes (`exists_axis_ne`).  Consequently the
entire lone-rook fortress — one-step escape, infinite run, and transfinite
inaccessibility — is a single theorem schema valid for *every* `d`, an unbounded
family of dimensions.  The natural further extension replaces `Fin (d+2)` by an
arbitrary index type with at least two elements, capturing a genuinely
infinite-dimensional Hilbert board for the covering (safe-square) results.

**Boundary.**  The threshold is exactly two axes.  In dimension one
(`one_dim_two_rooks_mate`) two rooks *do* checkmate, because each checker is
defended by the other and cannot be captured — the direct counterexample to the
higher-dimensional "no mate" phenomenon.  Thus the results are sharp: they hold
for all `d ≥ 0` (dimension `≥ 2`) and fail in dimension one.
-/

end HilbertBoardChess


