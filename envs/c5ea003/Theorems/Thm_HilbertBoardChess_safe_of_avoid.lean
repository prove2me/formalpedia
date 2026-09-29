-- Prove2me | Theorems.Thm_HilbertBoardChess_safe_of_avoid
-- name    : HilbertBoardChess.safe_of_avoid
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:35.787988+00:00
-- url     : https://prove2.me/theorems/4e6ec460-3689-44a9-bec9-25e70a79728a
-- title:
--   Safe-square core.
-- statement:
--   **Safe-square core.**  If `x` avoids every rook's first coordinate and `y`
--   every rook's second coordinate, the square with those two entries (and zeros
--   elsewhere) is unattacked: it differs from every rook in two coordinates, so it
--   cannot lie on any single axis-line.
--
--   ```lean
--   theorem HilbertBoardChess.safe_of_avoid{d : ℕ} (R : Finset (Sq d)) (x y : ℤ)
--       (hx : x ∉ R.image (fun r => r 0)) (hy : y ∉ R.image (fun r => r 1)) :
--       ¬ attackedBy R (fun i => if i = 0 then x else if i = 1 then y else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/HilbertBoardChess.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/HilbertBoardChess.lean#L145

-- Thm stub generated from Applications/HilbertSpace/HilbertBoardChess.lean
import Mathlib
import Definitions.Def_Applications_HilbertSpace_HilbertBoardChess

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

open HilbertBoardChess

/-! ## The Hilbert board in dimension `d + 2` -/







/-! ## The single-rook escape map -/





/-! ## The infinite escape run -/

theorem HilbertBoardChess.safe_of_avoid{d : ℕ} (R : Finset (Sq d)) (x y : ℤ)
    (hx : x ∉ R.image (fun r => r 0)) (hy : y ∉ R.image (fun r => r 1)) :
    ¬ attackedBy R (fun i => if i = 0 then x else if i = 1 then y else 0) := by sorry
