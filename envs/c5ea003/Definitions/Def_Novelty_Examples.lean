-- Prove2me | Definitions.Def_Novelty_Examples
-- name    : Novelty_Examples
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:27.720334+00:00
-- url     : https://prove2.me/theorems/4bc2fde9-3c1f-4c0e-a20c-b8163aea7487
-- title:
--   Aether Catalog definitions — Novelty_Examples
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Examples`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Examples.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_AFLMatching_Basic

/-!
# A finite witness that the AFL fraction `1/(r+t-1)` is only *asymptotic*

The AFL prediction for `r = t = 2` is a monochromatic matching of size at least
`n/(r+t-1) = n/3`.  For `n = 4` this clean fraction reads `4/3`, so a naive (non-asymptotic)
reading would demand a monochromatic matching of size `≥ 2`.

Here we exhibit an explicit `2`-colouring of the edges of the complete graph `K₄` whose
*every* monochromatic matching has size `≤ 1`.  Hence the clean fraction `n/(r+t-1)` is
violated on small hosts — the `-o(1)` slack in the AFL statement is genuinely necessary,
not cosmetic.

The colouring: an edge gets colour `0` iff it contains vertex `0`, else colour `1`.
* The colour-`0` class is the star at `0`, so any two of its edges meet — no matching of size 2.
* The colour-`1` class lives on `{1,2,3}` (3 vertices), too few for two disjoint edges.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Could AFL's `n/(r+t-1)` hold *exactly* (without the `-o(1)`)
on the complete host?  Test the smallest interesting instance `n=4, r=t=2`.

Experiment (Experimenter): Brute-force (`decide`) over all sub-collections of `K₄`'s edge
set the statement "matching + monochromatic ⟹ size ≤ 1".  It holds.

Analysis (Analyst): FALSE that the clean fraction holds for finite `n`: the star/triangle
colouring caps every monochromatic matching at `1 < 4/3`.  So AFL is inherently asymptotic;
the `-o(1)` cannot be removed.  This sharpens the Critic's worry about "corner cases".

Critique (Critic): The witness is a genuine matching obstruction (not vacuous): both
colour classes are nonempty and the cap is exactly `1`, matched by the general lower bound
`mono_matching_lower_bound` (which forces a nonempty monochromatic matching here).

Synthesis (PI): Concrete boundary data complementing the general bounds in `Bounds.lean`.
-/

namespace AFLMatching

open Finset

/-- The edge set of the complete graph `K₄`: all `2`-element subsets of `Fin 4`. -/
abbrev K4 : Finset (Finset (Fin 4)) := (Finset.univ : Finset (Fin 4)).powersetCard 2

/-- The 2-colouring: colour `0` for edges through vertex `0`, colour `1` otherwise. -/
def c4 (e : Finset (Fin 4)) : Fin 2 := if (0 : Fin 4) ∈ e then 0 else 1



end AFLMatching


