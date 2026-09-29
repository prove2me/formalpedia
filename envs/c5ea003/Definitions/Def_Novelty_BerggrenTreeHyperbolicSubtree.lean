-- Prove2me | Definitions.Def_Novelty_BerggrenTreeHyperbolicSubtree
-- name    : Novelty_BerggrenTreeHyperbolicSubtree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-14T01:20:12.249793+00:00
-- url     : https://prove2.me/theorems/7efdebb9-aabd-46d9-8521-6eec985510e2
-- title:
--   Aether Catalog definitions — Novelty_BerggrenTreeHyperbolicSubtree
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BerggrenTreeHyperbolicSubtree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BerggrenTreeHyperbolicSubtree.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# Purely hyperbolic subtrees: the abscissa drops below `1`

The abscissa of convergence of the full Berggren tree zeta is `1`
(`Novelty.BerggrenTreeZetaAbscissa`), not the silver value `σ₀`; the reason is that two of
the three branches grow only polynomially (`Lspine_hyp`, `Rspine_hyp`).  This file isolates
the mechanism by removing the parabolic directions.

Consider the free binary subtree spanned by the two blocks

* `MM`  (`blockList true  = [1,1]`), and
* `MR`  (`blockList false = [1,2]`),

each of which contains the hyperbolic Pell move `M`.  Write `blocks bs` for the Berggren
word obtained by concatenating the blocks of a bit string `bs`.  Then:

* `blocks_injective` — distinct bit strings give distinct nodes, so the subtree really is a
  free binary tree inside the ternary Berggren tree;
* `hyp_blocks_lower` / `hyp_blocks_upper` — `5 (5/2)^d ≤ c(blocks bs) ≤ 5 (3+2√2)^{2d}` for
  a bit string of length `d`: every block is *expanding*, unlike the pure `R` direction;
* `summable_subtree` — the subtree zeta converges for `s > log 2 / log(5/2) ≈ 0.7565`;
* `not_summable_subtree` — and diverges for `0 < s < log 2 / log((3+2√2)²) ≈ 0.1963`;
* `subtree_summable_at_one` — in particular it **converges at `s = 1`**, where the full tree
  zeta diverges.

So the abscissa of the hyperbolic subtree lies in `[0.196, 0.757] ⊂ (0,1)`: the silver-type
prediction "abscissa = log(branching)/log(growth)" is qualitatively correct once the
parabolic generators are removed, and the failure of the silver abscissa for the full tree
is entirely due to them.
-/

namespace BerggrenZeta

open Real

/-! ## Part A. The block subtree -/

/-- The two hyperbolic blocks: `true ↦ MM`, `false ↦ MR`. -/
def blockList : Bool → List (Fin 3)
  | true => [1, 1]
  | false => [1, 2]

/-- The Berggren word obtained by concatenating blocks. -/
def blocks : List Bool → List (Fin 3)
  | [] => []
  | b :: bs => blockList b ++ blocks bs






/-! ## Part B. Every block expands -/







/-! ## Part C. The subtree zeta -/

/-- The subtree zeta term, indexed by `(depth in blocks, choice of blocks)`. -/
noncomputable def subtreeTerm (s : ℝ) (p : (d : ℕ) × (Fin d → Bool)) : ℝ :=
  (hyp (blocks (List.ofFn p.2)) : ℝ) ^ (-s)





end BerggrenZeta


