-- Prove2me | Theorems.Thm_BerggrenZeta_blocks_injective
-- name    : BerggrenZeta.blocks_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-14T01:23:01.061769+00:00
-- url     : https://prove2.me/theorems/9bb20096-43e5-45ee-824d-ff8363a4baec
-- title:
--   Distinct bit strings label distinct nodes of the Berggren tree.
-- statement:
--   Distinct bit strings label distinct nodes of the Berggren tree.
--
--   ```lean
--   theorem BerggrenZeta.blocks_injective: Function.Injective blocks := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BerggrenTreeHyperbolicSubtree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BerggrenTreeHyperbolicSubtree.lean#L62

-- Thm stub generated from Novelty/BerggrenTreeHyperbolicSubtree.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeHyperbolicSubtree
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth

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

open BerggrenZeta

-- open removed: section is not a namespace

/-! ## Part A. The block subtree -/

theorem BerggrenZeta.blocks_injective: Function.Injective blocks := by sorry
