-- Prove2me | Theorems.Thm_BerggrenZeta_count_ge_silver_rpow
-- name    : BerggrenZeta.count_ge_silver_rpow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-14T01:23:25.749218+00:00
-- url     : https://prove2.me/theorems/d1f774c8-4caf-4d31-8d2a-7c61e7ed6aeb
-- title:
--   The silver exponent is a counting exponent.
-- statement:
--   **The silver exponent is a counting exponent.**
--   For `H ≥ 5` the number of Berggren nodes with hypotenuse at most `H` is at least
--   `(1/3)·(H/5)^{σ₀}`, where `σ₀ = log 3 / (2 log(1+√2))` is the silver abscissa.
--   Combined with `nodesBelow_ncard_le` (`N(H) = O(H)`) and `silverAbscissa_lt_one`, this shows
--   the silver value is a genuine lower growth exponent but not the true one.
--
--   ```lean
--   theorem BerggrenZeta.count_ge_silver_rpow{H : ℕ} (hH : 5 ≤ H) :
--       (1 / 3 : ℝ) * ((H : ℝ) / 5) ^ silverAbscissa ≤ ((nodesBelow H).ncard : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BerggrenTreeCounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BerggrenTreeCounting.lean#L121

-- Thm stub generated from Novelty/BerggrenTreeCounting.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeCounting
import Definitions.Def_Novelty_BerggrenTreeCriticalLine
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth

/-!
# Counting Berggren nodes below a height: the silver exponent as a lower bound

Let `N(H) = #{ w : c(w) ≤ H }` be the number of nodes of the Berggren tree whose hypotenuse
is at most `H`.  This file proves the two-sided estimate

* `nodesBelow_ncard_le` : `N(H) ≤ (⌊√H⌋ + 1)²`, so `N(H) = O(H)` — a consequence of the
  seed injectivity of `Novelty.BerggrenTreeZetaCore`, since a node with `c(w) = m²+n² ≤ H`
  has both Euclid parameters in `[0, √H]`;
* `silver_count_lower` / `count_ge_silver_rpow` : `N(H) ≥ 3^d` whenever `5(3+2√2)^d ≤ H`,
  hence `N(H) ≥ (1/3)·(H/5)^{σ₀}` with `σ₀ = log 3 / (2 log(1+√2))` the *silver abscissa*
  of `Novelty.BerggrenTreeCriticalLine`.

Together with `silverAbscissa_lt_one` this pins down the role of the silver exponent
exactly: the silver value `σ₀ ≈ 0.6237` is the growth exponent of the **depth-graded**
(purely exponential) model of the tree, and it is a genuine *lower* bound for the counting
function, but it is strictly smaller than the true abscissa of convergence `1` computed in
`Novelty.BerggrenTreeZetaAbscissa`.  The gap between `H^{σ₀}` and `H` is produced by the
polynomially growing outer spines (`Lspine_hyp`, `Rspine_hyp`), which contribute nodes far
below the silver speed limit.

## Lab notes (computed with `#eval` on the definitions of this development)

| `H`   | nodes with `c(w) ≤ H` | `(⌊√H⌋+1)²` | largest `d` with `5(3+2√2)^d ≤ H` | `3^d` |
|-------|----------------------|--------------|-----------------------------------|-------|
| 5     | 1                    | 9            | 0                                 | 1     |
| 50    | 7                    | 64           | 1                                 | 3     |
| 200   | 32                   | 225          | 2                                 | 9     |
| 1000  | 158                  | 1024         | 3                                 | 27    |

The counts (1, 7, 32, 158) — obtained by enumerating the admissible Euclid seeds `(m,n)`
with `m²+n² ≤ H`, which by `seedEquiv` is exactly the node count — confirm both bounds and
show that the truth sits strictly between `3^d ≍ H^{σ₀}` and `(√H+1)²`, in line with the
abscissa-`1` theorem (the counts grow essentially linearly in `H`).
-/

open BerggrenZeta

-- open removed: section is not a namespace







/-! ## Lower bound: the depth-`d` slice -/



/-! ## The silver exponent as a counting exponent -/

theorem BerggrenZeta.count_ge_silver_rpow{H : ℕ} (hH : 5 ≤ H) :
    (1 / 3 : ℝ) * ((H : ℝ) / 5) ^ silverAbscissa ≤ ((nodesBelow H).ncard : ℝ) := by sorry
