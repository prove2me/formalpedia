-- Prove2me | Definitions.Def_Combinatorics_QuartetCodesSmallCases
-- name    : Combinatorics_QuartetCodesSmallCases
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:48:55.477401+00:00
-- url     : https://prove2.me/theorems/c845aaf4-f267-46e7-8a04-501ea85cfe46
-- title:
--   Aether Catalog definitions — Combinatorics_QuartetCodesSmallCases
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.QuartetCodesSmallCases`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/QuartetCodesSmallCases.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesUpperBound

/-!
# Small-case quartet codes: three caterpillars on nine leaves avoid every quartet

The first-moment bound of `Combinatorics.QuartetCodes` needs `4v + 2` trees to defeat `3^v`
leaves, so at `n = 9 = 3^2` it only produces a family of ten trees.  Here we exhibit an *explicit*
family of **three** leaf orders on nine leaves whose caterpillars pairwise resolve every quartet
differently enough that no four leaves carry a common quartet.  Together with the
Erdős–Szekeres upper bound `caterpillar_family_common_quartet` this brackets the least leaf number
`h(3)` forcing a common quartet among three caterpillars:

```
10 ≤ h(3) ≤ 6562 .
```

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
The random-code lower bound is exponentially wasteful in the number of trees; concrete small codes
should beat it badly.  Concretely: three trees should already avoid a common quartet on far more
than five leaves.

## Experiment (Experimenter)
A local search over triples of leaf orders (cost = number of quartets on which all three agree)
was run for `n = 6, …, 14`.  Avoiding triples exist for `n ≤ 9` and were never found for `n ≥ 10`;
the search residue grows steadily (`1, 3, 8, 15, 27` constant quartets at `n = 10, …, 14`), which is
strong evidence that `h(3) = 10` exactly.  One of the `n = 9` solutions is hard-coded below and
verified by kernel evaluation over all `9^4` ordered quadruples.

## Analysis (Analyst)
`h(2) = 6` (computed exhaustively) and `h(3) = 10` (conjectural) against the proved bracket
`10 ≤ h(3) ≤ 6562` shows that the Erdős–Szekeres upper bound is the loose side, not the
construction side.  The empirical growth of the largest avoiding leaf number in the family size
`k` is `5, 9, 16, ~20, ~30` for `k = 2, 3, 4, 5, 6`, i.e. a ratio near `1.7` per extra tree —
comfortably exponential, and above the `3^{1/4} ≈ 1.316` per-tree rate that the first-moment
argument certifies.

## Critique (Critic)
The nine-leaf statement is a genuine universally quantified claim over all ordered quadruples of
distinct leaves, discharged by kernel `decide` (not `native_decide`); the permutations are given
with explicit two-sided inverses, so no classical choice enters their definition.
-/

open Finset AgreementSubtrees

namespace QuartetCodes


/-- The leaf order `0 ↦ 7, 1 ↦ 0, 2 ↦ 2, 3 ↦ 5, 4 ↦ 4, 5 ↦ 3, 6 ↦ 1, 7 ↦ 8, 8 ↦ 6`. -/
def order9a : Equiv.Perm (Fin 9) :=
  ⟨![7, 0, 2, 5, 4, 3, 1, 8, 6], ![1, 6, 2, 5, 4, 3, 8, 0, 7], by decide, by decide⟩

/-- The leaf order `0 ↦ 6, 1 ↦ 5, 2 ↦ 1, 3 ↦ 3, 4 ↦ 4, 5 ↦ 2, 6 ↦ 7, 7 ↦ 8, 8 ↦ 0`. -/
def order9b : Equiv.Perm (Fin 9) :=
  ⟨![6, 5, 1, 3, 4, 2, 7, 8, 0], ![8, 2, 5, 3, 4, 1, 0, 6, 7], by decide, by decide⟩





end QuartetCodes


