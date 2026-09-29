-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_order_one_stream
-- name    : Catalog.Probability.SeedRec.order_one_stream
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:10:45.021679+00:00
-- url     : https://prove2.me/theorems/aad88f05-680e-4865-8e19-fd2eda7cdb1f
-- title:
--   The order-one register over a field is multiplication by the single tap:
-- statement:
--   The order-one register over a field is multiplication by the single tap:
--   its output is the geometric sequence `t ↦ cᵗ · s`.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.order_one_stream(c σ : Fin 1 → K) (t : ℕ) :
--       (lfsrPRNG c).stream σ t = c 0 ^ t * σ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGEnumerationL1.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGEnumerationL1.lean#L45

-- Thm stub generated from Probability/PRNGEnumerationL1.lean
import Mathlib
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGEnumerationL1
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGRouterCapacity
import Definitions.Def_Probability_PRNGSeedRecovery

/-!
# Exact enumeration of the linear-complexity filtration at order one (conjecture C1)

`FUTURE_DIRECTIONS.md` conjectures that over a finite field `K` with `q = |K|`
elements and for `n ≥ 2L`,
```
|lfsrWords K L n| = (q^{2L+1} + 1) / (q + 1),
```
a value bracketed by the proved bounds `q^L ≤ |lfsrWords K L n| ≤ q^{2L}`.  This
file **settles the case `L = 1`**, where the conjectured value is
`(q³ + 1) / (q + 1) = q² - q + 1`.

The order-one register over a field is the map `x ↦ c · x`, so its output is the
geometric word `x_t = cᵗ · s`.  Two facts drive the count:

* if the seed `s` is nonzero the pair `(s, c)` is *recoverable* from the first
  two symbols (`c = x₁ / x₀`), giving `q(q - 1)` distinct words;
* if the seed is zero the word is the all-zero word, whatever the taps.

So the order-one family has exactly `q(q-1) + 1 = q² - q + 1` members — strictly
between the general bounds `q` and `q²`, confirming that both are loose.

Main contents.

* `order_one_stream` — the order-one LFSR emits the geometric sequence `cᵗ s`.
* `lfsrWords_one_eq_image` — the order-one family is the image of the explicit
  parameter set `{(s, c) : s ≠ 0} ∪ {(0,0)}`.
* `card_lfsrWords_one` — **the exact count** `q² - q + 1`, for every `n ≥ 2`.
* `card_lfsrWords_one_eq_conjectured` — the same number written in the
  conjectured closed form `(q³ + 1) / (q + 1)`.
* `card_lfsrWords_one_lt_pow` — the count is *strictly* below the general upper
  bound `q^{2L}`, so the pigeonhole ceiling of `card_lfsrWords_le` is not tight.
-/

open Catalog.Probability.SeedRec

open Finset


variable {K : Type*} [Field K]

theorem Catalog.Probability.SeedRec.order_one_stream(c σ : Fin 1 → K) (t : ℕ) :
    (lfsrPRNG c).stream σ t = c 0 ^ t * σ 0 := by sorry
