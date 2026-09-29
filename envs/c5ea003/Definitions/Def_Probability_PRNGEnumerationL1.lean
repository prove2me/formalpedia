-- Prove2me | Definitions.Def_Probability_PRNGEnumerationL1
-- name    : Probability_PRNGEnumerationL1
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:32.442658+00:00
-- url     : https://prove2.me/theorems/fe6e8d63-4249-4a1f-bf10-4ce67c428c86
-- title:
--   Aether Catalog definitions — Probability_PRNGEnumerationL1
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGEnumerationL1`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGEnumerationL1.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGRouterCapacity

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

namespace Catalog.Probability.SeedRec

open Finset

section OrderOne

variable {K : Type*} [Field K]


/-- The length-`n` word emitted by the order-one register with tap `c` and seed
`s`: the geometric word. -/
def geomWord (n : ℕ) (p : K × K) : Fin n → K := fun i => p.2 ^ (i : ℕ) * p.1


variable (K) [Fintype K] [DecidableEq K]

/-- The parameter set that enumerates the order-one family without repetition:
all pairs with nonzero seed, plus the single degenerate pair `(0,0)`. -/
def geomParams : Finset (K × K) :=
  (({0}ᶜ : Finset K) ×ˢ (univ : Finset K)) ∪ {(0, 0)}











end OrderOne

section SmallCases


end SmallCases

end Catalog.Probability.SeedRec


