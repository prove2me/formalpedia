-- Prove2me | Theorems.Thm_KTaxonomy_pin_gap_one_iff_two_pow
-- name    : KTaxonomy.pin_gap_one_iff_two_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:51:55.055767+00:00
-- url     : https://prove2.me/theorems/e02a34e8-5a80-43ca-9945-757e4ca566fe
-- title:
--   The pin gap is `1` exactly at the dyadic widths `W = 2 ^ (k + 1)`.
-- statement:
--   **The pin gap is `1` exactly at the dyadic widths `W = 2 ^ (k + 1)`.**  Together with
--   `pin_gap_general` (gap `∈ {1, 2}`) this determines the gap at every integer width: it is
--   `2` unless the width sits exactly on the power of two just above the optimum.
--
--   ```lean
--   theorem KTaxonomy.pin_gap_one_iff_two_pow(W k : ℕ) (hW : 2 ≤ W)
--       (hk : ∀ j, census (W : ℝ) k ≤ census (W : ℝ) j) :
--       kPin W - k = 1 ↔ W = 2 ^ (k + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/KTaxonomyRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/KTaxonomyRigidity.lean#L123

-- Thm stub generated from Cryptography/KTaxonomyRigidity.lean
import Mathlib
import Definitions.Def_Cryptography_KTaxonomyCensusEcon

/-!
# Rigidity of the k-taxonomy: price rescaling, tie sets, and the exact pin gap

Round three of the taxonomy.  The previous two files fixed the three budgets and proved the
exact identities relating them at unit query price and the argmin brackets at general width.
Here we close the three questions those results left open.

* **Price is a pure anchor rescaling** (`econ_eq_census_price`,
  `econ_argmin_iff_census_argmin_price`): for every price `c_q > 0`,
  `econ T₀ c_q k = c_q ⬝ (census (2 (T₀ - 1) / c_q) k + 1/2)`, so the economics optimum at
  price `c_q` is *exactly* the census optimum at the rescaled anchor `2 (T₀ - 1) / c_q`.
  The two-parameter taxonomy therefore collapses to the one-parameter census family.
* **Tie dichotomy** (`census_tie_iff`, `census_argmin_unique_of_not_two_pow`): the census
  argmin is a two-element set exactly at the dyadic widths `W = 2 ^ (k + 2)`, and is a
  singleton at every non-dyadic width.  So "the" census optimum is well defined off the
  dyadic locus, and ambiguous exactly on it.
* **Exact pin gap** (`pin_gap_one_iff_two_pow`): for an integer width `W ≥ 2` and a census
  optimum `k`, the gap `kPin W - k` equals `1` **iff** `W = 2 ^ (k + 1)`, and equals `2`
  otherwise.  Combined with `pin_gap_general` this determines the gap completely.

-- !-- Lab Notes -- !--
Hypothesizer (round 3):
 (H9)  Price enters only through the anchor: argmin of `econ T₀ c_q` = argmin of
       `census (2 (T₀ - 1) / c_q)`.                                              [BOLD]
 (H10) Ties happen exactly at dyadic widths.
 (H11) The pin gap is `2` at *non*-dyadic widths and `1` only when the width is exactly
       `2 ^ (k + 1)`.

Analyst: H11 is the informative correction of this round.  The natural guess from the
dyadic table (`argmin = {m-2, m-1}`, pin `m`, gaps `{2, 1}`) is that gap `1` is generic and
gap `2` is the dyadic exception.  The truth is the opposite: at `W = 3` the unique optimum
is `k = 0` while the pin is `2`, so the gap is `2`; a gap of `1` requires the width to sit
exactly on the power of two `2 ^ (k + 1)`.  This is a "needs a different statement" outcome
rather than a failure: the corrected statement is proved below, and it says the pin
overstates the work-optimal budget by *two* queries at almost every width.
-/

open KTaxonomy

/-! ## Price is a pure anchor rescaling -/



/-! ## The tie dichotomy -/




/-! ## The exact pin gap -/

theorem KTaxonomy.pin_gap_one_iff_two_pow(W k : ℕ) (hW : 2 ≤ W)
    (hk : ∀ j, census (W : ℝ) k ≤ census (W : ℝ) j) :
    kPin W - k = 1 ↔ W = 2 ^ (k + 1) := by sorry
