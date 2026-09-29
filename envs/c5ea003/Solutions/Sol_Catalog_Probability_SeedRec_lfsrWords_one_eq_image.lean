-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsrWords_one_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:24:50.861526+00:00
-- url     : https://prove2.me/submissions/3ed8604d-bb21-43eb-b675-a00ac4ba9c8e

-- Sol generated from Probability/PRNGEnumerationL1.lean
import Mathlib
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGEnumerationL1
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGRouterCapacity
import Definitions.Def_Probability_PRNGSeedRecovery
import Theorems.Thm_Catalog_Probability_SeedRec_mem_lfsrWords
import Theorems.Thm_Catalog_Probability_SeedRec_order_one_stream

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



theorem lfsr_pref_one (c σ : Fin 1 → K) (n : ℕ) :
    (lfsrPRNG c).pref n σ = geomWord n (σ 0, c 0) := by
  funext i
  simpa [geomWord] using order_one_stream c σ (i : ℕ)

variable (K) [Fintype K] [DecidableEq K]

















open Catalog.Probability.SeedRec in
theorem solution(n : ℕ) :
    lfsrWords K 1 n = (geomParams K).image (geomWord n) := by
  ext x
  constructor
  · intro hx
    rw [mem_lfsrWords] at hx
    obtain ⟨c, σ, hcσ⟩ := hx
    rw [lfsr_pref_one] at hcσ
    by_cases hs : σ 0 = 0
    · refine Finset.mem_image.2 ⟨(0, 0), ?_, ?_⟩
      · simp [geomParams]
      · rw [← hcσ]
        funext i
        rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
        · simp [geomWord, hi, hs]
        · simp [geomWord, hs, zero_pow (by omega : (i : ℕ) ≠ 0)]
    · exact Finset.mem_image.2 ⟨(σ 0, c 0), by simp [geomParams, hs], hcσ⟩
  · intro hx
    obtain ⟨p, _, hp⟩ := Finset.mem_image.1 hx
    rw [mem_lfsrWords]
    exact ⟨fun _ => p.2, fun _ => p.1, by rw [lfsr_pref_one]; exact hp⟩
