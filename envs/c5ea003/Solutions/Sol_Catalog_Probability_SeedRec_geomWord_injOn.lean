-- Prove2me | solution 1 for Catalog.Probability.SeedRec.geomWord_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:20:03.737226+00:00
-- url     : https://prove2.me/submissions/dbedfa4a-63a2-4127-a266-5c41ac1fee53

-- Sol generated from Probability/PRNGEnumerationL1.lean
import Mathlib
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGEnumerationL1
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

open Catalog.Probability.SeedRec

open Finset


variable {K : Type*} [Field K]




variable (K) [Fintype K] [DecidableEq K]


theorem mem_geomParams {p : K × K} : p ∈ geomParams K ↔ p.1 ≠ 0 ∨ p = (0, 0) := by
  simp only [geomParams, Finset.mem_union, Finset.mem_product, Finset.mem_compl,
    Finset.mem_singleton, Finset.mem_univ, and_true]















open Catalog.Probability.SeedRec in
theorem solution(n : ℕ) (hn : 2 ≤ n) :
    Set.InjOn (geomWord (K := K) n) (geomParams K) := by
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  intro p hp p' hp' h
  have e0 : p.1 = p'.1 := by
    have := congrFun h ⟨0, h0⟩
    simpa [geomWord] using this
  have e1 : p.2 * p.1 = p'.2 * p'.1 := by
    have := congrFun h ⟨1, h1⟩
    simpa [geomWord] using this
  by_cases hs : p.1 = 0
  · have hp0 : p = (0, 0) := by
      rcases (mem_geomParams K).1 (Finset.mem_coe.1 hp) with h' | h'
      · exact absurd hs h'
      · exact h'
    have hs' : p'.1 = 0 := by rw [← e0, hs]
    have hp0' : p' = (0, 0) := by
      rcases (mem_geomParams K).1 (Finset.mem_coe.1 hp') with h' | h'
      · exact absurd hs' h'
      · exact h'
    rw [hp0, hp0']
  · have hc : p.2 = p'.2 := by
      rw [← e0] at e1
      exact mul_right_cancel₀ hs e1
    exact Prod.ext e0 hc
