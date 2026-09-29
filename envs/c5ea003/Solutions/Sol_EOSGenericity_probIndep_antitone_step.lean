-- Prove2me | solution 1 for EOSGenericity.probIndep_antitone_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T23:41:28.453004+00:00
-- url     : https://prove2.me/submissions/992a4b91-2d74-4a9b-94d7-26413d893387

-- Sol generated from NumberTheory/EOSExclusiveDimGenericity.lean
import Mathlib
import Definitions.Def_NumberTheory_EOSExclusiveDimGenericity
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
import Theorems.Thm_EOSGenericity_probIndep_eq_prod
/-
# Are the exclusive dimensions really exclusive?  A `q`-Pochhammer genericity bound

Companion to `Catalog/NumberTheory/EOSWidthMonotoneRamp.lean`.

The ramp model draws the boundary token's `k` exclusive directions uniformly at random from a
finite `𝔽_p`-space `V` of dimension `n`.  For the phrase "`k` exclusive dimensions" to be
honest, the `k` draws must actually be linearly independent.  This file quantifies that:

* `EOSGenericity.probIndep_eq_prod` — the probability that `k ≤ n` uniform draws are linearly
  independent is exactly the `q`-Pochhammer product `∏_{i<k} (1 - p^{i-n})`
  (via Mathlib's `card_linearIndependent`);
* `EOSGenericity.one_sub_sum_le_prod_one_sub` — a Weierstrass product inequality, proved by
  induction;
* `EOSGenericity.probIndep_ge` — hence `P(independent) ≥ 1 - (p^k - 1)/((p-1) p^n)`: for
  `k ≪ n` the drawn directions are exclusive with overwhelming probability, so the model of
  the companion file is not vacuous;
* `EOSGenericity.probIndep_antitone_step` — genericity decays with `k`, in the opposite
  direction to the reliability ramp;
* `EOSGenericity.prob_indep_and_cure_ge` — **the synthesis**: with `k` exclusive dimensions the
  probability that the token both occupies a genuine `k`-dimensional subspace *and* escapes all
  `m` obstructions is at least

  `1 - m·p^{-k} - (p^k - 1)/((p-1)·p^n)`,

  a two-sided window: the first term (reliability) shrinks geometrically in `k`, the second
  (genericity) grows geometrically in `k`, so the optimal exclusive width is interior — there is
  a genuine trade-off and no cliff.

### Lab notes

With `p = 2`, `n = 192` (the hidden width of the recurrent cell in the motivating experiment)
and `m = 1`, the bound reads `1 - 2^{-k} - (2^k-1)·2^{-192}`: the genericity loss is utterly
negligible up to `k ≈ 100`, so in the regime of the data (`k ≤ 8`) the reliability term alone
governs, matching the observed monotone ramp `0.25 → 0.33 → 0.83 → 1.00 → 1.00`.
-/


open Module Finset

open EOSGenericity

variable {p m : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]






/-! ## Synthesis: reliability and genericity together -/



open EOSGenericity in
theorem solution{k : ℕ} (hk : k + 1 ≤ finrank (ZMod p) V) :
    probIndep p V (k + 1) ≤ probIndep p V k := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set n := finrank (ZMod p) V with hn
  have hk' : k ≤ n := by omega
  rw [probIndep_eq_prod hk, probIndep_eq_prod hk', Finset.prod_range_succ]
  have hnn : ∀ i ∈ range k, (0 : ℝ) ≤ 1 - (p : ℝ) ^ i / (p : ℝ) ^ n := by
    intro i hi
    have hle : (p : ℝ) ^ i ≤ (p : ℝ) ^ n :=
      pow_le_pow_right₀ (le_of_lt hpR) (le_trans (le_of_lt (mem_range.mp hi)) hk')
    have : (p : ℝ) ^ i / (p : ℝ) ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hle
    linarith
  have hprod : (0 : ℝ) ≤ ∏ i ∈ range k, (1 - (p : ℝ) ^ i / (p : ℝ) ^ n) :=
    Finset.prod_nonneg hnn
  have hfac : (0 : ℝ) ≤ (p : ℝ) ^ k / (p : ℝ) ^ n := by positivity
  nlinarith [hprod, hfac]
