-- Prove2me | Definitions.Def_NumberTheory_EOSExclusiveDimGenericity
-- name    : NumberTheory_EOSExclusiveDimGenericity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:26.763978+00:00
-- url     : https://prove2.me/theorems/7c922e9d-7b91-41d0-b17c-00b940c4d158
-- title:
--   Aether Catalog definitions — NumberTheory_EOSExclusiveDimGenericity
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.EOSExclusiveDimGenericity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/EOSExclusiveDimGenericity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
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

namespace EOSGenericity

variable {p m : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

/-- Probability that `k` uniform draws from `V` are linearly independent. -/
noncomputable def probIndep (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (k : ℕ) : ℝ :=
  (Nat.card {s : Fin k → V // LinearIndependent (ZMod p) s} : ℝ) / (Nat.card V : ℝ) ^ k





/-! ## Synthesis: reliability and genericity together -/


end EOSGenericity


