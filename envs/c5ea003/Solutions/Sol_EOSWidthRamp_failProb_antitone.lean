-- Prove2me | solution 1 for EOSWidthRamp.failProb_antitone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T23:57:28.643378+00:00
-- url     : https://prove2.me/submissions/29e93741-081a-456b-9c78-25713f3fe818

-- Sol generated from NumberTheory/EOSWidthMonotoneRamp.lean
import Mathlib
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
import Theorems.Thm_EOSWidthRamp_card_V_pos
import Theorems.Thm_EOSWidthRamp_failCount_succ_le
/-
# The exclusive-dimension reliability curve is a monotone ramp (no capacity cliff)

## Motivation (NET-27, `EOS-WIDTH-SHIFT-IS-A-MONOTONE-RAMP`)

An empirical study of a recurrent network with a boundary ("EOS") token whose learned
embedding occupies `k` *exclusive* parameter dimensions reported the reliability curve

| exclusive dims `k` | 0    | 1    | 2    | 4    | 8    |
|--------------------|------|------|------|------|------|
| `P(cure)`          | 0.25 | 0.33 | 0.83 | 1.00 | 1.00 |

with the qualitative reading: the curve is *monotone*, the benefit of extra dimensions is
*sublinear* (diminishing returns), and there is *no sharp critical width* — one exclusive
dimension is not sufficient, but no finite width makes success certain either.

## What is proved here

We give an exact finite-field model in which all four qualitative claims are theorems,
not observations.  Let `V` be a finite vector space over `𝔽_p` (`p` prime).  The boundary
token's exclusive subspace is modelled by a tuple `v : Fin k → V` of `k` independent
uniform draws, and the network's failure modes by a finite family `W : Fin m → Submodule 𝔽_p V`
of *proper* subspaces ("obstruction subspaces"): the run *fails* when the whole exclusive
subspace is swallowed by some obstruction, i.e. when `∃ j, ∀ i, v i ∈ W j`.

* `EOSWidthRamp.failCount_succ_le` — a fibration/prefix injection giving
  `failCount W (k+1) ≤ failCount W k * #V`, hence
* `EOSWidthRamp.failProb_antitone` / `EOSWidthRamp.cureProb_monotone` — **monotone ramp**;
* `EOSWidthRamp.failProb_pos` — failure probability is *strictly positive for every `k`*:
  **no finite width certifies a cure**, so there is no capacity cliff;
* `EOSWidthRamp.failProb_le` — union bound `P(fail) ≤ m · p^{-k}`: the curve does climb to 1;
* `EOSWidthRamp.cureProb_isMonotoneRamp` — the packaged law: `k ↦ P(cure)` is monotone,
  everywhere `< 1`, and tends to `1`;
* `EOSWidthRamp.hyperplane_cureProb` — in the single-hyperplane case the curve is *exactly*
  `1 - p^{-k}`, with `EOSWidthRamp.hyperplane_gain_strictAnti` (**sublinear benefit**:
  the marginal gain `(p-1)p^{-(k+1)}` strictly decreases) and
  `EOSWidthRamp.hyperplane_cureProb_one` (**the first exclusive dimension is not sufficient**);
* `EOSWidthRamp.cureProb_deficiency_two_sided` — the matching lower bound: the deficiency
  `1 - P(cure)` is pinned between `p^{-k}` and `m·p^{-k}`, so the ramp climbs at exactly the
  geometric rate;
* `EOSWidthRamp.width_sufficient` / `EOSWidthRamp.width_necessary` — a two-sided **design rule**:
  reliability `1 - ε` needs width `log_p(1/ε)` and is guaranteed by width `log_p(m/ε)`;
* `EOSWidthRamp.no_cliff` — the reliability curve is never a step function;
* `EOSWidthRamp.hyperplane_tsum_failProb` — the total failure mass `∑_k p^{-k} = p/(p-1)`,
  a number-theoretic invariant of the ramp;
* `EOSWidthRamp.concrete_isMonotoneRamp` and `EOSWidthRamp.ramp_two_values` — a concrete
  witness (`V = 𝔽_p`, obstruction `⊥`) showing the hypotheses are satisfiable, with the
  predicted `p = 2` values `0, 1/2, 3/4, 15/16, 255/256` at the experimental widths.

### Lab notes

The empirical failure masses `0.75, 0.67, 0.17, 0.00, 0.00` at `k = 0,1,2,4,8` are
compatible with the model's `min(1, m·p^{-k})` envelope for `p = 2`, `m ≈ 1` in the tail
(`p^{-2} = 0.25 ≥ 0.17`, `p^{-4} = 0.06`, `p^{-8} = 0.004`): the model predicts that the
observed "`0` failures at `k = 4, 8`" is a finite-sample effect, not an exact cliff — which
is precisely the theorem `failProb_pos`.
-/


open Module Filter Topology

open EOSWidthRamp

variable {p m : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

/-! ## Cardinalities over `𝔽_p` -/




/-! ## The model -/




/-! ## Exact counting -/






/-! ## The reliability curve -/






/-! ## A matching lower bound: the ramp climbs at exactly the geometric rate `p^{-k}` -/




/-! ## The abstract notion of a monotone ramp -/





/-! ## The exact hyperplane curve: sublinear benefit and total failure mass -/


variable (W : Submodule (ZMod p) V)










/-! ## A two-sided design rule for the required width -/



/-! ## No sharp critical width, and a concrete instance of the law -/










open EOSWidthRamp in
theorem solution(W : Fin m → Submodule (ZMod p) V) : Antitone (failProb W) := by
  have hN : (0 : ℝ) < (Nat.card V : ℝ) := by exact_mod_cast (card_V_pos (V := V))
  have step : ∀ k, failProb W (k + 1) ≤ failProb W k := by
    intro k
    have h := failCount_succ_le W k
    have h' : (failCount W (k + 1) : ℝ) ≤ (failCount W k : ℝ) * (Nat.card V : ℝ) := by
      exact_mod_cast h
    have hpk : (0 : ℝ) < (Nat.card V : ℝ) ^ k := pow_pos hN k
    rw [failProb, failProb, div_le_div_iff₀ (by positivity) hpk]
    calc (failCount W (k + 1) : ℝ) * (Nat.card V : ℝ) ^ k
        ≤ ((failCount W k : ℝ) * (Nat.card V : ℝ)) * (Nat.card V : ℝ) ^ k := by
          exact mul_le_mul_of_nonneg_right h' (le_of_lt hpk)
      _ = (failCount W k : ℝ) * (Nat.card V : ℝ) ^ (k + 1) := by ring
  exact antitone_nat_of_succ_le step
