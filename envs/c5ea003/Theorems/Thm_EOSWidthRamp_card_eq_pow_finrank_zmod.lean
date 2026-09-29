-- Prove2me | Theorems.Thm_EOSWidthRamp_card_eq_pow_finrank_zmod
-- name    : EOSWidthRamp.card_eq_pow_finrank_zmod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:27:25.487827+00:00
-- url     : https://prove2.me/theorems/010d5f79-9ac8-4b12-b806-a64896306b6e
-- title:
--   A finite `𝔽_p`-vector space has `p ^ dim` elements.
-- statement:
--   A finite `𝔽_p`-vector space has `p ^ dim` elements.
--
--   ```lean
--   theorem EOSWidthRamp.card_eq_pow_finrank_zmod(W : Type*) [AddCommGroup W] [Module (ZMod p) W] [Finite W] :
--       Nat.card W = p ^ finrank (ZMod p) W := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/EOSWidthMonotoneRamp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/EOSWidthMonotoneRamp.lean#L68

-- Thm stub generated from NumberTheory/EOSWidthMonotoneRamp.lean
import Mathlib
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
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

theorem EOSWidthRamp.card_eq_pow_finrank_zmod(W : Type*) [AddCommGroup W] [Module (ZMod p) W] [Finite W] :
    Nat.card W = p ^ finrank (ZMod p) W := by sorry
