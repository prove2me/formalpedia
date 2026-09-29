-- Prove2me | Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
-- name    : NumberTheory_EOSWidthMonotoneRamp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:44.044849+00:00
-- url     : https://prove2.me/theorems/c512b5fa-5d4c-4536-a83d-d440dd1ce3e3
-- title:
--   Aether Catalog definitions — NumberTheory_EOSWidthMonotoneRamp
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.EOSWidthMonotoneRamp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/EOSWidthMonotoneRamp.lean by skeleton subtraction
import Mathlib
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

namespace EOSWidthRamp

variable {p m : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

/-! ## Cardinalities over `𝔽_p` -/




/-! ## The model -/

/-- The number of `k`-tuples of vectors of `V` all of whose entries are swallowed by one of
the obstruction subspaces `W j`.  This is the number of *failing* exclusive subspaces of
width `k`. -/
noncomputable def failCount (W : Fin m → Submodule (ZMod p) V) (k : ℕ) : ℕ :=
  Nat.card {v : Fin k → V // ∃ j, ∀ i, v i ∈ W j}

/-- The failure probability at exclusive width `k`. -/
noncomputable def failProb (W : Fin m → Submodule (ZMod p) V) (k : ℕ) : ℝ :=
  (failCount W k : ℝ) / (Nat.card V : ℝ) ^ k

/-- The reliability ("cure") probability at exclusive width `k`. -/
noncomputable def cureProb (W : Fin m → Submodule (ZMod p) V) (k : ℕ) : ℝ :=
  1 - failProb W k

/-! ## Exact counting -/






/-! ## The reliability curve -/






/-! ## A matching lower bound: the ramp climbs at exactly the geometric rate `p^{-k}` -/




/-! ## The abstract notion of a monotone ramp -/

/-- A *monotone ramp*: a reliability curve that never decreases, never attains certainty,
and converges to certainty.  Such a curve has no critical width. -/
structure IsMonotoneRamp (P : ℕ → ℝ) : Prop where
  mono : Monotone P
  lt_one : ∀ k, P k < 1
  tendsto_one : Tendsto P atTop (𝓝 1)




/-! ## The exact hyperplane curve: sublinear benefit and total failure mass -/

section Hyperplane

variable (W : Submodule (ZMod p) V)









end Hyperplane

/-! ## A two-sided design rule for the required width -/



/-! ## No sharp critical width, and a concrete instance of the law -/


section Concrete






end Concrete

end EOSWidthRamp


