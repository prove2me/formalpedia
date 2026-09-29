-- Prove2me | Theorems.Thm_SelectionDilution_no_bounded_working_set
-- name    : SelectionDilution.no_bounded_working_set
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:43:54.603983+00:00
-- url     : https://prove2.me/theorems/81c2f640-ffea-40d1-9f3d-a8417b214e8a
-- title:
--   No bounded working set.
-- statement:
--   **No bounded working set.**  If the effective supports `N n` of a family of attention
--   profiles are unbounded, then for every fixed budget `k` and every target fraction
--   `m > 0` there is a context in the family at which the top-`k` mass is below `m`.  A
--   context-independent budget therefore cannot retain a constant fraction of the attention
--   mass — the knee must grow with the context.
--
--   ```lean
--   theorem SelectionDilution.no_bounded_working_set{ι' : ℕ → Type} [∀ n, Fintype (ι' n)] [∀ n, DecidableEq (ι' n)]
--       (k : ℕ) (p : ∀ n, ι' n → ℝ) (N : ℕ → ℝ) (T : ℕ → ℝ)
--       (hN : ∀ n, 0 < N n) (hsupp : ∀ n, ∑ i, p n i ^ 2 ≤ 1 / N n)
--       (hT : ∀ n, IsTopMass (p n) k (T n)) (hunbdd : ∀ C : ℝ, ∃ n, C < N n) (m : ℝ) (hm : 0 < m) :
--       ∃ n, T n < m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AttentionSelectionDilution.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AttentionSelectionDilution.lean#L267

-- Thm stub generated from Logic/AttentionSelectionDilution.lean
import Mathlib
import Definitions.Def_Logic_AttentionSelectionDilution
/-
# Selection gaps, concentration, and the dilution of top-`k` pruning at long context
# (NET-45, cycle 1)

Round NET-45 measures, at `(d = 4, ctx = 2048, seed 1)`, three quantities that the
knee files of this catalog (`Logic.KneeFluctuationTwoSeed`, `Logic.KneeDriftLadder`,
`Logic.KneeSeedEnsembleBracket`) do **not** touch, because they are not statements about
a threshold on a sweep grid but about the *attention profile itself*:

* the **selection gap** — how much better data-free top-`k` pruning is than keeping a
  uniformly random set of `k` positions (`+5.9 / +4.6` accuracy points at `ctx = 256`,
  `+5.3 / +4.6` at `512`, `+5.9 / +4.6` at `1024`, and only `+1.7 / +1.8` at
  `ctx = 2048`: the selection advantage **dilutes** with context);
* the **effective support** `N_eff` (`291.16` at `ctx = 1024`, `526.39` at `ctx = 2048`,
  a factor `1.81` per doubling — superlinear in the sense that it does not saturate);
* the **absence of a bounded working set**: top-`128` mass `0.589` and top-`256` mass
  `0.731` at `16×` context, both far from `1`.

This file develops the order-theoretic and convex-geometric content of those three
observations for an arbitrary attention profile `p : ι → ℝ` on a finite position set.

**Results.**

* `SelectionDilution.exists_isTopMass`, `IsTopMass.unique` : the top-`k` mass is a
  well-defined functional of the profile whenever `k ≤ |ι|`.
* `SelectionDilution.sum_mass_powersetCard` : the double-counting identity
  `∑_{|S| = k} ∑_{i ∈ S} p i = C(L-1, k-1) · ∑ p`, i.e. **the random-`k` baseline is
  exactly `k/L` of the total mass** — the null model the round compares against, proved
  rather than assumed (`randomK_baseline`).
* `SelectionDilution.uniform_le_topMass` : the selection gap is **always non-negative**.
  The round's observation that all measured gaps are positive is therefore not evidence
  for anything; only the *size* of the gap is informative.
* `SelectionDilution.uniform_of_topMass_eq` : **rigidity.**  A vanishing selection gap
  forces the profile to be *exactly uniform* (for `0 < k < L`).  So the dilution observed
  at `16×` context is a quantitative approach to uniformity, and a gap of exactly zero
  would be the strongest possible negative result about attention pruning.
* `SelectionDilution.topMass_sq_le_card_mul_sumSq` : the Cauchy–Schwarz concentration
  bound `T_k² ≤ k · ‖p‖₂² = k / N_eff`, tying the round's `N_eff` to its top-`k` masses.
* `SelectionDilution.no_bounded_working_set` : if the effective support of a family of
  profiles is unbounded, then **no fixed budget retains a fixed fraction of the mass** —
  a bounded working set is impossible, exactly the round's conclusion, and the reason a
  knee law must grow with context.
* `SelectionDilution.topMass_split_ge`,
  `selection_gap_mono_under_self_similar_refinement`,
  `dilution_refutes_self_similarity` : the **dilution theorem**.  Under exact
  self-similar refinement of the context (each position split into two half-weight
  positions, the scale-invariant null model of a Zipf-type profile), the selection gap at
  the matched ratio `k/L` can only *increase*.  Hence the measured strict decrease
  `+5.9 → +1.7` refutes exact self-similarity of the attention profile across the
  doubling — a falsifiable structural conclusion drawn from the round's weakest number.
-/


open SelectionDilution

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1.  The top-`k` mass functional -/




/-! ## 2.  The random-`k` baseline, by double counting -/





/-! ## 3.  The selection gap is non-negative, and vanishes only for uniform attention -/



/-! ## 4.  Concentration: Cauchy–Schwarz and the impossibility of a bounded working set -/

theorem SelectionDilution.no_bounded_working_set{ι' : ℕ → Type} [∀ n, Fintype (ι' n)] [∀ n, DecidableEq (ι' n)]
    (k : ℕ) (p : ∀ n, ι' n → ℝ) (N : ℕ → ℝ) (T : ℕ → ℝ)
    (hN : ∀ n, 0 < N n) (hsupp : ∀ n, ∑ i, p n i ^ 2 ≤ 1 / N n)
    (hT : ∀ n, IsTopMass (p n) k (T n)) (hunbdd : ∀ C : ℝ, ∃ n, C < N n) (m : ℝ) (hm : 0 < m) :
    ∃ n, T n < m := by sorry
