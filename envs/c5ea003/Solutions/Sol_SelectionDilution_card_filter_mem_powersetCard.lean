-- Prove2me | solution 1 for SelectionDilution.card_filter_mem_powersetCard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:25:55.246118+00:00
-- url     : https://prove2.me/submissions/87f8f935-eba6-45d2-a6a5-ef88356b0bf6

-- Sol generated from Logic/AttentionSelectionDilution.lean
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



/-! ## 5.  The dilution theorem: self-similar refinement cannot dilute selection -/





/-! ## 6.  The NET-45 numbers -/







open SelectionDilution in
theorem solution(i : ι) {k : ℕ} (hk : 1 ≤ k) :
    ((univ.powersetCard k (α := ι)).filter (fun S => i ∈ S)).card
      = (Fintype.card ι - 1).choose (k - 1) := by
  classical
  have hbij :
      ((univ.powersetCard k (α := ι)).filter (fun S => i ∈ S)).card
        = ((univ.erase i).powersetCard (k - 1)).card := by
    refine Finset.card_bij' (fun S _ => S.erase i) (fun T _ => insert i T) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powersetCard] at hS ⊢
      obtain ⟨⟨-, hcard⟩, hmem⟩ := hS
      refine ⟨fun x hx => ?_, ?_⟩
      · exact mem_erase.2 ⟨(mem_erase.1 hx).1, mem_univ _⟩
      · rw [card_erase_of_mem hmem, hcard]
    · intro T hT
      simp only [mem_powersetCard] at hT
      obtain ⟨hsub, hcard⟩ := hT
      have hiT : i ∉ T := fun h => (mem_erase.1 (hsub h)).1 rfl
      simp only [mem_filter, mem_powersetCard]
      refine ⟨⟨fun x _ => mem_univ x, ?_⟩, mem_insert_self _ _⟩
      rw [card_insert_of_notMem hiT, hcard]
      omega
    · intro S hS
      simp only [mem_filter] at hS
      exact insert_erase hS.2
    · intro T hT
      simp only [mem_powersetCard] at hT
      have hiT : i ∉ T := fun h => (mem_erase.1 (hT.1 h)).1 rfl
      exact erase_insert hiT
  rw [hbij, card_powersetCard, card_erase_of_mem (mem_univ i)]
  simp
