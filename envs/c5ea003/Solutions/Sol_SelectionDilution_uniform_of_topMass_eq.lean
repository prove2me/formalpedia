-- Prove2me | solution 1 for SelectionDilution.uniform_of_topMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:35:13.888375+00:00
-- url     : https://prove2.me/submissions/5ba609f8-6223-4e66-ba1d-03a83baff7c3

-- Sol generated from Logic/AttentionSelectionDilution.lean
import Mathlib
import Definitions.Def_Logic_AttentionSelectionDilution
import Theorems.Thm_SelectionDilution_sum_mass_powersetCard
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



/-- The binomial identity behind the baseline: `L · C(L-1, k-1) = C(L, k) · k`. -/
theorem nat_double_count (L k : ℕ) (hk : 1 ≤ k) (hkL : k ≤ L) :
    L * (L - 1).choose (k - 1) = L.choose k * k := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simpa using Nat.add_one_mul_choose_eq L' k'

/-- **The random-`k` baseline is exactly `k/L` of the total mass.**  Averaging the mass
over all `k`-subsets — the round's random-`k` control — returns `k/L · ∑ p`. -/
theorem randomK_baseline (p : ι → ℝ) {k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ Fintype.card ι) :
    (Fintype.card ι : ℝ) * ∑ S ∈ univ.powersetCard k (α := ι), ∑ i ∈ S, p i
      = (k : ℝ) * ((Fintype.card ι).choose k : ℝ) * ∑ i, p i := by
  have hL : 1 ≤ Fintype.card ι := le_trans hk hkL
  have hnat : Fintype.card ι * (Fintype.card ι - 1).choose (k - 1)
      = (Fintype.card ι).choose k * k := nat_double_count _ _ hk hkL
  rw [sum_mass_powersetCard p hk, ← mul_assoc]
  have : ((Fintype.card ι : ℝ)) * ((Fintype.card ι - 1).choose (k - 1) : ℝ)
      = ((Fintype.card ι).choose k : ℝ) * (k : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hnat
  rw [this]
  ring

/-! ## 3.  The selection gap is non-negative, and vanishes only for uniform attention -/



/-! ## 4.  Concentration: Cauchy–Schwarz and the impossibility of a bounded working set -/



/-! ## 5.  The dilution theorem: self-similar refinement cannot dilute selection -/





/-! ## 6.  The NET-45 numbers -/







open SelectionDilution in
theorem solution{p : ι → ℝ} {k : ℕ} {T : ℝ} (hk : 1 ≤ k)
    (hkL : k < Fintype.card ι) (hsum : ∑ i, p i = 1) (hT : IsTopMass p k T)
    (hgap : T = (k : ℝ) / (Fintype.card ι : ℝ)) :
    ∀ i j, p i = p j := by
  classical
  have hL : 1 ≤ Fintype.card ι := le_trans hk hkL.le
  have hLpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hL
  have hchoosepos : (0 : ℝ) < ((Fintype.card ι).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkL.le
  -- every `k`-subset has mass exactly `T`
  have hall : ∀ S ∈ univ.powersetCard k (α := ι), ∑ i ∈ S, p i = T := by
    have hsumeq : ∑ S ∈ univ.powersetCard k (α := ι), ∑ i ∈ S, p i
        = ∑ _S ∈ univ.powersetCard k (α := ι), T := by
      have hkey := randomK_baseline p hk hkL.le
      rw [hsum, mul_one] at hkey
      have hrhs : ∑ _S ∈ univ.powersetCard k (α := ι), T
          = ((Fintype.card ι).choose k : ℝ) * T := by
        rw [Finset.sum_const, card_powersetCard]; simp [nsmul_eq_mul]
      rw [hrhs, hgap]
      field_simp at hkey ⊢
      linarith [hkey]
    exact fun S hS => (Finset.sum_eq_sum_iff_of_le (fun S hS => hT.2 S hS)).1 hsumeq S hS
  intro i j
  by_cases hij : i = j
  · rw [hij]
  -- pick a `(k-1)`-subset `A` of the positions other than `i` and `j`
  have hcard : k - 1 ≤ ((univ.erase j).erase i).card := by
    have h1 : ((univ.erase j).erase i).card = Fintype.card ι - 1 - 1 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ i⟩), card_erase_of_mem (mem_univ j),
        card_univ]
    omega
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcard
  have hiA : i ∉ A := fun h => (mem_erase.1 (hAsub h)).1 rfl
  have hjA : j ∉ A := fun h => (mem_erase.1 (mem_of_mem_erase (hAsub h))).1 rfl
  have hSi : insert i A ∈ univ.powersetCard k (α := ι) := by
    rw [mem_powersetCard]
    exact ⟨fun x _ => mem_univ x, by rw [card_insert_of_notMem hiA, hAcard]; omega⟩
  have hSj : insert j A ∈ univ.powersetCard k (α := ι) := by
    rw [mem_powersetCard]
    exact ⟨fun x _ => mem_univ x, by rw [card_insert_of_notMem hjA, hAcard]; omega⟩
  have hi := hall _ hSi
  have hj := hall _ hSj
  rw [Finset.sum_insert hiA] at hi
  rw [Finset.sum_insert hjA] at hj
  linarith
