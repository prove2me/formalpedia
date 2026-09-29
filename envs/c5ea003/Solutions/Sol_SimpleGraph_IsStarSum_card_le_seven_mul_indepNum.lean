-- Prove2me | solution 1 for SimpleGraph.IsStarSum.card_le_seven_mul_indepNum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:17:27.388771+00:00
-- url     : https://prove2.me/submissions/6afbb7b6-08ea-405f-ab1a-9e81bbcfc4d2

-- Sol generated from Novelty/StarAmalgamSeventhBarrier.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam
import Definitions.Def_Novelty_StarAmalgamThresholdFamily
import Theorems.Thm_SimpleGraph_IsStarSum_sum_card_le_indepNum_add
import Theorems.Thm_SimpleGraph_IsStarSum_sum_card_le_indepNum_of_notMem

/-!
# The `1/7` barrier for star amalgams of threshold graphs

`Novelty.OneSumIndepRatioCounterexample` showed that the threshold property `i(G) ≥ 1/4` is
**not** closed under vertex amalgamation, and `Novelty.StarAmalgamThresholdFamily` produced an
`m`-parameter family of amalgams of `K₈ - e` whose independence ratio is `(m+1)/(7m+1)`, which
decreases to `1/7`.  This file closes the gap from the other side: **`1/7` is a genuine floor.**

Main results.

* `SimpleGraph.IsStarSum.card_le_seven_mul_indepNum` — if every side of a star amalgam carries
  an independent set of relative density at least `1/4` (and every side contains a vertex other
  than the cut vertex), then `n ≤ 7 α(G)`.
* `SimpleGraph.IsStarSum.indepRatio_ge_seventh` — the rational form `i(G) ≥ 1/7`.
* `SimpleGraph.StarFamily.seventh_barrier_optimal` — the constant `1/7` cannot be improved:
  the family `StarK8 m` satisfies the hypotheses for every `m ≥ 1`, and its ratio comes
  arbitrarily close to `1/7`.

The proof is a two-regime argument.  Write `Nᵢ` for the size of the `i`-th side, `sᵢ` for the
witnessing independent set (`Nᵢ ≤ 4|sᵢ|`), and `m` for the number of parts.

* *Large sides* (`Nᵢ ≥ 8` for all `i`): the plain defect bound `∑|sᵢ| ≤ α + (m-1)` already
  suffices, because `n = ∑Nᵢ - (m-1) ≥ 7m + 1` leaves enough room.
* *Some small side* (`N_j ≤ 7`): the defect bound is far too lossy there (it can even be
  vacuous), so one switches to the *cut-free* union bound `∑|tᵢ| ≤ α`, where `tᵢ` is `sᵢ`
  with the cut vertex deleted — replaced by an arbitrary non-cut vertex of the side when that
  deletion empties it.  The pointwise estimate `Nᵢ ≤ 7|tᵢ| + 1` holds for every `i` (it is
  `Nᵢ ≤ 4|sᵢ| ≤ 4|tᵢ| + 4 ≤ 7|tᵢ| + 1`, using `|tᵢ| ≥ 1`), and the small side gives the one
  extra unit `N_j ≤ 7|t_j|` that upgrades `7α ≥ n - 1` to `7α ≥ n`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): iterating 1-sums of graphs of independence ratio `1/4` cannot push
the ratio below `1/7`, and `1/7` is exactly the infimum.
Experiment (Experimenter): the naive route -- feed `r = 1/4` into
`SimpleGraph.IsStarSum.indepRatio_ge_of_sides` -- yields `1/4 - (m-1)(3/4)/n`, which is
*negative* for `m` large relative to `n`, so it does not prove any absolute floor.  Numerically,
minimising `∑ max(αᵢ-1,1) / (∑(Nᵢ-1)+1)` subject to `αᵢ ≥ Nᵢ/4` over side sizes
`Nᵢ ∈ {2,...,20}` gives per-side ratios `(Nᵢ-4)/(4(Nᵢ-1))` for `Nᵢ ≥ 8` and `1/(Nᵢ-1)` for
`Nᵢ ≤ 7`; the minimum over both regimes is attained at `Nᵢ = 8`, value `1/7`.  Sample values:
`N = 8 → 1/7 ≈ 0.1429`, `N = 12 → 8/44 ≈ 0.1818`, `N = 7 → 1/6 ≈ 0.1667`,
`N = 4 → 1/3`, `N = 2 → 1`.  Two regimes therefore have to be combined, which is exactly the
case split of the formal proof.
Analysis (Analyst): the failure of the single-bound approach is structural, not technical: the
defect bound `∑|sᵢ| ≤ α + (m-1)` charges `m-1` copies of the cut vertex, and for small sides
that charge exceeds the entire side.  Deleting the cut vertex up front (the `tᵢ` construction)
makes the charge disappear, at the cost of one vertex per side -- affordable precisely when a
side is small.
Critique (Critic): the hypothesis `2 ≤ Nᵢ` is load-bearing.  Without it a side may equal `{v}`,
so `tᵢ = ∅`, and the small-side upgrade `N_j ≤ 7|t_j|` fails.  It is also not merely technical:
the statement is about amalgams in which every part genuinely contributes.
Synthesis (PI): the pair (`indepRatio_ge_seventh`, `exists_indepRatio_lt`) pins the exact
constant `1/7` for the closure of the `1/4`-threshold under vertex amalgamation.
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

variable {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}

open IsStarSum

variable (h : IsStarSum G H A v)
include h

variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]





open StarFamily

variable {m : ℕ}





open SimpleGraph in
theorem solution[Nonempty ι] [∀ i, DecidablePred (· ∈ A i)]
    {s : ι → Finset V} (hs : ∀ i, ↑(s i) ⊆ A i) (hi : ∀ i, (H i).IsIndepSet ↑(s i))
    (hdens : ∀ i, (Finset.univ.filter (· ∈ A i)).card ≤ 4 * (s i).card)
    (hside : ∀ i, 2 ≤ (Finset.univ.filter (· ∈ A i)).card)
    (hcover : Fintype.card V + (Fintype.card ι - 1)
      = ∑ i, (Finset.univ.filter (· ∈ A i)).card) :
    Fintype.card V ≤ 7 * G.indepNum := by
  classical
  set N : ι → ℕ := fun i => (Finset.univ.filter (· ∈ A i)).card with hNdef
  have hcov : Fintype.card V + (Fintype.card ι - 1) = ∑ i, N i := hcover
  clear hcover
  have hm : 1 ≤ Fintype.card ι := Fintype.card_pos
  by_cases hall : ∀ i, 8 ≤ N i
  · -- Large sides: the plain defect bound already suffices.
    have hsum := h.sum_card_le_indepNum_add hs hi
    have h4 : ∑ i, N i ≤ 4 * ∑ i, (s i).card := by
      calc ∑ i, N i ≤ ∑ i, 4 * (s i).card := Finset.sum_le_sum fun i _ => hdens i
        _ = 4 * ∑ i, (s i).card := by rw [Finset.mul_sum]
    have h8 : 8 * Fintype.card ι ≤ ∑ i, N i := by
      calc 8 * Fintype.card ι = ∑ _i : ι, 8 := by
            simp [Finset.sum_const, Finset.card_univ, mul_comm]
        _ ≤ ∑ i, N i := Finset.sum_le_sum fun i _ => hall i
    omega
  · -- Some small side: switch to the cut-free bound.
    push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hex : ∀ i, ∃ x, x ∈ A i ∧ x ≠ v := by
      intro i
      obtain ⟨a, ha, b, hb, hab⟩ :=
        Finset.one_lt_card.1 (lt_of_lt_of_le one_lt_two (hside i))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      by_cases hav : a = v
      · exact ⟨b, hb, fun hbv => hab (hav.trans hbv.symm)⟩
      · exact ⟨a, ha, hav⟩
    choose x hxA hxne using hex
    set t : ι → Finset V :=
      fun i => if ((s i).erase v).Nonempty then (s i).erase v else {x i} with htdef
    have htv : ∀ i, v ∉ t i := by
      intro i
      by_cases hc : ((s i).erase v).Nonempty
      · simp only [htdef, if_pos hc]
        exact Finset.notMem_erase v (s i)
      · simp only [htdef, if_neg hc, Finset.mem_singleton]
        exact fun hcon => hxne i hcon.symm
    have htsub : ∀ i, ↑(t i) ⊆ A i := by
      intro i
      by_cases hc : ((s i).erase v).Nonempty
      · simp only [htdef, if_pos hc]
        intro y hy
        exact hs i (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hy)))
      · simp only [htdef, if_neg hc, Finset.coe_singleton]
        exact Set.singleton_subset_iff.2 (hxA i)
    have htindep : ∀ i, (H i).IsIndepSet ↑(t i) := by
      intro i
      by_cases hc : ((s i).erase v).Nonempty
      · simp only [htdef, if_pos hc]
        intro a ha b hb hne hadj
        exact hi i (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 ha)))
          (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hb))) hne hadj
      · simp only [htdef, if_neg hc, Finset.coe_singleton]
        intro a ha b hb hne _
        exact hne (ha.trans hb.symm)
    have htpos : ∀ i, 1 ≤ (t i).card := by
      intro i
      by_cases hc : ((s i).erase v).Nonempty
      · simp only [htdef, if_pos hc]
        exact Finset.card_pos.2 hc
      · simp [htdef, if_neg hc]
    have htge : ∀ i, (s i).card ≤ (t i).card + 1 := by
      intro i
      by_cases hc : ((s i).erase v).Nonempty
      · simp only [htdef, if_pos hc]
        have := Finset.pred_card_le_card_erase (s := s i) (a := v)
        omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hc
        have hsub : s i ⊆ {v} := by
          intro y hy
          by_cases hyv : y = v
          · simp [hyv]
          · exact absurd (hc ▸ Finset.mem_erase.2 ⟨hyv, hy⟩) (Finset.notMem_empty y)
        have : (s i).card ≤ 1 := by
          simpa using Finset.card_le_card hsub
        omega
    -- pointwise estimate `Nᵢ ≤ 7|tᵢ| + 1`
    have hkey : ∀ i, N i ≤ 7 * (t i).card + 1 := by
      intro i
      have h1 := hdens i
      have h2 := htge i
      have h3 := htpos i
      simp only [hNdef] at h1 ⊢
      omega
    have hjkey : N j ≤ 7 * (t j).card := by
      have := htpos j
      omega
    have hsumt : ∑ i, (t i).card ≤ G.indepNum :=
      h.sum_card_le_indepNum_of_notMem htsub htindep htv
    -- sum the pointwise estimates, gaining one unit at the small side `j`
    have hsplit_g : ∑ i, N i = N j + ∑ i ∈ Finset.univ.erase j, N i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hsplit_f : ∑ i, (7 * (t i).card + 1)
        = (7 * (t j).card + 1) + ∑ i ∈ Finset.univ.erase j, (7 * (t i).card + 1) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hrest : ∑ i ∈ Finset.univ.erase j, N i
        ≤ ∑ i ∈ Finset.univ.erase j, (7 * (t i).card + 1) :=
      Finset.sum_le_sum fun i _ => hkey i
    have hexp : ∑ i, (7 * (t i).card + 1) = 7 * (∑ i, (t i).card) + Fintype.card ι := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Finset.card_univ]
    omega
