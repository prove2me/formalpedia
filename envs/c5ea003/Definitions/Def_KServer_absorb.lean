-- Prove2me | Definitions.Def_KServer_absorb
-- name    : KServer_absorb
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T16:14:10.32548+00:00
-- url     : https://prove2.me/theorems/c8c6897f-82fc-4f9c-8504-3435689ca980
-- title:
--   The absorb skeleton: offline serving of chunked sequences along a reference path
-- statement:
--   Fix a metric space $M$ and a reference path $Q : \mathbb{N} \to M$. A chunked request sequence $\mathrm{cs}$ (a list of chunks, each a list of request sets) is *absorbable along $Q$ from step $a$ to step $b$*, written $\mathrm{Absorb}(Q, a, \mathrm{cs}, b)$, when it can be built up chunk by chunk so that each chunk either **advances** along $Q$ — its $i$-th request set contains $Q(a+i+1)$, and the remaining chunks are absorbable from $a + \mathrm{len}$ — or is **stationary** — every one of its request sets already contains the current position $Q(a)$, and the remaining chunks are absorbable from the same $a$. The main theorem converts a derivation into an offline evader bound:
--   $$\mathrm{Absorb}(Q, a, \mathrm{cs}, b) \implies \mathrm{OPT}\bigl(Q(a),\ \mathrm{flatten}(\mathrm{cs})\bigr) \;\le\; \sum_{i=a}^{b-1} d\bigl(Q(i), Q(i+1)\bigr),$$
--   where $\mathrm{OPT}(x_0, \sigma)$ is the optimal offline cost of serving the request sequence $\sigma$ from $x_0$ in the metrical-service-system (evader) model. The witnessing path follows $Q$ on advancing chunks and stands still on stationary ones, so the stationary chunks are served for free. This is the combinatorial core of the follow-the-survivor offline strategy for the coin race in the BCR randomized lower bound: the survivor's chunks advance along a lifted copy of the survivor's own offline path, while the dead side's park-augmented chunks (each request contains the survivor's parked position) and the terminal padding are stationary. Auxiliary results: a positional restatement of the serving predicate, a canonical serving path showing the offline cost set is nonempty and bounded below, and extraction of near-optimal offline paths from the infimum.
-- source:
--   Follow-the-survivor offline bookkeeping for the race construction in the BCR randomized k-server lower bound, adapted

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_shadow

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace Race

variable {M : Type*} [MetricSpace M]

/-! ### The absorb skeleton

Serving a chunked request sequence by following a reference path `Q`:
each chunk either **advances** along `Q` (its `i`-th request contains the
next `Q`-step) or is **stationary** (each of its requests already
contains the current `Q`-position).  A derivation `Absorb Q a cs b`
witnesses that the chunk list `cs` can be served starting at `Q a`,
consuming the `Q`-steps in `[a, b)`; the offline cost of the flattened
sequence is then at most the `Q`-movement on `[a, b)`.  This is the
follow-the-survivor argument of the race: the survivor's chunks advance
along the lifted survivor path, while the dead side's park-augmented
chunks and the padding are stationary. -/

/-- Positional restatement of `EvaderServes`. -/
theorem evaderServes_iff {x₀ : M} {σ : List (Set M)} {P : ℕ → M} :
    EvaderServes x₀ σ P ↔ P 0 = x₀ ∧
      ∀ n : ℕ, ∀ hn : n < σ.length, (σ[n]).Nonempty → P (n + 1) ∈ σ[n] := by
  constructor
  · intro h
    refine ⟨h.1, fun n hn hne => ?_⟩
    have := h.2 ⟨n, hn⟩ (by simpa [List.get_eq_getElem] using hne)
    simpa [List.get_eq_getElem] using this
  · intro h
    refine ⟨h.1, fun j hne => ?_⟩
    have := h.2 (j : ℕ) j.isLt (by simpa [List.get_eq_getElem] using hne)
    simpa [List.get_eq_getElem] using this

/-- Serving skeleton along a reference path. -/
inductive Absorb (Q : ℕ → M) : ℕ → List (List (Set M)) → ℕ → Prop
  | nil (a : ℕ) : Absorb Q a [] a
  | adv {a b : ℕ} {ch : List (Set M)} {cs : List (List (Set M))}
      (h : ∀ n : ℕ, ∀ hn : n < ch.length,
        (ch[n]).Nonempty → Q (a + n + 1) ∈ ch[n])
      (hnext : Absorb Q (a + ch.length) cs b) : Absorb Q a (ch :: cs) b
  | stat {a b : ℕ} {ch : List (Set M)} {cs : List (List (Set M))}
      (h : ∀ S ∈ ch, S.Nonempty → Q a ∈ S)
      (hnext : Absorb Q a cs b) : Absorb Q a (ch :: cs) b

theorem Absorb.start_le {Q : ℕ → M} {a : ℕ} {cs : List (List (Set M))}
    {b : ℕ} (h : Absorb Q a cs b) : a ≤ b := by
  induction h with
  | nil => exact le_refl _
  | adv h hnext ih => omega
  | stat h hnext ih => exact ih

/-- A derivation yields a serving path whose cost is the `Q`-movement. -/
theorem Absorb.exists_serves {Q : ℕ → M} {a : ℕ}
    {cs : List (List (Set M))} {b : ℕ} (h : Absorb Q a cs b) :
    ∃ P : ℕ → M, EvaderServes (Q a) cs.flatten P ∧
      ∑ j ∈ Finset.range cs.flatten.length, dist (P j) (P (j + 1))
        ≤ ∑ i ∈ Finset.Ico a b, dist (Q i) (Q (i + 1)) := by
  induction h with
  | nil a =>
    refine ⟨fun _ => Q a, evaderServes_iff.mpr ⟨rfl, ?_⟩, ?_⟩
    · intro n hn
      simp at hn
    · simp
  | @adv a b ch cs h hnext ih =>
    obtain ⟨Pr, hPr, hPrc⟩ := ih
    rw [evaderServes_iff] at hPr
    refine ⟨fun n => if n < ch.length then Q (a + n) else Pr (n - ch.length),
      ?_, ?_⟩
    all_goals
      set P : ℕ → M := fun n => if n < ch.length then Q (a + n)
        else Pr (n - ch.length) with hPdef
    all_goals
      have hPge : ∀ n, ch.length ≤ n → P n = Pr (n - ch.length) := by
        intro n hn
        show (if n < ch.length then Q (a + n) else Pr (n - ch.length)) = _
        rw [if_neg (by omega)]
    all_goals
      have hPshift : ∀ n, P (ch.length + n) = Pr n := by
        intro n
        rw [hPge _ (by omega), Nat.add_sub_cancel_left]
    all_goals
      have hPQ : ∀ n, n ≤ ch.length → P n = Q (a + n) := by
        intro n hn
        rcases Nat.lt_or_ge n ch.length with h1 | h1
        · show (if n < ch.length then Q (a + n) else Pr (n - ch.length)) = _
          rw [if_pos h1]
        · have he : n = ch.length := by omega
          subst he
          have h2 := hPshift 0
          rw [Nat.add_zero] at h2
          rw [h2, hPr.1]
    · -- serving
      refine evaderServes_iff.mpr ⟨?_, ?_⟩
      · rw [hPQ 0 (by omega), Nat.add_zero]
      · show ∀ n : ℕ, ∀ hn : n < (ch ++ cs.flatten).length,
          ((ch ++ cs.flatten)[n]).Nonempty → P (n + 1) ∈ (ch ++ cs.flatten)[n]
        intro n hn hne
        rw [List.length_append] at hn
        by_cases hnc : n < ch.length
        · rw [List.getElem_append_left hnc] at hne ⊢
          rw [hPQ (n + 1) (by omega)]
          exact h n hnc hne
        · rw [not_lt] at hnc
          rw [List.getElem_append_right hnc] at hne ⊢
          rw [hPge (n + 1) (by omega),
            show n + 1 - ch.length = (n - ch.length) + 1 from by omega]
          exact hPr.2 (n - ch.length) (by omega) hne
    · -- cost
      show ∑ j ∈ Finset.range (ch ++ cs.flatten).length,
          dist (P j) (P (j + 1)) ≤ _
      rw [List.length_append]
      have hsplit : ∑ j ∈ Finset.range (ch.length + cs.flatten.length),
          dist (P j) (P (j + 1))
          = (∑ j ∈ Finset.range ch.length, dist (P j) (P (j + 1)))
            + ∑ j ∈ Finset.range cs.flatten.length,
              dist (P (ch.length + j)) (P (ch.length + j + 1)) := by
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _
            (by omega : 0 ≤ ch.length)
            (by omega : ch.length ≤ ch.length + cs.flatten.length)]
        congr 1
        · rw [← Finset.range_eq_Ico]
        · rw [Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel_left]
      rw [hsplit]
      have h1 : ∑ j ∈ Finset.range ch.length, dist (P j) (P (j + 1))
          = ∑ i ∈ Finset.Ico a (a + ch.length), dist (Q i) (Q (i + 1)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [hPQ j (by omega), hPQ (j + 1) (by omega), Nat.add_assoc]
      have h2 : ∑ j ∈ Finset.range cs.flatten.length,
          dist (P (ch.length + j)) (P (ch.length + j + 1))
          = ∑ j ∈ Finset.range cs.flatten.length,
            dist (Pr j) (Pr (j + 1)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [show ch.length + j + 1 = ch.length + (j + 1) from rfl,
          hPshift, hPshift]
      rw [h1, h2,
        ← Finset.sum_Ico_consecutive (fun i => dist (Q i) (Q (i + 1)))
          (by omega : a ≤ a + ch.length) hnext.start_le]
      exact add_le_add le_rfl hPrc
  | @stat a b ch cs h hnext ih =>
    obtain ⟨Pr, hPr, hPrc⟩ := ih
    rw [evaderServes_iff] at hPr
    refine ⟨fun n => if n < ch.length then Q a else Pr (n - ch.length),
      ?_, ?_⟩
    all_goals
      set P : ℕ → M := fun n => if n < ch.length then Q a
        else Pr (n - ch.length) with hPdef
    all_goals
      have hPge : ∀ n, ch.length ≤ n → P n = Pr (n - ch.length) := by
        intro n hn
        show (if n < ch.length then Q a else Pr (n - ch.length)) = _
        rw [if_neg (by omega)]
    all_goals
      have hPconst : ∀ n, n ≤ ch.length → P n = Q a := by
        intro n hn
        rcases Nat.lt_or_ge n ch.length with h1 | h1
        · show (if n < ch.length then Q a else Pr (n - ch.length)) = _
          rw [if_pos h1]
        · have he : n = ch.length := by omega
          subst he
          rw [hPge _ (by omega), Nat.sub_self, hPr.1]
    · -- serving
      refine evaderServes_iff.mpr ⟨hPconst 0 (by omega), ?_⟩
      show ∀ n : ℕ, ∀ hn : n < (ch ++ cs.flatten).length,
        ((ch ++ cs.flatten)[n]).Nonempty → P (n + 1) ∈ (ch ++ cs.flatten)[n]
      intro n hn hne
      rw [List.length_append] at hn
      by_cases hnc : n < ch.length
      · rw [List.getElem_append_left hnc] at hne ⊢
        rw [hPconst (n + 1) (by omega)]
        exact h _ (List.getElem_mem hnc) hne
      · rw [not_lt] at hnc
        rw [List.getElem_append_right hnc] at hne ⊢
        rw [hPge (n + 1) (by omega),
          show n + 1 - ch.length = (n - ch.length) + 1 from by omega]
        exact hPr.2 (n - ch.length) (by omega) hne
    · -- cost
      show ∑ j ∈ Finset.range (ch ++ cs.flatten).length,
          dist (P j) (P (j + 1)) ≤ _
      rw [List.length_append]
      have hsplit : ∑ j ∈ Finset.range (ch.length + cs.flatten.length),
          dist (P j) (P (j + 1))
          = (∑ j ∈ Finset.range ch.length, dist (P j) (P (j + 1)))
            + ∑ j ∈ Finset.range cs.flatten.length,
              dist (P (ch.length + j)) (P (ch.length + j + 1)) := by
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _
            (by omega : 0 ≤ ch.length)
            (by omega : ch.length ≤ ch.length + cs.flatten.length)]
        congr 1
        · rw [← Finset.range_eq_Ico]
        · rw [Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel_left]
      rw [hsplit]
      have h1 : ∑ j ∈ Finset.range ch.length, dist (P j) (P (j + 1)) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [hPconst j (by omega), hPconst (j + 1) (by omega), dist_self]
      have h2 : ∑ j ∈ Finset.range cs.flatten.length,
          dist (P (ch.length + j)) (P (ch.length + j + 1))
          = ∑ j ∈ Finset.range cs.flatten.length,
            dist (Pr j) (Pr (j + 1)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have ha : P (ch.length + j) = Pr j := by
          rw [hPge _ (by omega), Nat.add_sub_cancel_left]
        have hb : P (ch.length + j + 1) = Pr (j + 1) := by
          rw [show ch.length + j + 1 = ch.length + (j + 1) from rfl,
            hPge _ (by omega), Nat.add_sub_cancel_left]
        rw [ha, hb]
      rw [h1, h2, zero_add]
      exact hPrc

open Classical in
/-- A canonical offline serving path: step into each nonempty request. -/
noncomputable def defaultPath (x₀ : M) (σ : List (Set M)) : ℕ → M
  | 0 => x₀
  | (j + 1) => if h : (σ.getD j ∅).Nonempty then h.choose
      else defaultPath x₀ σ j

theorem defaultPath_serves (x₀ : M) (σ : List (Set M)) :
    EvaderServes x₀ σ (defaultPath x₀ σ) := by
  refine ⟨rfl, ?_⟩
  intro j hne
  have hget : σ.get j = σ.getD (j : ℕ) ∅ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
    rfl
  show defaultPath x₀ σ ((j : ℕ) + 1) ∈ σ.get j
  rw [hget] at hne ⊢
  unfold defaultPath
  rw [dif_pos hne]
  exact hne.choose_spec

/-- The offline cost set is nonempty. -/
theorem offlineSet_nonempty (x₀ : M) (σ : List (Set M)) :
    {ch : ℝ | ∃ P : ℕ → M, EvaderServes x₀ σ P ∧
      ch = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))}.Nonempty :=
  ⟨_, defaultPath x₀ σ, defaultPath_serves x₀ σ, rfl⟩

theorem offlineSet_bddBelow (x₀ : M) (σ : List (Set M)) :
    BddBelow {ch : ℝ | ∃ P : ℕ → M, EvaderServes x₀ σ P ∧
      ch = ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1))} := by
  refine ⟨0, fun ch hc => ?_⟩
  obtain ⟨P, -, hc⟩ := hc
  rw [hc]
  exact Finset.sum_nonneg fun j _ => dist_nonneg

/-- The offline cost of an absorbable chunk sequence is at most the
reference movement. -/
theorem Absorb.offline_le {Q : ℕ → M} {a : ℕ}
    {cs : List (List (Set M))} {b : ℕ} (h : Absorb Q a cs b) :
    evaderOfflineCost (Q a) cs.flatten
      ≤ ∑ i ∈ Finset.Ico a b, dist (Q i) (Q (i + 1)) := by
  obtain ⟨P, hP, hcost⟩ := h.exists_serves
  exact le_trans (csInf_le (offlineSet_bddBelow _ _) ⟨P, hP, rfl⟩) hcost

/-- Extract a near-optimal offline path. -/
theorem offline_exists_lt (x₀ : M) (σ : List (Set M)) {ch : ℝ}
    (h : evaderOfflineCost x₀ σ < ch) :
    ∃ P : ℕ → M, EvaderServes x₀ σ P ∧
      ∑ j ∈ Finset.range σ.length, dist (P j) (P (j + 1)) < ch := by
  obtain ⟨d, ⟨P, hP, hd⟩, hdc⟩ :=
    exists_lt_of_csInf_lt (offlineSet_nonempty x₀ σ) h
  exact ⟨P, hP, by rw [← hd]; exact hdc⟩

end Race

end KServer


