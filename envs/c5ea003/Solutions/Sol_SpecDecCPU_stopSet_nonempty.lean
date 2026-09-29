-- Prove2me | solution 1 for SpecDecCPU.stopSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:07:10.354193+00:00
-- url     : https://prove2.me/submissions/b773631c-34bb-43cb-9028-05a781180467

-- Sol generated from Shared/SpeculativeDecodingStopDepth.lean
import Mathlib
import Definitions.Def_Shared_SpeculativeDecodingCostDominance
import Definitions.Def_Shared_SpeculativeDecodingStopDepth
import Theorems.Thm_SpecDecCPU_exists_depth_collapse
import Theorems.Thm_SpecDecCPU_speedup_zero

/-!
# The stopping depth as a canonical selector, and its monotonicity in acceptance

Cycle 5, the capstone of the NET-91 thread.  Cycles 1–4 produced three ingredients:

* throughput collapses at large depth (`exists_depth_collapse`);
* throughput is unimodal in depth, so greedy tuning is exact (`geom_greedy_depth_optimal`);
* the "deepening pays" frontier is monotone in acceptance (`depth_frontier_monotone`,
  `greedy_stop_antitone`).

Here they are combined into a single object: the **stopping depth**

`stopDepth a c = sInf {D | speedup a c (D+1) < speedup a c D}`,

the first depth at which one more drafted token stops paying.  It is well defined
(`stopSet_nonempty`), it is a *global* optimum, not merely a local one
(`stopDepth_optimal`), and it is monotone in the acceptance rate
(`stopDepth_mono_acceptance`).  That last statement is the sharpest formal version of the
NET-91 depth law: *a domain that accepts more should draft deeper, always*.

Instantiated at the measured 0.5B-draft cost, the selector returns
`stopDepth 0.477 0.118 = 2` for prose and `stopDepth 0.630 0.118 = 3` for code
(`prose_stopDepth_eq_two`, `code_stopDepth_eq_three`), a strict split
(`stopDepth_domain_split`).

-- !-- Lab Notes -- !--
Hypothesizer (cycle 5):
 (F1) [BOLD] There is a canonical depth selector, definable from the throughput curve
      alone, that is simultaneously globally optimal and monotone in acceptance.
 (F2) The selector is computable by one local test per depth — no grid search, no
      backtracking — which is what makes it deployable.
 (F3) The measured prose/code acceptances give different selector values, so the NET-91
      prescription is recovered as an equation rather than a fitted table.

Experimenter: F1–F3 formalised below, zero sorries.

Analyst: the only delicate point is well-definedness.  Unimodality alone does not give a
stopping depth — a curve that increases forever has none — so nonemptiness of the stopping
set is where the depth-collapse theorem of cycle 1 is genuinely needed; it is the formal
trace of the fact that sequential drafting on a CPU is never asymptotically free.

Critic: monotonicity is stated for `0 < a ≤ a' < 1` — at `a = 0` the profile is degenerate
(the drafter is useless and the selector returns `0`), and at `a = 1` the drafter is
perfect and the stopping set is empty, so both endpoints are genuinely excluded rather than
hidden.
-/

open SpecDecCPU

open Filter













open SpecDecCPU in
theorem solution{a c : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hc : 0 < c) :
    (stopSet a c).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hmono : ∀ D : ℕ, speedup a c D ≤ speedup a c (D + 1) := by
    intro D
    have : D ∉ stopSet a c := by rw [hempty]; exact Set.notMem_empty D
    simpa [stopSet, not_lt] using this
  have hall : ∀ d : ℕ, (1 : ℝ) ≤ speedup a c d := by
    intro d
    induction d with
    | zero => rw [speedup_zero]
    | succ n ih => exact le_trans ih (hmono n)
  obtain ⟨D, hD⟩ := exists_depth_collapse ha ha1 hc
  exact absurd (hall D) (not_le.2 (hD D le_rfl))
