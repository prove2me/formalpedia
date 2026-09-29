-- Prove2me | solution 1 for PRNGSeed.lfsrRun_isLinRec
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T05:59:51.795238+00:00
-- url     : https://prove2.me/submissions/bb82d0a7-7c94-446b-ba62-5cdd72d0eca6

/-
# `PRNGSeed.lfsrRun_isLinRec`
Target `62e08123` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

    IsLinRec L c x = ∀ n, x (n + L) = ∑ i : Fin L, c i * x (n + i)
    lfsrRun c init n = if h : n < L then init ⟨n,h⟩
                       else ∑ i : Fin L, c i * lfsrRun c init (n - L + i)

The run satisfies its own recurrence BY CONSTRUCTION. At index `n + L` the guard `n + L < L` is
false for every `n`, so the else-branch applies and gives `∑ i, c i * lfsrRun c init (n+L-L+i)`.
In ℕ, `n + L - L = n` with no truncation, since `n + L ≥ L` always. The two sides then coincide.

Verified exactly: zero discrepancy for L ∈ {1,2,3,5,8} across 40 indices each; the `n = 0` edge,
where the sum reads precisely the L initial values; and `L = 0`, where every value is the empty
sum `0` and the identity still holds.

**NOTHING HERE NEEDS DIVISION**, so `CommRing` suffices — which is exactly what the five rejected
submissions got wrong. The platform's rejection states the expected type verbatim:

    has type     ∀ {F} [Field F]    {L} (c init : Fin L → F), IsLinRec L c (lfsrRun c init)
    but expected ∀ {F} [CommRing F] {L} (c init : Fin L → F), IsLinRec L c (lfsrRun c init)

The bundle retains NO theorems, so nothing is cited from it; only the two definitions are used.
`lfsrRun` is defined by well-founded recursion, so if `rw [lfsrRun]` does not fire, the equation
lemma is `lfsrRun.eq_def`.
-/
import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR

set_option autoImplicit false
set_option maxHeartbeats 400000

open PRNGSeed in
/-- **The target, verbatim.** -/
theorem solution {F : Type*} [CommRing F] {L : ℕ} (c init : Fin L → F) :
    IsLinRec L c (lfsrRun c init) := by
  intro n
  have hnl : ¬ (n + L < L) := by omega
  have hsub : n + L - L = n := by omega
  rw [lfsrRun, dif_neg hnl, hsub]
