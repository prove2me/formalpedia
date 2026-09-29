-- Prove2me | Theorems.Thm_NeuroSymbolicRLHF_oscil_sum_le
-- name    : NeuroSymbolicRLHF.oscil_sum_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:48:56.973649+00:00
-- url     : https://prove2.me/theorems/18d78310-e37d-4a3d-b048-29b4544713b3
-- title:
--   Subadditivity of `oscil` along a finite family, by induction on the family.
-- statement:
--   Subadditivity of `oscil` along a finite family, by induction on the family.
--
--   ```lean
--   theorem NeuroSymbolicRLHF.oscil_sum_le(r : ℕ → ι → ℝ) (n : ℕ) :
--       oscil (fun i => ∑ k ∈ Finset.range n, r k i) ≤ ∑ k ∈ Finset.range n, oscil (r k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/RLHFDriftBudget.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/RLHFDriftBudget.lean#L112

-- Thm stub generated from Speculative/AutoResearch/RLHFDriftBudget.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Definitions.Def_Speculative_AutoResearch_RLHFSymbolicConstraintLattice
/-
# Multi-round RLHF: metric axioms and a drift budget

Fourth file of the neurosymbolic RLHF thread.  The catalog already knows that
exponential tilting is a transitive group action of the reward space on the
open simplex, and `MachineLearning/RLHFHilbertIsometry.lean` shows that this
action is by *isometries* of the Hilbert projective metric with scale `1/β`.

Here we complete the metric picture and cash it out for *iterated* alignment
(RLHF round after RLHF round, as in real alignment pipelines):

* **Level 0 — seminorm axioms** for `oscil` (subadditivity, symmetry under
  negation) and the resulting **pseudometric axioms** for `hilbertDist`
  (symmetry and the triangle inequality on positive vectors).
* **Level 1 — one round is a translation**
  (`hilbertDist_gibbs_add_left`): applying an extra reward `s` moves the policy
  by exactly `oscil s / β`, independently of the reward accumulated so far.
* **Level 2 — the drift budget** (`hilbertDist_gibbs_sum_le`,
  `tvDist_gibbs_sum_le`): after `n` alignment rounds with rewards
  `r 0, …, r (n-1)` the total drift from the SFT model obeys
  `d_H(π_n, ref) ≤ (∑_k oscil (r k)) / β`, and hence
  `‖π_n - ref‖_TV ≤ exp((∑_k oscil (r k))/β) - 1`.
  The proof is by induction on the number of rounds, using the isometry to
  convert each round into a translation.
* **Level 3 — sharpness** (`hilbertDist_gibbs_sum_eq_of_aligned`): the budget
  is attained exactly when the successive rewards never cancel, i.e. when the
  oscillation is additive along the round sequence; a concrete two-round
  cancellation example (`drift_cancellation`) shows the inequality is strict in
  general, so no "drift accounting" scheme can do better than this bound
  without looking at the rewards jointly.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Level 0: seminorm and pseudometric axioms -/





/-! ## Level 1: one alignment round is a metric translation -/


/-! ## Level 2: the multi-round drift budget -/

theorem NeuroSymbolicRLHF.oscil_sum_le(r : ℕ → ι → ℝ) (n : ℕ) :
    oscil (fun i => ∑ k ∈ Finset.range n, r k i) ≤ ∑ k ∈ Finset.range n, oscil (r k) := by sorry
