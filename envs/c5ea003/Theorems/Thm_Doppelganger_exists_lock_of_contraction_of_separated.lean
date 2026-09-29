-- Prove2me | Theorems.Thm_Doppelganger_exists_lock_of_contraction_of_separated
-- name    : Doppelganger.exists_lock_of_contraction_of_separated
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:39:40.311025+00:00
-- url     : https://prove2.me/theorems/694a9647-b2f8-484b-be8c-4d8254aada6e
-- title:
--   Quantization turns approximate telepathy into exact telepathy.
-- statement:
--   **Quantization turns approximate telepathy into exact telepathy.**  If distinct
--   internal states are separated by at least `ε > 0` and the state space has diameter at most
--   `D`, a contractive agent phase-locks *exactly* after `N` stimuli, for an `N` that depends
--   only on `k, ε, D` — never on the stimuli actually observed.
--
--   ```lean
--   theorem Doppelganger.exists_lock_of_contraction_of_separated[Nonempty S] (δ : S → I → S) {k ε D : ℝ}
--       (hk : 0 ≤ k) (hk1 : k < 1)
--       (hcontract : ∀ (i : I) (s t : S), dist (δ s i) (δ t i) ≤ k * dist s t)
--       (hε : 0 < ε) (hsep : ∀ s t : S, s ≠ t → ε ≤ dist s t)
--       (hD : ∀ s t : S, dist s t ≤ D) :
--       ∃ N : ℕ, ∀ w : List I, N ≤ w.length → Locks δ w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Contraction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Contraction.lean#L65

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Contraction.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
/-
# Doppelgänger Phase-Lock — the analytic (contractive) mechanism

The combinatorial theory of `Applications.DoppelgangerPhaseLock.Finite` answers *when*
identical agents can phase-lock.  This file supplies a *mechanism*: if each stimulus acts
on the internal state space as a `k`-Lipschitz map with `k < 1` — a "damped" or
"dissipative" agent — then the two separated copies converge towards each other
exponentially fast, at a rate that does not depend on the stimulus stream at all.

The last theorem is the bridge between analysis and combinatorics: in a state space that
is *quantized* (distinct states are at distance at least `ε`) and bounded, exponential
convergence forces **exact** phase-lock after finitely many stimuli, i.e. every
sufficiently long stimulus word is a locking word in the sense of the core file.  For a
finite metric state space, both hypotheses are automatic.

## Main results

* `Doppelganger.dist_drive_le` — `dist (drive δ w s) (drive δ w t) ≤ k ^ |w| * dist s t`.
* `Doppelganger.tendsto_dist_drive_zero` — asymptotic phase-lock along any stimulus stream.
* `Doppelganger.exists_lock_of_contraction_of_separated` — quantization upgrades
  asymptotic to exact phase-lock, uniformly in the stimulus stream.
* `Doppelganger.phaseLocking_of_contraction_finite` — every contractive agent with a
  finite metric state space is phase-locking.
* `Doppelganger.no_contractive_metric_of_bijective_stimulus` — the converse fails: an agent
  with a reversible stimulus admits no contractive metric at all.
-/

open Doppelganger

variable {S I : Type*}


variable [PseudoMetricSpace S]

theorem Doppelganger.exists_lock_of_contraction_of_separated[Nonempty S] (δ : S → I → S) {k ε D : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (hcontract : ∀ (i : I) (s t : S), dist (δ s i) (δ t i) ≤ k * dist s t)
    (hε : 0 < ε) (hsep : ∀ s t : S, s ≠ t → ε ≤ dist s t)
    (hD : ∀ s t : S, dist s t ≤ D) :
    ∃ N : ℕ, ∀ w : List I, N ≤ w.length → Locks δ w := by sorry
