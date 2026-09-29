-- Prove2me | Theorems.Thm_Doppelganger_dist_drive_le
-- name    : Doppelganger.dist_drive_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:39:02.704813+00:00
-- url     : https://prove2.me/theorems/ac04a3e0-04c7-407a-b5b0-f2ea7ad48fa4
-- title:
--   Exponential contraction of the doppelgänger gap.
-- statement:
--   **Exponential contraction of the doppelgänger gap.**  Under a uniform `k`-contraction
--   per stimulus, the distance between the two agents shrinks by a factor `k` per observation,
--   independently of *which* stimuli are observed.
--
--   ```lean
--   theorem Doppelganger.dist_drive_le(δ : S → I → S) {k : ℝ} (hk : 0 ≤ k)
--       (hcontract : ∀ (i : I) (s t : S), dist (δ s i) (δ t i) ≤ k * dist s t) (w : List I) (s t : S) :
--       dist (drive δ w s) (drive δ w t) ≤ k ^ w.length * dist s t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Contraction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Contraction.lean#L36

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

theorem Doppelganger.dist_drive_le(δ : S → I → S) {k : ℝ} (hk : 0 ≤ k)
    (hcontract : ∀ (i : I) (s t : S), dist (δ s i) (δ t i) ≤ k * dist s t) (w : List I) (s t : S) :
    dist (drive δ w s) (drive δ w t) ≤ k ^ w.length * dist s t := by sorry
