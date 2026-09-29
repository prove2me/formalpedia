-- Prove2me | Theorems.Thm_Doppelganger_no_contractive_metric_of_bijective_stimulus
-- name    : Doppelganger.no_contractive_metric_of_bijective_stimulus
-- status  : Disproved
-- author  : @raver1975
-- created : 2026-09-11T01:42:07.145856+00:00
-- url     : https://prove2.me/theorems/501b1e25-b5e5-4359-a02b-e48cbe76abb3
-- title:
--   No contractive metric in the presence of a reversible stimulus.
-- statement:
--   **No contractive metric in the presence of a reversible stimulus.**  If some stimulus
--   acts bijectively on a finite state space, then no metric can make every stimulus a uniform
--   `k`-contraction with `k < 1` unless the state space is a single point.
--
--   ```lean
--   theorem Doppelganger.no_contractive_metric_of_bijective_stimulus[Fintype S] [MetricSpace S]
--       (δ : S → I → S) (i₀ : I) (hbij : Function.Bijective (δ · i₀)) {k : ℝ}
--       (hk : 0 ≤ k) (hk1 : k < 1)
--       (hcontract : ∀ (i : I) (s t : S), dist (δ s i) (δ t i) ≤ k * dist s t) (s t : S) : s = t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Contraction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Contraction.lean#L154

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






variable [MetricSpace S] [Fintype S] [Nonempty S]





/-! ### Contractivity is strictly stronger than phase-lock

The contraction mechanism is *sufficient* for phase-lock but not necessary: an agent that
has a single reversible stimulus can never be contractive in any metric, because iterating
that stimulus around its (finite) orbit would force all distances to vanish.  Combined
with `Applications.DoppelgangerPhaseLock.Sharpness`, where a phase-locking agent with a
reversible stimulus is exhibited, this separates the analytic mechanism from the
combinatorial phenomenon. -/

theorem Doppelganger.no_contractive_metric_of_bijective_stimulus[Fintype S] [MetricSpace S]
    (δ : S → I → S) (i₀ : I) (hbij : Function.Bijective (δ · i₀)) {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (hcontract : ∀ (i : I) (s t : S), dist (δ s i) (δ t i) ≤ k * dist s t) (s t : S) : s = t := by sorry
