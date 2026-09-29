-- Prove2me | Definitions.Def_Probability_U9DriftDegenerateBootstrap
-- name    : Probability_U9DriftDegenerateBootstrap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:06.937424+00:00
-- url     : https://prove2.me/theorems/83141537-809d-4761-897e-ba645b2e1e6b
-- title:
--   Aether Catalog definitions — Probability_U9DriftDegenerateBootstrap
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.U9DriftDegenerateBootstrap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/U9DriftDegenerateBootstrap.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Why the smoke-leg bootstrap degenerated, and what that forces about the event count

Context (experiment 569, paper 216).  The run's ledger records a `NaN` verdict field on the
smoke leg and attributes it to a "starved-regime bootstrap": fewer than `100` of the
`NB = 2000` cluster resamples were non-degenerate, so the percentile bounds were `NaN` and
`excludes_1` was trivially `True`.  This file turns that anecdote into a theorem about the
resampling scheme itself.

A cluster bootstrap over `m` clusters draws a resample uniformly from the `m ^ m` functions
`Fin m → Fin m`.  Call a cluster an *event cluster* if it carries at least one smooth hit;
a resample is *degenerate* exactly when it selects no event cluster, since then both the
candidate and the control tallies vanish and the ratio is `0/0`.

Main results:

* `U9Drift.card_event_free_resamples` — exactly `(m - h) ^ m` of the `m ^ m` resamples avoid a
  fixed set of `h` event clusters (an exact count, proved by identifying the filtered set with
  a `Fintype.piFinset`).
* `U9Drift.degenerateFrac_eq` — hence the degenerate fraction is exactly `(1 - h/m) ^ m`.
* `U9Drift.degenerateFrac_le_exp` — the sharp exponential bound `(1 - h/m) ^ m ≤ exp (-h)`,
  uniform in the cluster count `m`.
* `U9Drift.nondegenerate_fraction_ge` — consequently a *single* event cluster already forces
  at least a `0.632` fraction of non-degenerate resamples, whatever `m` is.
* `U9Drift.starved_nan_requires_event_free_population` — therefore the observed smoke-leg
  behaviour (fewer than `100` of `2000` expected non-degenerate resamples) is impossible with
  even one event cluster: the `NaN` is not resampling bad luck but reports a population with
  no smooth hit at all.  This is exactly why the ledger's "non-canonical, full-run verdict
  governs" ruling is the correct one — the smoke-leg interval carries no information about
  the ratio, rather than carrying a wide one.
-/

namespace U9Drift

open Finset


/-- The fraction of degenerate (event-free) resamples in a cluster bootstrap over `m`
clusters of which `h` carry an event. -/
noncomputable def degenerateFrac (m h : ℕ) : ℝ := ((m - h : ℕ) : ℝ) ^ m / (m : ℝ) ^ m






end U9Drift


