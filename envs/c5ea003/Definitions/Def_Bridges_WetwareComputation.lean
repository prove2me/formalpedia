-- Prove2me | Definitions.Def_Bridges_WetwareComputation
-- name    : Bridges_WetwareComputation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:47.4339+00:00
-- url     : https://prove2.me/theorems/5c3b1b07-7da8-46b8-83a6-e247598edc49
-- title:
--   Aether Catalog definitions — Bridges_WetwareComputation
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.WetwareComputation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/WetwareComputation.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wetware Computation: A Bridge from Discrete Dynamics to the Information Cost of Determinism

A **wetware** computation is modelled as a discrete dynamical system: a *step map*
`step : S → S` on a (neural) state space `S`, run by iteration.  This file develops
the model and then proves a *connector* theorem linking two a-priori unrelated areas:

* **Enumerative combinatorics** — counting the configurations of two hardware models
  (deterministic transition maps vs. arbitrary connection matrices), and
* **Information theory / asymptotic analysis** — the Shannon information (energy, in
  bits) needed to specify one configuration, and its asymptotics.

## The model

* `WetwareSystem S` — a dynamical system on `S` given by its `step` map.
* `WetwareSystem.run t x = step^[t] x` — running the system for `t` steps.
* `run_add` — the *flow / semigroup* law `run (s+t) = run s ∘ run t`: a wetware
  system is a monoid action of `(ℕ, +)`, the mathematical core of "iterated computation".

## Computation

* `exists_wetware_computes` — **universality on finite data**: *every* function
  `f : X → Y` between finite types is computed by some wetware system (with an
  encoder and a decoder).  This is the finite-state analogue of Turing-completeness.
* `orbit_eventually_periodic` — the **dynamics ↔ finiteness** bridge: on a finite
  state space every orbit collides with itself, hence is eventually periodic
  (pigeonhole).  A wetware system with finitely many neurons cannot compute
  aperiodic behaviour by pure iteration.

## Energy — the connector theorem

For `n` neurons we compare two hardware disciplines by their number of
*distinguishable configurations* and take the base-2 logarithm (Shannon information):

* **Wetware** = a deterministic transition map `Fin n → Fin n`.
  `wetware_config_card : #(Fin n → Fin n) = n ^ n`, hence
  `wetwareEnergy_eq : wetwareEnergy n = n * logb 2 n`   — `Θ(n log n)` bits.
* **Silicon** = an arbitrary binary connection matrix `Fin n → Fin n → Bool`.
  `silicon_config_card : #(Fin n → Fin n → Bool) = 2 ^ (n ^ 2)`, hence
  `siliconEnergy_eq : siliconEnergy n = n ^ 2`          — `Θ(n²)` bits.

The bridge results:

* `wetware_beats_silicon` — for `n ≥ 1`, `wetwareEnergy n < siliconEnergy n`.
* `energy_ratio_tendsto_zero` — `wetwareEnergy n / siliconEnergy n → 0`:
  the information cost of *determinism* is asymptotically negligible next to the
  cost of arbitrary *connectivity*.

## Application keywords

dynamical systems, discrete dynamics, iteration, neural computation, wetware,
Turing completeness, pigeonhole, eventual periodicity, information theory, Shannon
information, enumerative combinatorics, asymptotics, little-o, geometry of state space
-/

open Real Filter Topology

namespace Wetware

universe u

/-! ## The wetware dynamical system -/

/-- A **wetware system** on a state space `S`: a discrete dynamical system given by
its one-step transition (`step`) map.  Running the system means iterating `step`. -/
structure WetwareSystem (S : Type*) where
  /-- The one-step neural transition map. -/
  step : S → S

variable {S : Type*}

/-- Running a wetware system for `t` steps from state `x`. -/
def WetwareSystem.run (W : WetwareSystem S) (t : ℕ) (x : S) : S := W.step^[t] x


@[simp] theorem WetwareSystem.run_one (W : WetwareSystem S) (x : S) : W.run 1 x = W.step x := rfl



/-! ## Computation: universality on finite data (finite-state Turing completeness) -/

/-- `W` **computes** `f : X → Y` in `T` steps with encoder `enc` and decoder `dec`
if decoding the state reached after running the encoded input for `T` steps returns
`f x`. -/
def Computes {X Y : Type*} (W : WetwareSystem S) (enc : X → S) (dec : S → Y)
    (T : ℕ) (f : X → Y) : Prop :=
  ∀ x, dec (W.run T (enc x)) = f x


/-! ## Dynamics ↔ finiteness: eventual periodicity -/


/-! ## Energy: the connector theorem (combinatorics ↔ information/asymptotics) -/

/-- The **wetware energy** on `n` neurons: the Shannon information (bits) needed to
specify one deterministic transition map `Fin n → Fin n`, i.e. the base-2 log of the
number of such maps. -/
noncomputable def wetwareEnergy (n : ℕ) : ℝ :=
  Real.logb 2 (Fintype.card (Fin n → Fin n))

/-- The **silicon energy** on `n` neurons: the Shannon information (bits) needed to
specify one arbitrary binary connection matrix `Fin n → Fin n → Bool`. -/
noncomputable def siliconEnergy (n : ℕ) : ℝ :=
  Real.logb 2 (Fintype.card (Fin n → Fin n → Bool))








end Wetware


