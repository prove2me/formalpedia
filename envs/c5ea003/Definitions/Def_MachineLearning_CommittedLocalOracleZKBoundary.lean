-- Prove2me | Definitions.Def_MachineLearning_CommittedLocalOracleZKBoundary
-- name    : MachineLearning_CommittedLocalOracleZKBoundary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:53.199404+00:00
-- url     : https://prove2.me/theorems/72bf8287-180d-4250-a57a-b0ec10b60fb7
-- title:
--   Aether Catalog definitions — MachineLearning_CommittedLocalOracleZKBoundary
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CommittedLocalOracleZKBoundary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CommittedLocalOracleZKBoundary.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

/-!
# Boundary of the composition theorem: both hypotheses are load-bearing

`MachineLearning/CommittedLocalOracleZK.lean` proves that

  *perfect hiding of unopened coordinates* + *perfect simulation of opened
  coordinates* ⟹ *perfect honest-verifier zero knowledge*.

This file shows that **neither hypothesis may be dropped**, by exhibiting two
explicit tiny committed local-oracle protocols:

* `leakyOracle` — a 1-query protocol whose *opened* coordinate is perfectly
  simulated (`leaky_simulates`) but whose commitment is the identity, so unopened
  coordinates leak (`leaky_not_hiding`). Its real and simulated transcript
  distributions differ maximally: `1` versus `0` (`leaky_hvzk_fails`).
* `padOracle` — a one-time-padded protocol, hence perfectly hiding
  (`pad_hides`), equipped with a simulator that guesses the wrong colour for the
  *opened* coordinate (`badSim_not_simulating`); again the transcript
  distributions differ, `1/2` versus `0` (`pad_hvzk_fails`).

Together with the positive theorem these delimit exactly what the composition
needs: hiding controls the unopened part, simulation the opened part, and each
failure is visible already at query complexity one.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the two hypotheses of `perfect_hvzk` are independent;
neither implies the other, and each alone is insufficient.

Experiment (Experimenter): the two protocols below are the minimal witnesses —
two coordinates over `ZMod 2` for the hiding failure (one opened, one unopened,
so that the leak is invisible in the opened view), one coordinate for the
simulation failure. The probabilities are computed by direct evaluation of the
counting definitions.

Analysis (Analyst): the hiding counterexample shows the failure is *not*
detectable from the opened view alone — `leaky_simulates` holds — so the
composition theorem really is a statement about the commitment, not about the
query pattern.

Critique (Critic): both counterexamples are non-vacuous (all randomness spaces
are nonempty and the transcripts exhibited actually occur in the real
interaction, with probability `1` and `1/2` respectively).

Synthesis (PI): the composition theorem is tight.
-- !-- Lab Notes -- !--
-/

namespace MachineLearning.CommittedLocalOracleZKBoundary

open Finset MachineLearning.CommittedLocalOracleZK

/-! ## Hiding is necessary: a perfectly simulatable but leaking protocol -/

/-- A 1-query protocol on two coordinates over `ZMod 2` whose "commitment" is the
identity map: it publishes the whole proof string. The queried coordinate is
always coordinate `0`, whose value is constantly `0`; coordinate `1` is never
opened and carries the value `1`. -/
def leakyOracle : CommittedOracle (Fin 2) (ZMod 2) (Fin 2 → ZMod 2) Unit Unit Unit Unit where
  com u _ := u
  openInfo _ _ _ := ()
  Q _ := {0}
  qbound := 1
  query_card_le := by intro _; simp
  proof _ := fun i => if i = 0 then 0 else 1

/-- The simulator for `leakyOracle`: it writes `0` everywhere, which reproduces
the opened coordinate exactly. -/
def leakySim : Unit → Unit → Fin 2 → ZMod 2 := fun _ _ _ => 0






/-! ## Simulation is necessary: a perfectly hiding protocol with a wrong simulator -/

/-- A one-coordinate one-time-padded protocol whose proof string is constantly
`0`. -/
def padOracle : CommittedOracle (Fin 1) (ZMod 2) (Fin 1 → ZMod 2) (Fin 1 → Option (ZMod 2))
    (Fin 1 → ZMod 2) Unit Unit :=
  otpOracle (fun _ _ => 0) (fun _ => {0}) 1 (by intro _; simp)

/-- A simulator that opens the *wrong* value at the queried coordinate. -/
def badSim : Unit → Unit → Fin 1 → ZMod 2 := fun _ _ _ => 1





/-! ## Sharp 2-transitivity is necessary: cyclic rerandomization leaks

In the 3-colouring protocol the prover rerandomizes its colouring with a uniform
element of the *symmetric* group `S₃`. Replacing `S₃` by the cyclic subgroup of
colour shifts (order 3, still transitive on colours!) destroys zero knowledge:
the opened pair then determines the colour *difference* along the challenged
edge. We prove this as a genuine impossibility statement: **no** simulator
whatsoever — with arbitrary randomness space — can simulate the shift-based
protocol for both of two colourings simultaneously, so no witness-independent
simulator exists. -/

/-- A two-vertex, one-edge instance queried at both endpoints, where the prover
rerandomizes its colouring by a *cyclic shift* `c ↦ c + d` instead of a full
colour permutation. -/
def shiftOracle (c : Fin 2 → ZMod 3) :
    CommittedOracle (Fin 2) (ZMod 3) (Fin 2 → ZMod 3) (Fin 2 → Option (ZMod 3))
      (Fin 2 → ZMod 3) Unit (ZMod 3) :=
  otpOracle (fun d v => c v + d) (fun _ => {0, 1}) 2
    (by intro _; exact le_trans (card_insert_le _ _) (by simp))

/-- The proper colouring `(0, 1)` of the single edge. -/
def colA : Fin 2 → ZMod 3 := fun v => if v = 0 then 0 else 1

/-- The proper colouring `(0, 2)` of the single edge. -/
def colB : Fin 2 → ZMod 3 := fun v => if v = 0 then 0 else 2

/-- The opened view targeted in the separation: colour `0` on the first endpoint
and `1` on the second. -/
def viewAB : Fin 2 → Option (ZMod 3) := fun v => if v = 0 then some 0 else some 1


end MachineLearning.CommittedLocalOracleZKBoundary


