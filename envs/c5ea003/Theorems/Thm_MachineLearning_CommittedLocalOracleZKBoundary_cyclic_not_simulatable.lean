-- Prove2me | Theorems.Thm_MachineLearning_CommittedLocalOracleZKBoundary_cyclic_not_simulatable
-- name    : MachineLearning.CommittedLocalOracleZKBoundary.cyclic_not_simulatable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:43:00.019438+00:00
-- url     : https://prove2.me/theorems/f080e07f-0929-4f00-ab01-90b4f3b44fa8
-- title:
--   Cyclic rerandomization is not simulatable.
-- statement:
--   **Cyclic rerandomization is not simulatable.** No simulator (over any finite,
--   nonempty randomness space) perfectly simulates the opened view of the
--   shift-randomized protocol for both proper colourings `colA` and `colB`: the view
--   `(0,1)` has probability `1/3` under `colA` and `0` under `colB`. Hence the
--   zero-knowledge property of the 3-colouring protocol genuinely uses the *sharply
--   2-transitive* action of the full symmetric group, not mere transitivity.
--
--   ```lean
--   theorem MachineLearning.CommittedLocalOracleZKBoundary.cyclic_not_simulatable{S : Type} [Fintype S] [Nonempty S]
--       (sim : Unit → S → Fin 2 → ZMod 3) :
--       ¬ (PerfectlySimulatesOpened (shiftOracle colA) sim ∧
--           PerfectlySimulatesOpened (shiftOracle colB) sim) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CommittedLocalOracleZKBoundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CommittedLocalOracleZKBoundary.lean#L187

-- Thm stub generated from MachineLearning/CommittedLocalOracleZKBoundary.lean
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK
import Definitions.Def_MachineLearning_CommittedLocalOracleZKBoundary

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

open MachineLearning.CommittedLocalOracleZKBoundary

open Finset MachineLearning.CommittedLocalOracleZK

/-! ## Hiding is necessary: a perfectly simulatable but leaking protocol -/








/-! ## Simulation is necessary: a perfectly hiding protocol with a wrong simulator -/







/-! ## Sharp 2-transitivity is necessary: cyclic rerandomization leaks

In the 3-colouring protocol the prover rerandomizes its colouring with a uniform
element of the *symmetric* group `S₃`. Replacing `S₃` by the cyclic subgroup of
colour shifts (order 3, still transitive on colours!) destroys zero knowledge:
the opened pair then determines the colour *difference* along the challenged
edge. We prove this as a genuine impossibility statement: **no** simulator
whatsoever — with arbitrary randomness space — can simulate the shift-based
protocol for both of two colourings simultaneously, so no witness-independent
simulator exists. -/

theorem MachineLearning.CommittedLocalOracleZKBoundary.cyclic_not_simulatable{S : Type} [Fintype S] [Nonempty S]
    (sim : Unit → S → Fin 2 → ZMod 3) :
    ¬ (PerfectlySimulatesOpened (shiftOracle colA) sim ∧
        PerfectlySimulatesOpened (shiftOracle colB) sim) := by sorry
