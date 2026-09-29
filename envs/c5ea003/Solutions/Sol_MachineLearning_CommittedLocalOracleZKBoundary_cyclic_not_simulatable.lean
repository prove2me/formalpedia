-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZKBoundary.cyclic_not_simulatable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:16:47.543261+00:00
-- url     : https://prove2.me/submissions/0d5610ff-d00c-40b5-9511-66669bac6fe0

-- Sol generated from MachineLearning/CommittedLocalOracleZKBoundary.lean
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







open MachineLearning.CommittedLocalOracleZKBoundary in
theorem solution{S : Type} [Fintype S] [Nonempty S]
    (sim : Unit → S → Fin 2 → ZMod 3) :
    ¬ (PerfectlySimulatesOpened (shiftOracle colA) sim ∧
        PerfectlySimulatesOpened (shiftOracle colB) sim) := by
  rintro ⟨h1, h2⟩
  have e1 := h1 () viewAB
  have e2 := h2 () viewAB
  have c1 : (univ.filter fun d : ZMod 3 =>
      restrictTo ((shiftOracle colA).Q ()) ((shiftOracle colA).proof d) = viewAB).card = 1 := by
    decide
  have c2 : (univ.filter fun d : ZMod 3 =>
      restrictTo ((shiftOracle colB).Q ()) ((shiftOracle colB).proof d) = viewAB).card = 0 := by
    decide
  have hQ : (shiftOracle colB).Q () = (shiftOracle colA).Q () := rfl
  rw [c1] at e1
  rw [c2, hQ] at e2
  have hcard3 : Fintype.card (ZMod 3) = 3 := ZMod.card 3
  have hSpos : 0 < Fintype.card S := Fintype.card_pos
  rw [hcard3] at e1 e2
  omega
