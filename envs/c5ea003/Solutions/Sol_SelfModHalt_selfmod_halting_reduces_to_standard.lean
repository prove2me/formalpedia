-- Prove2me | solution 1 for SelfModHalt.selfmod_halting_reduces_to_standard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:04:24.720398+00:00
-- url     : https://prove2.me/submissions/990aedd6-53ad-4f3e-9568-41b837ad16a8

-- Sol generated from Probability/SelfModHalt.lean
import Mathlib
import Definitions.Def_Probability_SelfModHalt
import Theorems.Thm_SelfModHalt_selfmod_halts_iff_standard

/-! # Self-modifying machines and their halting problem

This module supplies the machine model used by
`Novelty.SelfModifyingUndecidability`, whose own import of it was lost from the catalog
snapshot: a *self-modifying* machine carries its program inside the configuration and
may rewrite it at every step, whereas a *standard* machine has a fixed transition
function on a state space.

The main content is the simulation lemma `selfmod_halts_iff_standard` ("code is data"):
storing the changing program in the state turns a self-modifying machine into an
ordinary one with the *same* halting behaviour, so self-modification does not raise the
degree of the halting problem.
-/

open SelfModHalt







variable {P S X : Type*}















open SelfModHalt in
theorem solution(m : SelfModMachine P S) :
    ManyOneReduces m.halts m.toStd.halts :=
  ⟨fun cfg => (cfg.prog, cfg.state), selfmod_halts_iff_standard m⟩
