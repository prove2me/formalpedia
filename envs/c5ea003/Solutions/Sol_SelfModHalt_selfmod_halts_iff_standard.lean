-- Prove2me | solution 1 for SelfModHalt.selfmod_halts_iff_standard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:21.811645+00:00
-- url     : https://prove2.me/submissions/65b0e5bb-29fa-4957-87cb-07ab732b48f6

-- Sol generated from Probability/SelfModHalt.lean
import Mathlib
import Definitions.Def_Probability_SelfModHalt

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







/-- Step-for-step simulation: the fixed-program run is the self-modifying run, read
through the "code is data" bijection. -/
theorem toStd_run (m : SelfModMachine P S) (cfg : SelfModConfig P S) (n : ℕ) :
    m.toStd.run (cfg.prog, cfg.state) n
      = (m.run cfg n).map (fun c => (c.prog, c.state)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [StdMachine.run, ih, SelfModMachine.run]
      cases h : m.run cfg n with
      | none => simp
      | some c => simp [SelfModMachine.toStd]








open SelfModHalt in
theorem solution(m : SelfModMachine P S) (cfg : SelfModConfig P S) :
    m.halts cfg ↔ m.toStd.halts (cfg.prog, cfg.state) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [toStd_run, hn]; rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [toStd_run] at hn
    cases h : m.run cfg n with
    | none => rfl
    | some c => rw [h] at hn; exact absurd hn (by simp)
