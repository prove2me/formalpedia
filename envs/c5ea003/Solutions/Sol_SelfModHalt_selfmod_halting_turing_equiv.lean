-- Prove2me | solution 1 for SelfModHalt.selfmod_halting_turing_equiv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:15.799829+00:00
-- url     : https://prove2.me/submissions/cac802c5-84dd-4f2a-a123-e6360992615e

-- Sol generated from Probability/SelfModHalt.lean
import Mathlib
import Definitions.Def_Probability_SelfModHalt
import Theorems.Thm_SelfModHalt_selfmod_halting_reduces_to_standard

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











theorem toSelfMod_run (M : StdMachine X) (x : X) (n : ℕ) :
    M.toSelfMod.run ⟨(), x⟩ n = (M.run x n).map (fun y => ⟨(), y⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [SelfModMachine.run, ih, StdMachine.run]
      cases h : M.run x n with
      | none => simp
      | some y => simp [StdMachine.toSelfMod]

theorem std_halts_iff_selfmod (M : StdMachine X) (x : X) :
    M.halts x ↔ M.toSelfMod.halts ⟨(), x⟩ := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [toSelfMod_run, hn]; rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [toSelfMod_run] at hn
    cases h : M.run x n with
    | none => rfl
    | some y => rw [h] at hn; exact absurd hn (by simp)



open SelfModHalt in
theorem solution(m : SelfModMachine P S) :
    ManyOneReduces m.halts m.toStd.halts ∧
      ∃ m' : SelfModMachine Unit (P × S), ManyOneReduces m.toStd.halts m'.halts :=
  ⟨selfmod_halting_reduces_to_standard m,
    m.toStd.toSelfMod, fun x => ⟨(), x⟩, std_halts_iff_selfmod m.toStd⟩
