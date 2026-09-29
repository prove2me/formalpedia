-- Prove2me | Definitions.Def_Probability_SelfModHalt
-- name    : Probability_SelfModHalt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:53.109134+00:00
-- url     : https://prove2.me/theorems/2febea59-ca11-4a11-9168-c679d8c3f566
-- title:
--   Aether Catalog definitions — Probability_SelfModHalt
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SelfModHalt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SelfModHalt.lean by skeleton subtraction
import Mathlib

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

namespace SelfModHalt

/-- Many-one reducibility between predicates on arbitrary types: `A` reduces to `B` when
there is a map `f` with `A x ↔ B (f x)`. -/
def ManyOneReduces {α β : Sort*} (A : α → Prop) (B : β → Prop) : Prop :=
  ∃ f : α → β, ∀ x, A x ↔ B (f x)



/-- A configuration of a self-modifying machine: the current program together with the
current state. -/
structure SelfModConfig (P S : Type*) where
  /-- The current (rewritable) program. -/
  prog : P
  /-- The current state. -/
  state : S

/-- A self-modifying machine: one step may rewrite the program as well as the state, and
returns `none` when the machine halts. -/
structure SelfModMachine (P S : Type*) where
  /-- The one-step transition; `none` means "halted". -/
  step : SelfModConfig P S → Option (SelfModConfig P S)

/-- A machine with a fixed program: one step transforms the state, and returns `none`
when the machine halts. -/
structure StdMachine (X : Type*) where
  /-- The one-step transition; `none` means "halted". -/
  step : X → Option X

variable {P S X : Type*}

/-- `n` steps of a self-modifying machine; `none` records that the run has halted. -/
def SelfModMachine.run (m : SelfModMachine P S) (cfg : SelfModConfig P S) :
    ℕ → Option (SelfModConfig P S)
  | 0 => some cfg
  | n + 1 => (m.run cfg n).bind m.step

/-- `n` steps of a fixed-program machine. -/
def StdMachine.run (M : StdMachine X) (x : X) : ℕ → Option X
  | 0 => some x
  | n + 1 => (M.run x n).bind M.step

/-- A self-modifying machine halts on a configuration when some finite run is undefined. -/
def SelfModMachine.halts (m : SelfModMachine P S) (cfg : SelfModConfig P S) : Prop :=
  ∃ n, m.run cfg n = none

/-- A fixed-program machine halts on a state when some finite run is undefined. -/
def StdMachine.halts (M : StdMachine X) (x : X) : Prop :=
  ∃ n, M.run x n = none

/-- `d` decides the halting problem of the fixed-program machine `M`. -/
def StdHaltingDecider (M : StdMachine X) (d : X → Bool) : Prop :=
  ∀ x, d x = true ↔ M.halts x

/-- The fixed-program simulation of a self-modifying machine: the program is stored in
the state, so the transition function is fixed. -/
def SelfModMachine.toStd (m : SelfModMachine P S) : StdMachine (P × S) :=
  ⟨fun x => (m.step ⟨x.1, x.2⟩).map (fun c => (c.prog, c.state))⟩




/-- Every fixed-program machine is a self-modifying machine with a one-element program
type, with the same halting behaviour. -/
def StdMachine.toSelfMod (M : StdMachine X) : SelfModMachine Unit X :=
  ⟨fun c => (M.step c.state).map (fun y => ⟨(), y⟩)⟩




end SelfModHalt


