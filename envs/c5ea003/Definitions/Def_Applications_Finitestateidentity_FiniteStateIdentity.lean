-- Prove2me | Definitions.Def_Applications_Finitestateidentity_FiniteStateIdentity
-- name    : Applications_Finitestateidentity_FiniteStateIdentity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:54:41.783706+00:00
-- url     : https://prove2.me/theorems/d3ced456-749a-4c39-9c7e-cd225546154a
-- title:
--   Aether Catalog definitions — Applications_Finitestateidentity_FiniteStateIdentity
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Finitestateidentity.FiniteStateIdentity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Finitestateidentity/FiniteStateIdentity.lean by skeleton subtraction
import Mathlib

/-! # Finite-state information-theoretic identity

This file gives a genuine finite-state version of behavioural identity.  A person model is
a finite Moore machine: it changes state in response to each input symbol and exposes an
observation at every state.  Two initialized machines are person-equivalent when every
finite input history produces the same observation.

The main theorem, `traceEquiv_iff_hasBisimulation`, characterizes this infinitary-looking
condition by the existence of a finite Boolean bisimulation table.  Since all possible
tables can be searched, `traceEquiv_decidable` proves that person-equivalence of finite-state
models is decidable even though there are infinitely many input words.
-/

namespace Lifebox

/-- A deterministic finite-state person model with Moore-style observations. -/
structure FinitePerson (Input State Output : Type*) where
  step : State → Input → State
  observe : State → Output

namespace FinitePerson

variable {Input S T Output : Type*}

/-- State reached after a finite input history. -/
def runFrom (M : FinitePerson Input S Output) (s : S) (w : List Input) : S :=
  w.foldl M.step s

@[simp] theorem runFrom_cons (M : FinitePerson Input S Output) (s : S)
    (a : Input) (w : List Input) :
    M.runFrom s (a :: w) = M.runFrom (M.step s a) w := rfl



/-- Behavioural identity: every finite experiment has the same observable result. -/
def TraceEquiv (M : FinitePerson Input S Output) (N : FinitePerson Input T Output)
    (s : S) (t : T) : Prop :=
  ∀ w : List Input, M.observe (M.runFrom s w) = N.observe (N.runFrom t w)


/-- A finite Boolean table is a bisimulation when related states have equal observations
and every one-step successor pair remains in the table. -/
def IsBisimulation (M : FinitePerson Input S Output) (N : FinitePerson Input T Output)
    (R : S → T → Bool) : Prop :=
  ∀ s t, R s t = true →
    M.observe s = N.observe t ∧ ∀ a, R (M.step s a) (N.step t a) = true

/-- Two states possess a finite Boolean bisimulation certificate. -/
def HasBisimulation (M : FinitePerson Input S Output) (N : FinitePerson Input T Output)
    (s : S) (t : T) : Prop :=
  ∃ R : S → T → Bool, R s t = true ∧ M.IsBisimulation N R

/-- A bisimulation certificate guarantees equal observations after every input history. -/
theorem traceEquiv_of_hasBisimulation
    (M : FinitePerson Input S Output) (N : FinitePerson Input T Output)
    {s : S} {t : T} (h : M.HasBisimulation N s t) : M.TraceEquiv N s t := by
  obtain ⟨R, hRst, hR⟩ := h
  intro w
  induction w generalizing s t with
  | nil => exact (hR s t hRst).1
  | cons a w ih =>
      simp only [runFrom_cons]
      exact ih ((hR s t hRst).2 a)

/-- Trace equivalence itself determines a Boolean bisimulation table. -/
theorem hasBisimulation_of_traceEquiv
    (M : FinitePerson Input S Output) (N : FinitePerson Input T Output)
    {s : S} {t : T} (h : M.TraceEquiv N s t) : M.HasBisimulation N s t := by
  classical
  let R : S → T → Bool := fun x y => decide (M.TraceEquiv N x y)
  refine ⟨R, ?_, ?_⟩
  · simp [R, h]
  · intro x y hxy
    have htrace : M.TraceEquiv N x y := by
      simpa [R] using hxy
    constructor
    · exact htrace []
    · intro a
      simp only [R, decide_eq_true_eq]
      intro w
      exact htrace (a :: w)

/-- The coinductive behavioural definition is exactly finite Boolean bisimilarity. -/
theorem traceEquiv_iff_hasBisimulation
    (M : FinitePerson Input S Output) (N : FinitePerson Input T Output)
    (s : S) (t : T) :
    M.TraceEquiv N s t ↔ M.HasBisimulation N s t := by
  exact ⟨hasBisimulation_of_traceEquiv M N, traceEquiv_of_hasBisimulation M N⟩

/-- **Finite-state Lifebox theorem.** Behavioural identity of two finite person models is
algorithmically decidable.  The decision procedure searches the finite space of Boolean
relations on pairs of states for a bisimulation certificate. -/
instance traceEquiv_decidable [Fintype Input] [Fintype S] [Fintype T]
    [DecidableEq Input] [DecidableEq S] [DecidableEq T] [DecidableEq Output]
    (M : FinitePerson Input S Output) (N : FinitePerson Input T Output)
    (s : S) (t : T) : Decidable (M.TraceEquiv N s t) := by
  rw [traceEquiv_iff_hasBisimulation]
  unfold HasBisimulation IsBisimulation
  infer_instance



end FinitePerson
end Lifebox


