-- Prove2me | Definitions.Def_MachineLearning_LifeboxInformationIdentity
-- name    : MachineLearning_LifeboxInformationIdentity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:23.500224+00:00
-- url     : https://prove2.me/theorems/f4ff292c-b4e8-4f77-beda-c1bed377e321
-- title:
--   Aether Catalog definitions — MachineLearning_LifeboxInformationIdentity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.LifeboxInformationIdentity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/LifeboxInformationIdentity.lean by skeleton subtraction
import Mathlib

/-! # Lifebox information-theoretic identity

This file models identity as observable behavior rather than physical substrate. It proves
that behavioral equivalence of initialized finite Moore machines is decidable, proves a
finite-test obstruction for unrestricted systems, formalizes the linear no-cloning
obstruction, and gives a precise conditional version of a finite description-complexity
bound.
-/

namespace LifeboxIdentity

/-- A deterministic finite-state system whose current state has an observable output. -/
structure MooreMachine (Input State Output : Type*) where
  step : State → Input → State
  observe : State → Output

namespace MooreMachine

variable {Input S T U Output : Type*}

/-- The state reached from `s` after processing a finite input word. -/
def runFrom (M : MooreMachine Input S Output) (s : S) (w : List Input) : S :=
  w.foldl M.step s


@[simp] theorem runFrom_cons (M : MooreMachine Input S Output) (s : S)
    (a : Input) (w : List Input) :
    M.runFrom s (a :: w) = M.runFrom (M.step s a) w := by
  simp [runFrom]

/-- Two initialized systems are person-equivalent when every finite experiment gives the
same observation. -/
def PersonEquiv (M : MooreMachine Input S Output) (N : MooreMachine Input T Output)
    (s : S) (t : T) : Prop :=
  ∀ w : List Input, M.observe (M.runFrom s w) = N.observe (N.runFrom t w)




/-- A Boolean relation is a bisimulation when it preserves observations and transitions. -/
def IsBisimulation (M : MooreMachine Input S Output) (N : MooreMachine Input T Output)
    (R : S → T → Bool) : Prop :=
  ∀ s t, R s t = true →
    M.observe s = N.observe t ∧ ∀ a, R (M.step s a) (N.step t a) = true

/-- A finite certificate of behavioral identity consists of a Boolean bisimulation
containing the two initial states. -/
def HasBisimulation (M : MooreMachine Input S Output) (N : MooreMachine Input T Output)
    (s : S) (t : T) : Prop :=
  ∃ R : S → T → Bool, R s t = true ∧ M.IsBisimulation N R

/-- Every bisimulation certificate implies equality of all finite observations. -/
theorem personEquiv_of_hasBisimulation
    (M : MooreMachine Input S Output) (N : MooreMachine Input T Output)
    {s : S} {t : T} (h : M.HasBisimulation N s t) : M.PersonEquiv N s t := by
  obtain ⟨R, hst, hR⟩ := h
  intro w
  induction w generalizing s t with
  | nil => exact (hR s t hst).1
  | cons a w ih =>
      simp only [runFrom_cons]
      exact ih ((hR s t hst).2 a)

/-- Equality of all finite observations itself defines a Boolean bisimulation. -/
theorem hasBisimulation_of_personEquiv
    (M : MooreMachine Input S Output) (N : MooreMachine Input T Output)
    {s : S} {t : T} (h : M.PersonEquiv N s t) : M.HasBisimulation N s t := by
  classical
  let R : S → T → Bool := fun x y => decide (M.PersonEquiv N x y)
  refine ⟨R, ?_, ?_⟩
  · simp [R, h]
  · intro x y hxy
    have htrace : M.PersonEquiv N x y := by
      simpa [R] using hxy
    constructor
    · exact htrace []
    · intro a
      simp only [R, decide_eq_true_eq]
      intro w
      exact htrace (a :: w)

/-- Behavioral identity is equivalent to the existence of a finite bisimulation table. -/
theorem personEquiv_iff_hasBisimulation
    (M : MooreMachine Input S Output) (N : MooreMachine Input T Output)
    (s : S) (t : T) :
    M.PersonEquiv N s t ↔ M.HasBisimulation N s t := by
  exact ⟨hasBisimulation_of_personEquiv M N,
    personEquiv_of_hasBisimulation M N⟩

/-- Behavioral identity of finite-state systems is decidable, despite quantifying over
infinitely many finite input histories. The decision procedure searches the finite space
of Boolean relations for a bisimulation certificate. -/
instance personEquivDecidable [Fintype Input] [Fintype S] [Fintype T]
    [DecidableEq Input] [DecidableEq S] [DecidableEq T] [DecidableEq Output]
    (M : MooreMachine Input S Output) (N : MooreMachine Input T Output)
    (s : S) (t : T) : Decidable (M.PersonEquiv N s t) := by
  rw [personEquiv_iff_hasBisimulation]
  unfold HasBisimulation IsBisimulation
  infer_instance

end MooreMachine


open scoped TensorProduct


/-- A description scheme assigns finite bit strings to the identities they decode. -/
structure DescriptionScheme (Identity : Type*) where
  decode : List Bool → Option Identity

namespace DescriptionScheme

variable {Identity : Type*}

/-- The description complexity of an identity is the least length of a bit string that
decodes to it; it is zero when no description exists. -/
noncomputable def complexity (D : DescriptionScheme Identity) (x : Identity) : ℕ :=
  sInf {n : ℕ | ∃ code : List Bool, code.length = n ∧ D.decode code = some x}




end DescriptionScheme


end LifeboxIdentity


