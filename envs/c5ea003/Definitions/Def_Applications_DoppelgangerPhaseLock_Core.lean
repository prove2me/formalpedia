-- Prove2me | Definitions.Def_Applications_DoppelgangerPhaseLock_Core
-- name    : Applications_DoppelgangerPhaseLock_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:41:42.716384+00:00
-- url     : https://prove2.me/theorems/cc7b0407-190c-4786-8c3e-3eb6e20e7bdf
-- title:
--   Aether Catalog definitions — Applications_DoppelgangerPhaseLock_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DoppelgangerPhaseLock.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DoppelgangerPhaseLock/Core.lean by skeleton subtraction
import Mathlib
/-
# Doppelgänger Phase-Lock — Core theory

Two spatially separated but *identical* agents are modelled as two copies of one
deterministic reactive system

```
δ : S → I → S
```

(`S` = internal state space, `I` = alphabet of environmental stimuli).  Both
copies observe the *same* stimulus stream; the question of "quantum telepathic
synchronization" is thereby demystified into an exact mathematical question:

> for which `δ` does there exist a finite stimulus word `w` after which the two
> copies occupy the *same* internal state, no matter how far apart their initial
> states were?

This is exactly the classical notion of a **synchronizing (reset) word** for a
deterministic automaton, and this file develops it from scratch in the language
of phase-locking agents.

## Main definitions

* `Doppelganger.drive δ w s` — the state reached from `s` after the stimulus word `w`.
* `Doppelganger.Locks δ w` — `w` *phase-locks* the pair of agents: it maps **all**
  states to a common state.
* `Doppelganger.Mergeable δ s t` — the particular pair `(s,t)` can be locked.
* `Doppelganger.PhaseLocking δ` — some word locks the doppelgänger pair.

## Main results

* `Doppelganger.drive_append`, `Doppelganger.transitionHom` — the stimulus monoid acts
  on the state space; `w ↦ drive δ w` is a monoid *anti*-homomorphism
  `FreeMonoid I →* (Function.End S)ᵐᵒᵖ` (algebraic layer).
* `Doppelganger.locks_ideal` — the set of phase-locking words is a two-sided ideal of
  the free monoid of stimuli: *once telepathy is possible, no amount of extra noise,
  before or after, can destroy it*.
* `Doppelganger.Locks.flatten_of_mem` — a stimulus stream chopped into blocks locks as
  soon as **one** block locks (used for the quantitative rarity estimates).
* `Doppelganger.phaseLocking_iff_const_mem_range` — phase-locking is equivalent to the
  transition monoid containing a constant map (rank-one element).
* `Doppelganger.locked_forever` — phase-lock is absorbing: the diagonal is invariant.
-/

namespace Doppelganger

variable {S I : Type*}

/-! ### The stimulus action -/

/-- `drive δ w s` is the state reached by an agent with transition rule `δ`, started in
state `s`, after observing the finite stimulus word `w` (left to right). -/
def drive (δ : S → I → S) (w : List I) (s : S) : S := w.foldl δ s




/-- Concatenation of stimuli = composition of state maps (in the opposite order). -/
lemma drive_append (δ : S → I → S) (w v : List I) (s : S) :
    drive δ (w ++ v) s = drive δ v (drive δ w s) := by
  simp [drive]

/-- The length-`n` prefix of an infinite stimulus stream. -/
def pre (x : ℕ → I) (n : ℕ) : List I := List.ofFn fun i : Fin n => x i


/-! ### Phase-locking -/

/-- The stimulus word `w` **phase-locks** the agents: after observing `w`, two copies of
the agent are in the same internal state whatever their initial states were. -/
def Locks (δ : S → I → S) (w : List I) : Prop := ∀ s t : S, drive δ w s = drive δ w t

/-- The particular pair of states `(s,t)` can be merged by some stimulus word. -/
def Mergeable (δ : S → I → S) (s t : S) : Prop := ∃ w : List I, drive δ w s = drive δ w t

/-- The agent design `δ` admits doppelgänger phase-lock. -/
def PhaseLocking (δ : S → I → S) : Prop := ∃ w : List I, Locks δ w








/-! ### The algebraic layer: the transition monoid -/

/-- The stimulus monoid acts on states; since `drive` composes contravariantly, this is
a monoid homomorphism into the *opposite* of the endomorphism monoid of `S`. -/
def transitionHom (δ : S → I → S) : FreeMonoid I →* (Function.End S)ᵐᵒᵖ where
  toFun w := MulOpposite.op (drive δ (FreeMonoid.toList w))
  map_one' := by apply MulOpposite.unop_injective; funext s; rfl
  map_mul' w v := by
    apply MulOpposite.unop_injective
    funext s
    exact drive_append δ _ _ s



end Doppelganger


