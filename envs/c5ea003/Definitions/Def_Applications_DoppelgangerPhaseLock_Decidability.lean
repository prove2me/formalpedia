-- Prove2me | Definitions.Def_Applications_DoppelgangerPhaseLock_Decidability
-- name    : Applications_DoppelgangerPhaseLock_Decidability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-15T00:47:29.141629+00:00
-- url     : https://prove2.me/theorems/53837fe3-f6b8-4e8c-a659-33e5dae9b548
-- title:
--   Aether Catalog definitions — Applications_DoppelgangerPhaseLock_Decidability
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DoppelgangerPhaseLock.Decidability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DoppelgangerPhaseLock/Decidability.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Boundary
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
import Theorems.Thm_Doppelganger_exists_lock_length_le_of_phaseLocking
/-
# Doppelgänger Phase-Lock — decidability and extremal experiments

Third research cycle.  The finite synchronization theorem is *effective*: because a
phase-locking agent must lock within `(|S| - 1)·|S|²` stimuli
(`Doppelganger.exists_lock_length_le_of_phaseLocking`), the search for a locking word can
be confined to a finite set.  This yields a genuine `Decidable` instance: *whether two
identical agents can be telepathically synchronized is an algorithmically decidable
property of the agent design*.

We then run the decision procedure as an experiment on the three-state Černý agent, and
prove — by exhaustive certified search — that its minimal phase-lock time is exactly
`4 = (3-1)²`, the Černý extremal value.  This is a genuine (kernel-checked, no
`native_decide`) computation, not a definitional triviality.

## Main results

* `Doppelganger.phaseLocking_iff_exists_bounded` — reduction to a finite search.
* `Doppelganger.decidablePhaseLocking` — decidability of doppelgänger telepathy.
* `Doppelganger.cerny3_lock_time_eq_four` — the Černý agent locks in exactly four shared
  stimuli, and in no fewer.
-/

namespace Doppelganger

/-- Locking is a decidable property of a finite agent and a finite stimulus word. -/
instance decidableLocks {S I : Type*} [Fintype S] [DecidableEq S] (δ : S → I → S) (w : List I) :
    Decidable (Locks δ w) := by unfold Locks; infer_instance

section Decide

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- **Reduction to a finite search.**  Thanks to the cubic bound on the phase-lock time,
telepathy of an agent design is witnessed, if at all, by a word of bounded length. -/
theorem phaseLocking_iff_exists_bounded [Nonempty S] (δ : S → I → S) :
    PhaseLocking δ ↔ ∃ m < (Fintype.card S - 1) * (Fintype.card S * Fintype.card S) + 1,
      ∃ f : Fin m → I, Locks δ (List.ofFn f) := by
  constructor
  · intro h
    obtain ⟨w, hlen, hw⟩ := exists_lock_length_le_of_phaseLocking δ h
    exact ⟨w.length, by omega, fun i => w[i], by simpa using hw⟩
  · rintro ⟨m, _, f, hf⟩
    exact ⟨List.ofFn f, hf⟩

/-- **Telepathy is decidable.**  For finite state spaces and finite stimulus alphabets,
whether two separated copies of the agent can be phase-locked is decidable. -/
instance decidablePhaseLocking [Nonempty S] (δ : S → I → S) : Decidable (PhaseLocking δ) :=
  decidable_of_iff _ (phaseLocking_iff_exists_bounded δ).symm

end Decide

/-! ### Running the decision procedure -/



/-- The three-state Černý agent: stimulus `0` rotates the internal state, stimulus `1`
collapses state `0` onto state `1` and fixes the rest. -/
def cerny3 : Fin 3 → Fin 2 → Fin 3 :=
  fun s i => if i = 0 then s + 1 else (if s = 0 then 1 else s)





/-- The four-state Černý agent. -/
def cerny4 : Fin 4 → Fin 2 → Fin 4 :=
  fun s i => if i = 0 then s + 1 else (if s = 0 then 1 else s)




end Doppelganger


