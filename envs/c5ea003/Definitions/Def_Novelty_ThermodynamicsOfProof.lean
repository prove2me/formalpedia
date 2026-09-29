-- Prove2me | Definitions.Def_Novelty_ThermodynamicsOfProof
-- name    : Novelty_ThermodynamicsOfProof
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:43:41.216503+00:00
-- url     : https://prove2.me/theorems/c006b838-73e7-4938-b414-75bbf7a0dbc7
-- title:
--   Aether Catalog definitions — Novelty_ThermodynamicsOfProof
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ThermodynamicsOfProof`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ThermodynamicsOfProof.lean by skeleton subtraction
import Mathlib

/-!
# Thermodynamics of Mathematical Proof

A **Landauer-like principle for mathematical reasoning**.

We model a single *proof step* (a rewrite, a case merge, a lookup, a verification) as a
function `f : α → β` between finite state spaces.  Physically, a computation that is
*logically irreversible* — one that maps several distinct inputs to the same output —
must dump the lost distinctions into the environment.  Landauer's principle states that
erasing one bit of information costs at least `k_B · T · ln 2` of dissipated entropy.

The information erased by the step `f` is the drop in Shannon capacity of the register:

  `erasedBits f = log₂ (card α) − log₂ (image size of f)`.

## Main results

* `erasedBits_nonneg` — a proof step never *un*-erases information.
* `erasedBits_eq_zero_iff_injective` — **reversibility criterion**: a step erases zero bits
  iff it is injective (logically reversible).
* `landauerCost_pos_of_not_injective` — **Landauer's principle**: an irreversible step costs
  strictly positive entropy at positive temperature.
* `erasedBits_lower_bound` — the erasure of any step into a `card β`-state register is at
  least `log₂(card α) − log₂(card β)`.
* `erasedBits_mono_comp` — **erasure is monotone along a proof pipeline**: composing steps
  can only accumulate erasure, never undo it (a data-processing inequality).
* `erasedBits_bennett` — **Bennett's reversible embedding**: *retaining the input* makes any
  step reversible (erases zero bits), so erasure is not forced by computation per se.
* `erasedBits_collapse` / `erasedBits_bigCollapse` — explicit families realising *linear*
  and *exponential* erasure in a size parameter.
* `exponential_erasure_separation` — there are theorems (state collapses) whose verification
  erases unboundedly (indeed exponentially) many bits.
* `incompressible` — a Kolmogorov counting bound: the `2ⁿ` Boolean predicates on `n` bits
  cannot be injectively coded by the `2ⁿ − 1` programs of length `< n`, so some predicate has
  no proof/description shorter than `n` bits — its verification erases `≥ n · k_B T ln 2`.
-/

open Finset Real

namespace ThermoProof

/-! ## Information erased by a proof step -/

/-- The number of distinct outputs of `f` (the size of its image). -/
def imageCard {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) : ℕ :=
  (Finset.univ.image f).card





/-- Bits of information erased by one step `f`: the entropy drop between input and output. -/
noncomputable def erasedBits {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) : ℝ :=
  Real.logb 2 (Fintype.card α) - Real.logb 2 (imageCard f)



/-! ## The Landauer cost -/

/-- **Landauer cost.** Erasing `bits` of information into an environment at temperature `T`
(with Boltzmann constant `kB`) dissipates `bits · kB · T · ln 2` of entropy/heat. -/
noncomputable def landauerCost (bits kB T : ℝ) : ℝ := bits * (kB * T * Real.log 2)




/-! ## Erasure accumulates along a proof (data-processing) -/



/-! ## Bennett's reversible embedding: erasure is avoidable -/

/-- **Bennett's reversible embedding** of a step `f`: keep the input alongside the output,
`x ↦ (x, f x)`. -/
def bennettEmbedding {α β : Type*} (f : α → β) : α → α × β := fun x => (x, f x)



/-! ## Explicit erasure families and the exponential separation -/



/-- Collapsing `2ⁿ` states onto a single answer (a decision procedure) erases exactly `n`
bits. -/
noncomputable def collapse (n : ℕ) : Fin (2^n) → Fin 1 := fun _ => 0


/-- A doubly-exponential state space collapsed to one answer: erases `2ᵐ` bits. -/
noncomputable def bigCollapse (m : ℕ) : Fin (2^(2^m)) → Fin 1 := fun _ => 0






/-! ## Kolmogorov incompressibility and the cost of verification -/


end ThermoProof


