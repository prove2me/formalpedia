-- Prove2me | Theorems.Thm_ThermoProof_imageCard_comp_le
-- name    : ThermoProof.imageCard_comp_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:39:24.627139+00:00
-- url     : https://prove2.me/theorems/ee6d620a-78f1-4d92-a592-afa973ccc787
-- title:
--   ImageCard comp le
-- statement:
--   Formal statement of `ThermoProof.imageCard_comp_le` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ThermoProof.imageCard_comp_le{α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
--       (f : α → β) (g : β → γ) : imageCard (g ∘ f) ≤ imageCard f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ThermodynamicsOfProof.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ThermodynamicsOfProof.lean#L140

-- Thm stub generated from Novelty/ThermodynamicsOfProof.lean
import Mathlib
import Definitions.Def_Novelty_ThermodynamicsOfProof

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

open ThermoProof

/-! ## Information erased by a proof step -/









/-! ## The Landauer cost -/





/-! ## Erasure accumulates along a proof (data-processing) -/

theorem ThermoProof.imageCard_comp_le{α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) : imageCard (g ∘ f) ≤ imageCard f := by sorry
