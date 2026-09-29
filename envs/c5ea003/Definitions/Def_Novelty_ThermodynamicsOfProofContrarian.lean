-- Prove2me | Definitions.Def_Novelty_ThermodynamicsOfProofContrarian
-- name    : Novelty_ThermodynamicsOfProofContrarian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:43:38.264139+00:00
-- url     : https://prove2.me/theorems/483c3f53-0fe9-4867-998c-5b47effd39e1
-- title:
--   Aether Catalog definitions — Novelty_ThermodynamicsOfProofContrarian
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ThermodynamicsOfProofContrarian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ThermodynamicsOfProofContrarian.lean by skeleton subtraction
import Mathlib

/-!
# Thermodynamics of Mathematical Proof — Contrarian Conjectures

This companion file (fully self-contained) tests several **bold conjectures** about the
information-erasure cost of proof steps.  For each we either prove it or refute it with an
explicit counterexample.  Disproofs are first-class results here.

We reuse the same model as `ThermodynamicsOfProof`: a proof step is a function `f : α → β`
between finite state spaces, and

  `erasedBits f = log₂ (card α) − log₂ (image size of f)`.

## Conjectures adjudicated

* **Refuted** — *"Every non-identity proof step erases information."*
  (`exists_reversible_nontrivial_step`): the NOT gate is a non-identity bijection that erases
  zero bits.  Logical *irreversibility*, not activity, is what costs entropy.

* **Confirmed (textbook Landauer)** — *"The AND gate erases exactly one bit."*
  (`erasedBits_andGate`): `∧ : Bool² → Bool` is `3`-to-`1` on `false`, collapsing `4` states
  to `2`, so it erases `log₂ 4 − log₂ 2 = 1` bit — the canonical `kT ln 2` dissipation.

* **Refuted** — *"Erasure is additive under composition."*
  (`erasedBits_not_additive`): two constant steps on `Fin 2` compose to a step erasing `1`
  bit, not `1 + 1 = 2`.  Erasure is *sub*-additive (indeed idempotent here), not additive.

* **Confirmed** — *"Every bijection (reversible step) erases zero bits."*
  (`erasedBits_bijective_zero`).
-/

open Finset Real

namespace ThermoProofContrarian

/-! ## Minimal self-contained model -/

/-- The number of distinct outputs of `f`. -/
def imageCard {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) : ℕ :=
  (Finset.univ.image f).card



/-- Bits of information erased by one step `f`. -/
noncomputable def erasedBits {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) : ℝ :=
  Real.logb 2 (Fintype.card α) - Real.logb 2 (imageCard f)


/-! ## Confirmed: reversible steps are free -/


/-! ## Refuted: not every non-identity step erases -/


/-! ## Confirmed: the AND gate is the textbook Landauer erasure -/

/-- The Boolean AND gate as a proof/computation step `Bool² → Bool`. -/
noncomputable def andGate : Bool × Bool → Bool := fun p => p.1 && p.2


/-! ## Refuted: erasure is not additive under composition -/


end ThermoProofContrarian


