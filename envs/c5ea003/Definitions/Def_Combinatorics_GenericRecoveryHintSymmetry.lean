-- Prove2me | Definitions.Def_Combinatorics_GenericRecoveryHintSymmetry
-- name    : Combinatorics_GenericRecoveryHintSymmetry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:43:57.655+00:00
-- url     : https://prove2.me/theorems/30edf2e2-a594-4fba-972b-16c101b738a4
-- title:
--   Aether Catalog definitions — Combinatorics_GenericRecoveryHintSymmetry
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.GenericRecoveryHintSymmetry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/GenericRecoveryHintSymmetry.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_GenericRecoveryHintTaxonomy
/-
# GENERIC-RECOVERY, cycle III: every hint deficit is a symmetry

Cycles I and II established that a `t`-bit hint reduces the search by exactly
`2^t`, that the bound is attained, and that two special families — value hints
and trace hints — fall short by one and by three bits respectively.  Cycle III
asks *why* a family falls short, and answers: **because the hint is invariant
under a group of candidate symmetries, and the deficit is the order of that
group.**

* `GenericRecovery.cost_ge_of_family` — the abstract mechanism: an injective
  family of candidates carrying the same hint reading forces a class at least
  that large.
* `GenericRecovery.card_image_mul_le`, `GenericRecovery.worstCost_ge_of_uniform`
  — if such a family exists at *every* candidate, the number of usable readings
  drops by the factor `g`: `g · #readings ≤ |S|`, i.e. `log₂ g` bits are lost
  from the hint's nominal budget.
* `GenericRecovery.kleinMul`, `GenericRecovery.card_kleinMul`,
  `GenericRecovery.kleinMul_sq_eq_one` — the invariance group of the trace hint:
  the Klein four-group `{±1, ±(1 + 2^{t-1})}` of square roots of `1` mod `2^t`.
* `GenericRecovery.cost_sqHint_ge_four`, `GenericRecovery.card_image_sqHint_le`
  — the payoff: on *any* candidate set of units closed under that group, the
  square (equivalently trace) hint has classes of size at least `4` and at most
  `|S|/4` readings.  Cycle II computed `4` on the full odd-residue set; here the
  same deficit is derived from structure and holds on every symmetric candidate
  set, e.g. the sparse prime sets of the experiment.
-/

namespace GenericRecovery

open Finset

/-! ## 1.  The abstract mechanism -/

variable {α β ι : Type*} [DecidableEq β]




/-! ## 2.  The invariance group of the trace hint -/

section Klein

variable (n : ℕ)

/-- The Klein four-group of square roots of `1` modulo `2^{n+3}`. -/
def kleinMul : Finset (ZMod (2 ^ (n + 3))) :=
  {((1 : ℤ) : ZMod (2 ^ (n + 3))), ((-1 : ℤ) : ZMod (2 ^ (n + 3))),
    ((1 + 2 ^ (n + 2) : ℤ) : ZMod (2 ^ (n + 3))),
    ((-(1 + 2 ^ (n + 2)) : ℤ) : ZMod (2 ^ (n + 3)))}









end Klein

end GenericRecovery


