-- Prove2me | Theorems.Thm_TimeTravelContrarian_involutive_consistentCount_parity
-- name    : TimeTravelContrarian.involutive_consistentCount_parity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:39:45.643778+00:00
-- url     : https://prove2.me/theorems/74e8711b-7134-40a4-81ef-52099984c757
-- title:
--   Involutive consistentCount parity
-- statement:
--   Formal statement of `TimeTravelContrarian.involutive_consistentCount_parity` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TimeTravelContrarian.involutive_consistentCount_parity[Fintype X] [DecidableEq X] {f : X → X}
--       (hf : Involutive f) :
--       (CausalLoop.mk f).consistentCount ≡ Fintype.card X [MOD 2] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/TimeTravelContrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/TimeTravelContrarian.lean#L136

-- Thm stub generated from Novelty/TimeTravelContrarian.lean
import Mathlib
import Definitions.Def_Novelty_TimeTravelContrarian
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Time-Travel Logic, Contrarian Edition: which hypotheses *force* self-consistency?

This file continues the study of causal loops and the **Novikov self-consistency
principle** begun in `Catalog/.../TimeTravelCausalConsistency.lean`.  There a causal
loop's one-traversal net effect is modelled by a self-map `evolve : X → X`, and a loop
is **self-consistent** exactly when `evolve` has a fixed point.

The mission here is *contrarian*: we state a batch of bold conjectures of the form
"such-and-such structural hypothesis on the loop forces a consistent history", and for
each we either **prove** it or exhibit an explicit **counterexample** (a disproof).

The verdicts:

* `not_bijective_forces_selfConsistent` — **DISPROVED.**  Reversibility of the causal
  step (the loop map being a bijection) does *not* force self-consistency: the
  grandfather flip `¬·` on `Bool` is a bijection with no fixed point.
* `exists_sq_consistent_not_consistent` — **DISPROVED** ("consistency does not descend").
  A loop whose *double* traversal is self-consistent need not itself be self-consistent.
* `exists_selfConsistent_comp_not_selfConsistent` — **DISPROVED** ("consistency is not
  compositional").  Two self-consistent loops sharing a state space can compose to a
  fixed-point-free (paradoxical) loop; explicit witnesses on `Fin 3`.
* `selfConsistent_iterate` — **PROVED** ("consistency ascends").  A self-consistent
  loop stays self-consistent under every number of repetitions.
* `contracting_unique_selfConsistent` — **PROVED** ("deterministic time travel").  If
  the loop map is a contraction on a complete state space, the consistent history exists
  and is *unique* (Banach).
* `involutive_consistentCount_parity` — **PROVED** (quantitative Novikov).  For a
  reversible-by-symmetry (involutive) loop on a finite state space, the number of
  consistent histories has the same parity as the number of states.
* `involutive_odd_selfConsistent` — **PROVED** corollary: an involutive loop on an
  odd-sized state space is always self-consistent (with an *odd* number of histories).
* `exists_iterate_selfConsistent` — **PROVED** ("eventual consistency").  On a finite
  non-empty state space, some positive number of repetitions of *any* loop is
  self-consistent.
* `grandfather_consistentCount` / `identity_consistentCount` — concrete counts.
-/


open TimeTravelContrarian

open Function

variable {X : Type*}

/-! ## Core model -/





/-! ## Disproofs: hypotheses that do **not** force self-consistency -/




/-! ## Proofs: hypotheses that **do** force self-consistency -/



/-
**PROOF — quantitative Novikov for involutive loops.**  If the loop map is an
involution (traversing the loop twice restores the state) on a finite state space, then
the number of consistent histories has the *same parity* as the number of states.  This
refines the mere existence result below to an exact parity count.
-/

theorem TimeTravelContrarian.involutive_consistentCount_parity[Fintype X] [DecidableEq X] {f : X → X}
    (hf : Involutive f) :
    (CausalLoop.mk f).consistentCount ≡ Fintype.card X [MOD 2] := by sorry
