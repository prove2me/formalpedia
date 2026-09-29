-- Prove2me | Theorems.Thm_LatticeEnumerator_dilCount_unitInterval
-- name    : LatticeEnumerator.dilCount_unitInterval
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:52:30.301153+00:00
-- url     : https://prove2.me/theorems/9d4f24b7-a53f-4dff-8c09-4f4694207d24
-- title:
--   One-dimensional evaluation.
-- statement:
--   **One-dimensional evaluation.**  The half-open unit interval has enumerator `⌈t⌉`.
--
--   ```lean
--   theorem LatticeEnumerator.dilCount_unitInterval{t : ℝ} (ht : 0 < t) :
--       dilCount (Set.univ.pi fun _ : Fin 1 => Set.Ico (0 : ℝ) 1) t = ⌈t⌉₊ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LatticePointExamples.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LatticePointExamples.lean#L29

-- Thm stub generated from Cryptography/LatticePointExamples.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness

/-!
# Worked examples and computational sanity checks

Concrete evaluations of the lattice-point enumerator, used as machine-checked evidence that the
definitions in `Cryptography.LatticePointEnumerator` behave as intended.

## Main results

* `LatticeEnumerator.dilCount_unitInterval` : in dimension one, `L_{[0,1)}(t) = ⌈t⌉` for every
  `t > 0`; in particular `L(t)/t → 1 = vol([0,1))`, in agreement with the Gauss–Weyl theorem.
* `LatticeEnumerator.dilCount_unitInterval_examples` : numerical instances.
* `LatticeEnumerator.dilCount_empty`, `LatticeEnumerator.shiftCount_empty` : degenerate cases.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

open LatticeEnumerator

theorem LatticeEnumerator.dilCount_unitInterval{t : ℝ} (ht : 0 < t) :
    dilCount (Set.univ.pi fun _ : Fin 1 => Set.Ico (0 : ℝ) 1) t = ⌈t⌉₊ := by sorry
