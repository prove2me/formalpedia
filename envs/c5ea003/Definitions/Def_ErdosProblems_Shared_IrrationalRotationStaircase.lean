-- Prove2me | Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
-- name    : ErdosProblems_Shared_IrrationalRotationStaircase
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:11:47.072234+00:00
-- url     : https://prove2.me/theorems/b0ec7ec9-12d6-4296-bd04-f42fe4498aa1
-- title:
--   IrrationalRotationStaircase
-- statement:
--   Defines a no-integer-return condition for a real rotation and finite staircase carry matrices. The staircase is a finite combinatorial pattern, not a claim about a particular prime pair.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Shared/IrrationalRotationStaircase.lean#L1-L390
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Irrational-rotation staircases and the carry-staircase determinant

Two independent pieces of reusable machinery.

* `ErdosProblems.Shared.exists_pos_nat_fract_mem_Ioo` : the **forward** orbit
  `n ↦ Int.fract (n * α)`, `n ≥ 1`, is dense in `[0,1]` as soon as no positive
  integer multiple of `α` is an integer.  The hypothesis is packaged as
  `NoIntegerOrbit`; for real `α` it is exactly irrationality, but it is often
  cheaper to verify directly.

* `ErdosProblems.Shared.det_carryStaircase` : the exact determinant
  `det (fun i j => if j ≤ i then t else 1) = t * (t - 1) ^ n`
  of the `(n+1)`-dimensional *carry staircase*.

Combined in `exists_staircase_indices`, they say that a pair of independent
rotations without integer returns realises an arbitrarily large staircase in
the two-dimensional carry `⌊fract (i * α) + fract (j * β)⌋`.  That is the
engine behind the three-prime running-LCM rank phase transition of Erdős #269.

Nothing here mentions a specific Erdős problem; the file is Mathlib-only.
-/

namespace ErdosProblems.Shared

open Set Matrix

/-! ## Forward orbits of a rotation without integer returns -/

/-- `NoIntegerOrbit α` : no positive integer multiple of `α` is an integer.
For real `α` this is equivalent to irrationality of `α`. -/
def NoIntegerOrbit (α : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → Int.fract ((n : ℝ) * α) ≠ 0









/-! ## The carry staircase and its determinant -/

variable {R : Type*} [CommRing R]









/-! ## Realising an arbitrary staircase from two independent rotations -/



end ErdosProblems.Shared


