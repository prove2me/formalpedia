-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exists_proofDSVDensityRationalPublicBucketPhysicalMixedPrefixCleanup_sq
-- name    : QuantumParallelRepetition.exists_proofDSVDensityRationalPublicBucketPhysicalMixedPrefixCleanup_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T08:09:04.763659+00:00
-- url     : https://prove2.me/theorems/f1a0247f-2dad-455f-957f-99c6617136df
-- title:
--   Bucket-indexed local unitaries clean up the common-rank prefix state, at the cost of the rank gap
-- statement:
--   Fix $N\ge 1$, a phase set $\Omega$, a label set $I$ with decidable equality, a bucketing $\mathrm{bk}:\Omega\times\{0,\dots,N\}\to I$ and a representative map $\mathrm{rep}:\Omega\times I\to\{0,\dots,N\}$, and let $\varepsilon>0$. For a rank $m$ write $|\Psi_m\rangle=\big(\sum_{k<m}|k\rangle|k\rangle\big)\otimes|\mu_n\rangle$ for the unnormalized rank-$m$ prefix tensored with the $n$-level embezzlement state, and $|\mu_{Nn}\rangle$ for the embezzlement state in dimension $Nn$. The claim is that there exist $n\ge 1$ and unitary families $A,B:\Omega\times I\to\mathrm U(Nn)$ such that for every phase $\omega$ and all ranks $r,s\in\{0,\dots,N\}$, $$\big\|\big(A_{\omega,\mathrm{bk}(\omega,r)}\otimes B_{\omega,\mathrm{bk}(\omega,s)}\big)|\Psi_{\min(r,s)}\rangle-\sqrt{r}\,|\mu_{Nn}\rangle\big\|^{2}\le 2|r-s|+2r\Big(2\varepsilon^{2}+\frac{8\,|r-\mathrm{rep}(\omega,\mathrm{bk}(\omega,r))|}{\max\big(1,\min(r,\mathrm{rep}(\omega,\mathrm{bk}(\omega,r)))\big)}+4\cdot\mathbf 1\{\mathrm{bk}(\omega,r)\ne\mathrm{bk}(\omega,s)\}\Big).$$ Crucially each side's unitary may depend only on its own bucket label, not on the other side's rank.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L43877-L43963

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem
    QuantumParallelRepetition.exists_proofDSVDensityRationalPublicBucketPhysicalMixedPrefixCleanup_sq
    {Ω I : Type*} [DecidableEq I] {N : ℕ} (grid : 0 < N)
    (bucket : Ω → Fin (N + 1) → I)
    (representative : Ω → I → Fin (N + 1))
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin (N + 1)),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVCanonicalFailurePrefix
                  (dSVDensityRationalPublicBucketPhysicalCommonRank
                    r s))) -
            Real.sqrt (r.val : ℝ) •
              embezzlementState (N * n)‖ ^ 2 ≤
            2 * |(r.val : ℝ) - (s.val : ℝ)| +
              2 * (r.val : ℝ) *
                (2 * ε ^ 2 +
                  8 * |(r.val : ℝ) -
                    ((representative phase (bucket phase r)).val : ℝ)| /
                    (max 1
                      (min r.val
                        (representative phase (bucket phase r)).val) : ℕ) +
                  4 * (if bucket phase r = bucket phase s
                    then (0 : ℝ) else 1)) := by sorry
