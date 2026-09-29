-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
-- name    : ErdosProblems_Erdos269_KernelCarryRank
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:12:10.601883+00:00
-- url     : https://prove2.me/theorems/90611d88-bd04-4ba2-bd28-ad97c545fad7
-- title:
--   KernelCarryRank
-- statement:
--   Defines the floor-logarithm multiplicative carry, row and column factors for kernel factorization, and the reciprocal two-prime running-height kernel.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/KernelCarryRank.lean#L1-L596
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the rank phase transition of the running-LCM kernel

The running-LCM kernel `threePrimeKernelQ p q r i j k` is
`1 / (p ^ log_p N * q ^ log_q N * r ^ log_r N)` with `N = p^i q^j r^k`.

**Two generators.**  With only `p` and `q` the analogous kernel is an outer
product, so every matrix it forms has rank at most one
(`twoPrimeKernelQ_eq_outer_product`).

**Three generators.**  The only new ingredient is the single *binary* carry
`logCarry r (p^i) (q^j) ∈ {0,1}`.  That one bit is enough to destroy every
finite separation: for pairwise-independent generators and every `n`, there
are injective index families `I, J : Fin n → ℕ` whose `n × n` minor is
nonzero **simultaneously in every layer `k`**
(`exists_uniform_nonsingular_threePrimeKernel_minor`).  Hence each fixed-`k`
matrix has infinite rank over `ℚ`, and no finite sum
`∑_{ℓ<d} f_ℓ(i) · G_ℓ(j,k)` can represent the kernel
(`not_finite_separable_threePrimeKernel`).

Nothing here proves irrationality or transcendence of a three-prime value.
The missing producer is still an infinite residue-escape theorem; this module
sharpens the *structural* boundary that any such producer must respect.
-/

namespace ErdosProblems.Erdos269

open ErdosProblems.Shared

/-! ## The two-factor logarithmic carry -/

/-- The binary carry of `Nat.log` across a product. -/
def logCarry (b x y : ℕ) : ℕ :=
  Nat.log b (x * y) - Nat.log b x - Nat.log b y











/-! ## The real bridge: the carry is a two-dimensional rotation carry -/





/-! ## Independence of the two generators -/



/-! ## The kernel factorises through the carry -/













/-! ## Two generators: the kernel is an outer product -/







/-! ## Three generators: uniformly nonsingular minors of every order -/







end ErdosProblems.Erdos269

namespace ErdosProblems.Erdos269

/-! ## Exact `{2,3,5}` receipts

The layer `k = 0` of the `{2,3,5}` kernel begins

```
1        1/6      1/360     1/10800
1/2      1/60     1/720     1/21600
1/12     1/360    1/21600   1/129600
1/120    1/720    1/43200   1/1296000
```

The leading `2 x 2` and `3 x 3` minors are nonzero, but the leading `4 x 4`
minor **vanishes**.  So the rank theorem above is genuinely about the
existence of suitable index families, not about leading minors; the
vanishing `4 x 4` is the regression test against overstating it. -/

















































end ErdosProblems.Erdos269


