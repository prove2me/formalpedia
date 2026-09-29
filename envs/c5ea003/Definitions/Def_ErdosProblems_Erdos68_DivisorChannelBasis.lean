-- Prove2me | Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
-- name    : ErdosProblems_Erdos68_DivisorChannelBasis
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T15:44:52.027223+00:00
-- url     : https://prove2.me/theorems/357391ee-1105-44d8-a243-2572ce63d1c1
-- title:
--   Adjacent differences and isolated channel units
-- statement:
--   Defines the adjacent-difference vector, the finite lcm of factorial gaps, and recursively isolated channel units. Their support, moment, and channel identities are separate theorem nodes.
-- source:
--   Pinned Lean definition adjacentDifference: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/DivisorChannelBasis.lean#L116-L117
--   Pinned Lean definition channelLCM: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/DivisorChannelBasis.lean#L431-L432
--   Pinned Lean definition isolatedChannelUnit: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/DivisorChannelBasis.lean#L527-L535
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# Divisor-coordinate channel basis for Erdős problem 68

The adjacent difference `T_n = n e_{n-1} - e_n` hits exactly the divisor
channels of index `n`.  Subtracting proper-divisor copies produces an
integral family `U_n` with a single nonzero channel.  On the manuscript
support `n ≥ 2`, the second channel forces an extra factor of `12` in the
moment, so annihilating channels through `D` yields `12 L_D ∣ M`.

No declaration here constructs a cofinal nonintegrality family or decides
rationality of the factorial-gap series.
-/

namespace ErdosProblems.Erdos68

open Finsupp

/-! ## Linearity of the Finsupp channel presentation -/





























/-! ## Adjacent differences `T_n` -/

/-- Adjacent difference `T_n = n e_{n-1} - e_n`. -/
noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1















/-! ## Support-sensitive factor of `12` -/

















/-! ## Channel moduli and `12 L_D` -/







/-- Least common multiple of the channel moduli through `D`. -/
def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)













/-! ## Isolated channel units `U_n` -/

/-- Isolated one-channel basis vector, `U_n = T_n - ∑_{d | n, 2 ≤ d < n} W_{d,n} U_d`. -/
noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0































end ErdosProblems.Erdos68


