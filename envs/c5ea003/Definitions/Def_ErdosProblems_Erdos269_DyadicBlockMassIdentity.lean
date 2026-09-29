-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
-- name    : ErdosProblems_Erdos269_DyadicBlockMassIdentity
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:12:37.755646+00:00
-- url     : https://prove2.me/theorems/dff9edbc-7890-4a92-86ae-ce9c798a9466
-- title:
--   DyadicBlockMassIdentity
-- statement:
--   Defines dyadic 2·3·5 smooth shells, the odd height suffix at each shell point, and zero-, one-, and two-jump mass and digit formulas used to compare ordered internal jumps.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/DyadicBlockMassIdentity.lean#L1-L207
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: exact dyadic block-mass normalization

The integer checker compresses the smooth numbers in a half-open dyadic shell
`[2^a, 2^(a+1))`.  After clearing by the height at the right endpoint, every
summand contains the terminal dyadic factor `2`.  Dividing that common factor
leaves a suffix product of the zero, one, or two internal odd-prime jumps.

This file kernel-checks the complete cell algebra used by the checker.  The
remaining source-specific step is to identify the cell cardinalities with the
appropriate `strictSmoothShell` filters for every `a`.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- For the positive bases `2,3,5`, the redundant exponent box in
`strictSmoothExponents` imposes no extra condition: strict source membership is
exactly the value inequality. -/
theorem mem_strictSmoothExponents235_iff
    {x : ℕ} {e : ℕ × ℕ × ℕ} :
    e ∈ strictSmoothExponents 2 3 5 x ↔
      smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < x := by
  rcases e with ⟨i, j, k⟩
  constructor
  · intro he
    exact (Finset.mem_filter.mp he).2
  · intro hval
    have hpos : 0 < smooth3Val 2 3 5 i j k := by
      simp [smooth3Val]
    have hiDvd : 2 ^ i ∣ smooth3Val 2 3 5 i j k := by
      refine ⟨3 ^ j * 5 ^ k, ?_⟩
      simp [smooth3Val, mul_assoc]
    have hjDvd : 3 ^ j ∣ smooth3Val 2 3 5 i j k := by
      refine ⟨2 ^ i * 5 ^ k, ?_⟩
      simp [smooth3Val]
      ring
    have hkDvd : 5 ^ k ∣ smooth3Val 2 3 5 i j k := by
      refine ⟨2 ^ i * 3 ^ j, ?_⟩
      simp [smooth3Val]
      ring
    have hi : i < x :=
      (Nat.lt_pow_self (by norm_num : 1 < 2)).trans_le
        ((Nat.le_of_dvd hpos hiDvd).trans hval.le)
    have hj : j < x :=
      (Nat.lt_pow_self (by norm_num : 1 < 3)).trans_le
        ((Nat.le_of_dvd hpos hjDvd).trans hval.le)
    have hk : k < x :=
      (Nat.lt_pow_self (by norm_num : 1 < 5)).trans_le
        ((Nat.le_of_dvd hpos hkDvd).trans hval.le)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hi, Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hk⟩⟩, hval⟩

/-- The actual `{2,3,5}`-smooth exponent points in the half-open dyadic shell
`[2^a,2^(a+1))`. -/
def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))

theorem mem_dyadicSmoothShell235_iff
    {a : ℕ} {e : ℕ × ℕ × ℕ} :
    e ∈ dyadicSmoothShell235 a ↔
      2 ^ a ≤ smooth3Val 2 3 5 e.1 e.2.1 e.2.2 ∧
        smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < 2 ^ (a + 1) := by
  simp only [dyadicSmoothShell235, strictSmoothShell, Finset.mem_sdiff,
    mem_strictSmoothExponents235_iff]
  omega



/-- The odd suffix multiplier remaining between a shell point and the right
endpoint height. -/
def oddHeightSuffix235 (a : ℕ) (e : ℕ × ℕ × ℕ) : ℕ :=
  3 ^ (Nat.log 3 (2 ^ (a + 1)) -
      Nat.log 3 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2)) *
    5 ^ (Nat.log 5 (2 ^ (a + 1)) -
      Nat.log 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2))























end ErdosProblems.Erdos269


