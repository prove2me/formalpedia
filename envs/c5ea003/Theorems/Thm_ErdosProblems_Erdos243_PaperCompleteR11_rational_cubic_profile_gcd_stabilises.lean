-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_cubic_profile_gcd_stabilises
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_profile_gcd_stabilises
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:26:10.604421+00:00
-- url     : https://prove2.me/theorems/25f5493c-1d9f-468d-ab13-16977b157b46
-- title:
--   Lean source theorem: rational_cubic_profile_gcd_stabilises
-- statement:
--   For a nonzero-leading rational cubic profile and a natural recurrence with positive C, if disagreements with the profile have no lower-density bound of 1/4, the gcd of C(n),D(n) is uniformly bounded at all indices and constant on some tail.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicGcdFence.lean#L140-L159
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# A uniform four-window gcd reduction for cubic profiles

The reduction works below density `1/4`, not only
under density zero. Four agreeing values give the exact third difference;
every earlier common divisor divides that difference. No upper growth estimate,
record restart, denominator reduction, or prime-existence hypothesis is needed.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_profile_gcd_stabilises
    (a C D : ℕ → ℕ) (κ η : ℚ) (hκ : κ ≠ 0)
    (hpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hlow : ¬ LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
      (1 / 4)) :
    ∃ B N : ℕ, (∀ n, Nat.gcd (C n) (D n) ≤ B) ∧
      ∀ n, N ≤ n → Nat.gcd (C n) (D n) = Nat.gcd (C N) (D N) := by sorry
