-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_profile_gcd_stabilises
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:30:12.723716+00:00
-- url     : https://prove2.me/submissions/409b49e6-9216-4a68-a1fe-6083ad6d3149

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_gcd_bound_of_not_quarter_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_gcd_stabilises_of_not_quarter_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_profile_integer_clearing
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

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a C D : ℕ → ℕ) (κ η : ℚ) (hκ : κ ≠ 0)
    (hpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hlow : ¬ LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
      (1 / 4)) :
    ∃ B N : ℕ, (∀ n, Nat.gcd (C n) (D n) ≤ B) ∧
      ∀ n, N ≤ n → Nat.gcd (C n) (D n) = Nat.gcd (C N) (D N) := by
  obtain ⟨q, A, B, _hq, hclear, hA⟩ := cubic_profile_integer_clearing κ η
  let P : ℕ → ℚ := fun n ↦ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η
  have hbound := cubic_gcd_bound_of_not_quarter_density a C D P q A B (hA hκ)
    hC hD hclear hlow
  obtain ⟨N, hN⟩ := cubic_gcd_stabilises_of_not_quarter_density a C D P q A B
    (hA hκ) hpos hC hD hclear hlow
  exact ⟨(6 * A).natAbs, N, hbound, hN⟩
