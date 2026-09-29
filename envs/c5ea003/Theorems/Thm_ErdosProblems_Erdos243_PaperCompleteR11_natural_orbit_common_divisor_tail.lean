-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_natural_orbit_common_divisor_tail
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.natural_orbit_common_divisor_tail
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:33.83115+00:00
-- url     : https://prove2.me/theorems/b4dab82c-8ae2-4c38-8265-a46623005a1d
-- title:
--   Lean source theorem: natural_orbit_common_divisor_tail
-- statement:
--   If natural sequences obey C(n+1)+D(n)=a(n)C(n) and D(n+1)=a(n)D(n), then any natural d dividing both C(s) and D(s) divides both coordinates at every later state s+k.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicGcdFence.lean#L61-L78
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.natural_orbit_common_divisor_tail (a C D : ℕ → ℕ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (s d : ℕ) (hdC : d ∣ C s) (hdD : d ∣ D s) :
    ∀ k : ℕ, d ∣ C (s + k) ∧ d ∣ D (s + k) := by sorry
