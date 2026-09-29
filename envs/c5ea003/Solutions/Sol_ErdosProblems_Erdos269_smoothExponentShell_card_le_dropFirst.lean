-- Prove2me | solution 1 for ErdosProblems.Erdos269.smoothExponentShell_card_le_dropFirst
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:00:47.882177+00:00
-- url     : https://prove2.me/submissions/3e4a5e14-4d41-40e0-b480-88d82e1b0ba2

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Theorems.Thm_ErdosProblems_Erdos269_exponent_unique_in_short_interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the three-prime running-LCM coordinate

This module starts the problem-owned formalization of the first unresolved
three-prime case.  It records the exact computational height used by the
running-LCM representation, its cubic majorant, the smallest non-separation
fixture for `{2,3,5}`, the variable-base tail-state update, and the uniform
quadratic bound for actual filtered smooth-number shells.

No declaration here asserts irrationality or transcendence of a three-prime
value.  The missing producer is still an infinite residue-escape or genuinely
higher-dimensional analytic theorem.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators































/-! ## Finite pure-power jump enumeration -/

















/-! ## Single-coordinate jump ratios -/













/-! ## Finite jump grouping -/













/-! The first exact `{2,3,5}` kernel values. -/















/-! ## Exact short-shell multiplicity bounds -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p q r lo hi hp hq hr : ℕ}
    (hpPos : 0 < p) (hwidth : hi ≤ p * lo) :
    (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (hq + 1) * (hr + 1) := by
  classical
  let target := (Finset.range (hq + 1)).product (Finset.range (hr + 1))
  have hcard :
      (smoothExponentShell p q r lo hi hp hq hr).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn (fun e : ℕ × ℕ × ℕ => e.2) ?_ ?_
    · intro e he
      change e ∈ smoothExponentShell p q r lo hi hp hq hr at he
      change e.2 ∈ target
      rcases e with ⟨a, b, c⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he
      have houter := Finset.mem_product.mp he.1
      have hinner := Finset.mem_product.mp houter.2
      exact Finset.mem_product.mpr
        ⟨hinner.1, hinner.2⟩
    · intro e₁ he₁ e₂ he₂ hproj
      change e₁ ∈ smoothExponentShell p q r lo hi hp hq hr at he₁
      change e₂ ∈ smoothExponentShell p q r lo hi hp hq hr at he₂
      rcases e₁ with ⟨a₁, b₁, c₁⟩
      rcases e₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he₁ he₂
      have ha₁Lo : lo ≤ p ^ a₁ * (q ^ b₁ * r ^ c₁) := by
        simpa [smooth3Val, mul_assoc] using he₁.2.1
      have ha₁Hi : p ^ a₁ * (q ^ b₁ * r ^ c₁) < hi := by
        simpa [smooth3Val, mul_assoc] using he₁.2.2
      have ha₂Lo : lo ≤ p ^ a₂ * (q ^ b₁ * r ^ c₁) := by
        simpa [smooth3Val, mul_assoc] using he₂.2.1
      have ha₂Hi : p ^ a₂ * (q ^ b₁ * r ^ c₁) < hi := by
        simpa [smooth3Val, mul_assoc] using he₂.2.2
      have ha : a₁ = a₂ := exponent_unique_in_short_interval hpPos hwidth
        ha₁Lo ha₁Hi ha₂Lo ha₂Hi
      simp [ha]
  simpa [target] using hcard
