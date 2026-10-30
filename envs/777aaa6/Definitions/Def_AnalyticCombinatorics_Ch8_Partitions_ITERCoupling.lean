-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
-- name    : AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:37:20.93976+00:00
-- url     : https://prove2.me/theorems/0cdae64a-9f2a-4cb2-a217-1b27759d3f86
-- title:
--   I T E R Coupling
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def Mpow (P : α → α → ℝ) : ℕ → α → α → ℝ
--     | 0 => fun x y => if x = y then 1 else 0
--     | t + 1 => fun x y => ∑ z, Mpow P t x z * P z y
--   ```
--
--   ```lean
--   def GoodW (x y : α) : Prop := (Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) ≤ W
--   ```
--
--   ```lean
--   def cmass (x y : α) : ℝ := ∑ z, Cpart P rnk W x y z
--   ```
--
--   ```lean
--   def umass (t : ℕ) : ℝ := ∑ x, ∑ y, Umat P rnk W i j t x y
--   ```
--
--   ```lean
--   def Cpart (x y z : α) : ℝ := if GoodW rnk W x y then min (P x z) (P y z) else 0
--   ```
--
--   ```lean
--   def Umat : ℕ → α → α → ℝ
--     | 0 => fun a b => if a = i ∧ b = j then 1 else 0
--     | t + 1 => fun a b => ∑ x, ∑ y, Umat t x y * Kres P rnk W x y a b
--   ```
--
--   ```lean
--   def Kres (x y a b : α) : ℝ :=
--     if cmass P rnk W x y < 1 then Lres P rnk W x y a * Rres P rnk W x y b / (1 - cmass P rnk W x y)
--     else 0
--   ```
--
--   ```lean
--   def Lres (x y z : α) : ℝ := P x z - Cpart P rnk W x y z
--   def Rres (x y z : α) : ℝ := P y z - Cpart P rnk W x y z
--   ```
--
--   ```lean
--   def Rres (x y z : α) : ℝ := P y z - Cpart P rnk W x y z
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ITERCoupling.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Fact B via Doeblin: the deterministic windowed-coupling ITER (finite-sum algebra)

The renewal-alignment overlap bound, built WITHOUT any probabilistic coupling library — purely as
finite-sum recursion over a finite state type `α` with a stochastic kernel `P`.  We track the coalesced
common-minorant mass `ρ_t` and the unmatched pair mass `U_t`; the marginal invariant
`ρ_t z + ∑_y U_t z y = Pⁿ i z` makes `ρ_t` a common minorant of the two `t`-step laws, so
`∑ ρ_t ≤ overlap`.  The unmatched mass contracts: `u_{t+1} ≤ (1−δ) u_t + δ b_t` with `b_t` the unmatched
mass outside the rank window.  Hence

  `overlap(Pᵐ i ·, Pᵐ j ·) ≥ 1 − (1−δ)^m − δ·∑_{t<m} (1−δ)^{m−t−1} b_t`.

The lone analytic input left is the bad-mass bound `b_t ≤ e_t`.  Opus-authored (construction ChatGPT R3).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `t`-step law (right matrix power applied to the point mass at the start). -/
def Mpow (P : α → α → ℝ) : ℕ → α → α → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | t + 1 => fun x y => ∑ z, Mpow P t x z * P z y

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- Two states are in the rank window. -/
def GoodW (x y : α) : Prop := (Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) ≤ W

instance (x y : α) : Decidable (GoodW rnk W x y) := by unfold GoodW; infer_instance

/-- The common part of two rows on the window. -/
def Cpart (x y z : α) : ℝ := if GoodW rnk W x y then min (P x z) (P y z) else 0

/-- Total common mass at a pair. -/
def cmass (x y : α) : ℝ := ∑ z, Cpart P rnk W x y z

/-- Left/right residual rows. -/
def Lres (x y z : α) : ℝ := P x z - Cpart P rnk W x y z
def Rres (x y z : α) : ℝ := P y z - Cpart P rnk W x y z

/-- Residual product coupling kernel. -/
def Kres (x y a b : α) : ℝ :=
  if cmass P rnk W x y < 1 then Lres P rnk W x y a * Rres P rnk W x y b / (1 - cmass P rnk W x y)
  else 0

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

variable (i j : α)

/-- Unmatched pair mass after `t` steps (initialised at the pair `(i,j)`). -/
def Umat : ℕ → α → α → ℝ
  | 0 => fun a b => if a = i ∧ b = j then 1 else 0
  | t + 1 => fun a b => ∑ x, ∑ y, Umat t x y * Kres P rnk W x y a b

/-- Total unmatched mass after `t` steps. -/
def umass (t : ℕ) : ℝ := ∑ x, ∑ y, Umat P rnk W i j t x y

end AnalyticCombinatorics.Ch8.Partitions.Erdos


