-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_greenQ_eq_half_jumpEnergy_add_killEnergy
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.greenQ_eq_half_jumpEnergy_add_killEnergy
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:07:05.039739+00:00
-- url     : https://prove2.me/theorems/1e229834-8fa8-4bd9-972f-443c8d7d6340
-- title:
--   The symmetric killed-kernel energy decomposition
-- statement:
--   Finite symmetric-kernel form identity and nonnegativity corollary; the source partition residual kernel is not thereby proved symmetric.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem greenQ_eq_half_jumpEnergy_add_killEnergy
--       (K : ι → ι → ℝ) (f : ι → ℝ) (hKsym : ∀ x y, K x y = K y x) :
--       greenQ K f = (1 / 2) * jumpEnergy K f + killEnergy K f
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/SymmetricDirichlet.lean#L110. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_GreenForm
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SymmetricDirichlet
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Dirichlet-form representation of `greenQ` (renewal route B, Layer-2 Stage 3b/3c bridge)

The identity linking the `GreenForm` quadratic form `greenQ K f = ⟨(I−K)f, f⟩` to the directed jump
energy and killing defect (ChatGPT ac2 R12), for a **symmetric** kernel:

  `greenQ K f = ½·jumpEnergy K f + killEnergy K f`,
  `jumpEnergy K f = ∑_{x,y} K x y (f y − f x)²`,  `killEnergy K f = ∑_x (1 − rowSum K x)·f x²`.

This is the crux connecting `DirichletForm.bounded_jump_energy_le_edge_energy` (which bounds
`jumpEnergy`) to `GreenForm.green_domination_of_form_le` (which consumes `greenQ`).  Corollary
`greenQ_nonneg_of_symm_substochastic` discharges GreenForm's `hQnonneg` hypothesis for any symmetric
substochastic kernel.  (The `−Λ·E_edge` ellipticity lower half lives separately; see DOCTRINE R12/R13.)
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.greenQ_eq_half_jumpEnergy_add_killEnergy
    (K : ι → ι → ℝ) (f : ι → ℝ) (hKsym : ∀ x y, K x y = K y x) :
    greenQ K f = (1 / 2) * jumpEnergy K f + killEnergy K f := by sorry
