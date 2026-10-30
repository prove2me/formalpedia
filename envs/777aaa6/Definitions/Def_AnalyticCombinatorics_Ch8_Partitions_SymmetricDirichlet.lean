-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SymmetricDirichlet
-- name    : AnalyticCombinatorics_Ch8_Partitions_SymmetricDirichlet
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:03:40.825585+00:00
-- url     : https://prove2.me/theorems/86557437-721c-4417-8e0f-652551b8f063
-- title:
--   Symmetric Dirichlet
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/SymmetricDirichlet.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Row sum of a finite kernel. -/
def rowSum (K : ι → ι → ℝ) (x : ι) : ℝ := ∑ y, K x y

/-- Unnormalized directed jump energy `∑_{x,y} K x y (f y − f x)²`. -/
def jumpEnergy (K : ι → ι → ℝ) (f : ι → ℝ) : ℝ := ∑ x, ∑ y, K x y * (f y - f x) ^ 2

/-- Killing/defect term `∑_x (1 − rowSum K x) f x²` in `⟨(I−K)f,f⟩`. -/
def killEnergy (K : ι → ι → ℝ) (f : ι → ℝ) : ℝ := ∑ x, (1 - rowSum K x) * (f x) ^ 2

end AnalyticCombinatorics.Ch8.Partitions.Erdos


