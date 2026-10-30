-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_DirichletForm
-- name    : AnalyticCombinatorics_Ch8_Partitions_DirichletForm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:12:51.835906+00:00
-- url     : https://prove2.me/theorems/48e04606-c2ae-4191-ade2-84ef66abc7c7
-- title:
--   Dirichlet Form
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def intVerts (L : ℕ) : Finset ℤ := Finset.Icc (-(L : ℤ)) (L : ℤ)
--   ```
--
--   ```lean
--   def intEdges (L : ℕ) : Finset ℤ := Finset.Ico (-(L : ℤ)) (L : ℤ)
--   ```
--
--   ```lean
--   def edgeSq (f : ℤ → ℝ) (r : ℤ) : ℝ := (f (r + 1) - f r) ^ 2
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/DirichletForm.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Bounded-jump Dirichlet-form comparison (renewal route B, Layer-2 Stage 3c)

The kernel-side upper bound of the finite-interval Green/Harnack comparison (ChatGPT ac2 R11): for a
nonnegative bounded-jump kernel `Kc` on the integer interval `[-L,L]` with row mass `≤ 1`, the energy
form is dominated by the nearest-neighbor edge energy,

  `∑_{d,e} Kc(d,e)·(f e − f d)² ≤ B(2B+1)·∑_r (f(r+1) − f r)²   (≤ 3B²·… for B ≥ 1)`.

One factor `B` is the path Cauchy–Schwarz (the banked `sq_diff_le_path_energy_nat`); the `2B+1` is the
edge-charging count (`crossing_charge_le`: only starts within `B` of an edge can cross it, each with
row mass `≤ 1`).  No symmetry needed.  This is the `E_K ≤ Λ·E_edge` half of the form sandwich feeding
`GreenForm.green_domination_of_form_le`.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Vertex interval `[-L,L] ⊂ ℤ`. -/
def intVerts (L : ℕ) : Finset ℤ := Finset.Icc (-(L : ℤ)) (L : ℤ)

/-- Edge interval `[-L,L) ⊂ ℤ`; edge `r` means `(r,r+1)`. -/
def intEdges (L : ℕ) : Finset ℤ := Finset.Ico (-(L : ℤ)) (L : ℤ)

/-- Nearest-neighbor edge energy. -/
def edgeSq (f : ℤ → ℝ) (r : ℤ) : ℝ := (f (r + 1) - f r) ^ 2

end AnalyticCombinatorics.Ch8.Partitions.Erdos


