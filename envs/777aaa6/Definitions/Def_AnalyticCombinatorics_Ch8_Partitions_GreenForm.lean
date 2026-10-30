-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_GreenForm
-- name    : AnalyticCombinatorics_Ch8_Partitions_GreenForm
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:02:40.94554+00:00
-- url     : https://prove2.me/theorems/9e23e399-fb93-4274-961e-206eab2bfcc7
-- title:
--   Green Form
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/GreenForm.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Variational Green-from-form comparison (renewal route B, Layer-2 Stage 3b)

The finite-dimensional, measure-theory-free heart of the Dirichlet-form Green comparison
(ChatGPT ac2 R10).  For a finite type `ι`, kernel operator `A_K = I − K`, energy form
`Q_K(f) = ⟨A_K f, f⟩`, and a Green operator `G` supplied via the resolvent hypothesis
`A_K (G h) = h`:

* `green_complete_square` — the crux identity `2⟨h,f⟩ − Q_K(f) = ⟨h,u⟩ − Q_K(f−u)` when `A_K u = h`
  (needs `A_K` self-adjoint, i.e. `K` symmetric);
* `green_form_duality_isGreatest` — `⟨h, G h⟩` is the greatest value of `f ↦ 2⟨h,f⟩ − Q_K(f)`
  (`sSup`-free, via `IsGreatest`);
* `green_domination_of_form_le` — **form domination ⟹ Green domination**:
  `Q_K(f) ≤ Λ·Q_R(f)` (∀f) ⟹ `⟨h, G_K h⟩ ≥ Λ⁻¹·⟨h, G_R h⟩`.

The Green operator's existence (Neumann convergence) is kept *separate*: these lemmas only consume the
resolvent identity `hG : ∀ h x, greenA K (G h) x = h x`, so they are pure finite-dim linear algebra.
(The nonreversible/sector generalization — `quadratic_green_compare_sector`, core `2AB−A²≤B²` — and the
cut-flux Hardy SOS are the remaining hard residual; see `DOCTRINE-walls.md` R11/R12.)
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Plain finite-sum dot product on `ι → ℝ`. -/
def dotV (f g : ι → ℝ) : ℝ := ∑ x, f x * g x

/-- Kernel action `K f`. -/
def kerApply (K : ι → ι → ℝ) (f : ι → ℝ) : ι → ℝ := fun x => ∑ y, K x y * f y

/-- The killed/resolvent form operator `A_K = I − K`. -/
def greenA (K : ι → ι → ℝ) (f : ι → ℝ) : ι → ℝ := fun x => f x - kerApply K f x

/-- Dirichlet/resolvent quadratic form `Q_K(f) = ⟨A_K f, f⟩`. -/
def greenQ (K : ι → ι → ℝ) (f : ι → ℝ) : ℝ := dotV (greenA K f) f

end AnalyticCombinatorics.Ch8.Partitions.Erdos


