-- Prove2me | Definitions.Def_Zeta23_MV_Spacing
-- name    : Zeta23_MV_Spacing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:07:09.125151+00:00
-- url     : https://prove2.me/theorems/4fa6b3ef-efa2-4a66-95c7-3c908fc74d1d
-- title:
--   Admissible frequency–gap pairs and their disjoint intervals $I_t$ (MV step 0)
-- statement:
--   This bundle fixes the admissibility structure used throughout the project's proof of the Montgomery–Vaughan inequality. For a finite index type $\iota$ and functions $\lambda, \delta : \iota \to \mathbb{R}$ (`freq`, `δ`):
--
--   - `MV.Adm freq δ` is the proposition (a structure) that the pair is **admissible**: $\lambda$ is injective, $\delta_r > 0$ for all $r$, and $\delta_r \le |\lambda_r - \lambda_s|$ for all $s \neq r$ — exactly the hypothesis shape of `Zeta23.MVHilbert`. This generalizes the literature's minimal-gap choice $\delta_r = \min_{s\neq r}|\lambda_r - \lambda_s|$.
--   - `MV.Adm.itv` assigns to each index $t$ the open interval
--   $$I_t \;:=\; \bigl(\lambda_t - \tfrac{\delta_t}{2},\; \lambda_t + \tfrac{\delta_t}{2}\bigr),$$
--   which under admissibility are pairwise disjoint.
--
--   Role: the disjointness of the intervals $I_t$ drives, by comparison with $\int |u - \lambda_s|^{-\sigma}\,du$, the elementary spacing lemmas $\sum_{t\neq s} \delta_t/(\lambda_s-\lambda_t)^2 \le 9/\delta_s$, $\sum_{t\neq s} \delta_t/(\lambda_s-\lambda_t)^4 \le 27/\delta_s^3$, and a two-point variant — replacing Preissmann's lemmas with self-contained arguments at worse (but sufficient) constants. These feed the quadratic-form and eigenvalue steps that culminate in the diagonal Montgomery–Vaughan inequality `MVDiag`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/Spacing.lean

import Mathlib

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 0 — spacing lemmas for admissible weights

For an injective `freq : ι → ℝ` on a finite index type with ADMISSIBLE weights `δ`
(`0 < δ r` and `δ r ≤ |freq r − freq s|` for all `s ≠ r` — the shape of Zeta23.MVHilbert),
the open intervals `I_t = (freq t − δ t/2, freq t + δ t/2)` are pairwise disjoint, giving
by comparison with `∫ |u − freq s|^{−σ} du`:

* `spacing_sq`   (σ = 2):  Σ_{t≠s} δ t/(freq s − freq t)²  ≤  9/δ s
* `spacing_four` (σ = 4):  Σ_{t≠s} δ t/(freq s − freq t)⁴  ≤  27/(δ s)³
* `two_point`:  Σ_{k≠ℓ,m} δ k/((freq k − freq ℓ)²(freq k − freq m)²)
                  ≤ 36(δ ℓ + δ m)/(δ ℓ · δ m · (freq ℓ − freq m)²)

These replace [Preissmann 1984, Lemmes 1 & 6] (cited without proof in arXiv:2203.14950)
with elementary arguments at worse constants — sufficient for the ∃C form.
-/

noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Admissibility of weights (matches Zeta23.MVHilbert's hypotheses). -/
structure Adm (freq δ : ι → ℝ) : Prop where
  inj : Function.Injective freq
  pos : ∀ r, 0 < δ r
  le : ∀ r s, r ≠ s → δ r ≤ |freq r - freq s|

namespace Adm

variable {freq δ : ι → ℝ} (h : Adm freq δ)

/-- The interval `I_t`. -/
def itv (t : ι) : Set ℝ := Set.Ioo (freq t - δ t / 2) (freq t + δ t / 2)







section MainSpacing
variable (h : Adm freq δ) (s : ι)





end MainSpacing





end Adm
end MV
end Zeta23


