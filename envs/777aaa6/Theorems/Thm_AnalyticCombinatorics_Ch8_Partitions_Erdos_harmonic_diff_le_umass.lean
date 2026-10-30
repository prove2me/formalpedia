-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_harmonic_diff_le_umass
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.harmonic_diff_le_umass
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:38:43.134629+00:00
-- url     : https://prove2.me/theorems/814a4abd-ca5b-48d4-859e-444383247a37
-- title:
--   A conditional harmonic-average difference bound
-- statement:
--   Let $\alpha$ be a finite type with decidable equality, let $P$ be a nonnegative row-stochastic real kernel, and fix the source rank function and natural window $W$. Suppose $|h(z)|\le B$ for all $z$ and two real values satisfy $h_i=\sum_zP^m(i,z)h(z)$ and $h_j=\sum_zP^m(j,z)h(z)$. Then $$|h_i-h_j|\le2B\,\texttt{umass}(P,\texttt{rnk},W,i,j,m).$$ The unmatched-mass construction and both exact averaging premises are retained. This is a reusable conditional estimate.
--
--   This support estimate carries the following complete literal source contract:
--
--   ```lean
--   theorem harmonic_diff_le_umass (h : α → ℝ) (B : ℝ) (hB : ∀ z, |h z| ≤ B)
--       (hi hj : ℝ) (i j : α) (m : ℕ)
--       (hhi : hi = ∑ z, Mpow P m i z * h z) (hhj : hj = ∑ z, Mpow P m j z * h z) :
--       |hi - hj| ≤ umass P rnk W i j m * (2 * B)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ActiveCoupling.lean#L49. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Active coupling inequality (TASK #9 layer B, abstract core)

The route-independent coupling bound for the windowed pair coupling: if `h` is a bounded function on a
finite state type `α` that equals its `m`-step `Mpow`-average at two starts `i, j` (i.e. `h` is
`Mpow`-harmonic at those starts), then

  `|h i_val − h j_val| ≤ umass(i, j, m) · (2 B)`,

where `umass` is the unmatched (non-coalesced) pair mass of the windowed coupling and `2 B` plays the
role of the oscillation constant `osc(h)` (a FIXED finite constant once `h` is bounded — no `u`
oscillation bootstrap is needed).  This is the abstract content behind the spec's

  `|hitVal_J(i) − hitVal_J(j)| ≤ umass_active(i, j) · osc_J(u)`.

Proof: combine `harmonic_diff_le_overlap` (`|hi − hj| ≤ 2 B (1 − overlap p q)`) with the banked coupling
invariants `umass_eq` (`umass = 1 − ∑ ρ`) and `rho_mass_le_overlap` (`∑ ρ ≤ overlap`), giving
`1 − overlap ≤ umass`.  Pure finite-sum linear algebra.  Opus-authored.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
include hPnn hPmass

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.harmonic_diff_le_umass (h : α → ℝ) (B : ℝ) (hB : ∀ z, |h z| ≤ B)
    (hi hj : ℝ) (i j : α) (m : ℕ)
    (hhi : hi = ∑ z, Mpow P m i z * h z) (hhj : hj = ∑ z, Mpow P m j z * h z) :
    |hi - hj| ≤ umass P rnk W i j m * (2 * B) := by sorry
