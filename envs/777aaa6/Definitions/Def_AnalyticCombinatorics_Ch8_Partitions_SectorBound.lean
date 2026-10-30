-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SectorBound
-- name    : AnalyticCombinatorics_Ch8_Partitions_SectorBound
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:14:20.653141+00:00
-- url     : https://prove2.me/theorems/fcd98dce-7ccd-410d-818a-dcb565e7db56
-- title:
--   Sector Bound
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   def grad (f : ℤ → ℝ) (e : ℤ) : ℝ := f (e + 1) - f e
--   ```
--
--   ```lean
--   def Hcut (I : Finset ℤ) (J : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (e : ℤ) : ℝ :=
--     (1 / 2 : ℝ) * ∑ x ∈ I, ∑ y ∈ I, J x y * f x * edgeSign e x y
--   ```
--
--   ```lean
--   def aAnti (I : Finset ℤ) (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (f g : ℤ → ℝ) : ℝ :=
--     (aK I π K f g - aK I π K g f) / 2
--   ```
--
--   ```lean
--   def edgeEnergyOn (E : Finset ℤ) (f : ℤ → ℝ) : ℝ := ∑ e ∈ E, (grad f e) ^ 2
--   ```
--
--   ```lean
--   def SectorBound (aAnti aSym : (ℤ → ℝ) → (ℤ → ℝ) → ℝ) (θ : ℝ) : Prop :=
--     ∀ f g, |aAnti f g| ≤ θ * Real.sqrt (aSym f f) * Real.sqrt (aSym g g)
--   ```
--
--   ```lean
--   def edgeSign (e x y : ℤ) : ℝ :=
--     if x ≤ e ∧ e < y then 1 else if y ≤ e ∧ e < x then -1 else 0
--   ```
--
--   ```lean
--   def aK (I : Finset ℤ) (π : ℤ → ℝ) (K : ℤ → ℤ → ℝ) (f g : ℤ → ℝ) : ℝ :=
--     ∑ x ∈ I, π x * f x * (g x - ∑ y ∈ I, K x y * g y)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/SectorBound.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Abstract sector bound (renewal route B, Layer-2 nonreversible perturbation)

The abstract sector framework (ChatGPT ac R13/R14) for the nonreversible Green comparison:

* definitions `edgeSign`, `grad`, `Jflow`, `divJ`, `Hcut`, `aK`, `aAnti`, `edgeEnergyOn`, `SectorBound`;
* `sector_bound_from_Hcut_on` — from a Hardy bound on `∑ Hcut²` (`≤ 8BΓ²L²·E_edge`), the cut identity
  `aAnti f g = −∑ Hcut(f)·grad g`, and ellipticity `p·E_edge ≤ aSym`, derive
  `|aAnti f g| ≤ θ·√(aSym f f)·√(aSym g g)` with `θ = √8·√B·Γ·L/p`, via Cauchy–Schwarz
  (`Finset.inner_mul_le_norm_mul_norm`) and `sq_le_sq₀`.

`sector_bound_from_Hcut_on` is fully abstract (it consumes the cut identity and Hardy/ellipticity as
hypotheses), so it is independent of the kernel.  Discharging its hypotheses for the *actual* Erdős
rank-difference kernel — the `erdos_rankdiff_sector_input` with `θ ≤ 1/2` — is the lone genuine
analytic residual (needs a reference measure / cut-flux control; see `DOCTRINE-walls.md` R13).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Signed indicator that edge `e` lies on the oriented path from `x` to `y`. -/
def edgeSign (e x y : ℤ) : ℝ :=
  if x ≤ e ∧ e < y then 1 else if y ≤ e ∧ e < x then -1 else 0

/-- Discrete gradient across edge `e`. -/
def grad (f : ℤ → ℝ) (e : ℤ) : ℝ := f (e + 1) - f e

/-- Weighted cut functional at edge `e`. -/
def Hcut (I : Finset ℤ) (J : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (e : ℤ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x ∈ I, ∑ y ∈ I, J x y * f x * edgeSign e x y

/-- Edge energy over an explicit edge set. -/
def edgeEnergyOn (E : Finset ℤ) (f : ℤ → ℝ) : ℝ := ∑ e ∈ E, (grad f e) ^ 2

/-- Abstract sector condition: `|aAnti f g| ≤ θ·√(aSym f f)·√(aSym g g)`. -/
def SectorBound (aAnti aSym : (ℤ → ℝ) → (ℤ → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∀ f g, |aAnti f g| ≤ θ * Real.sqrt (aSym f f) * Real.sqrt (aSym g g)

end AnalyticCombinatorics.Ch8.Partitions.Erdos


