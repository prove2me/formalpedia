-- Prove2me | Theorems.Thm_RLHF_rewardMass_eq_zero
-- name    : RLHF.rewardMass_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:47:18.681264+00:00
-- url     : https://prove2.me/theorems/8346eabc-0087-453a-a6c6-9cd8e0a11cdf
-- title:
--   A level outside the range of the reward carries no mass.
-- statement:
--   A level outside the range of the reward carries no mass.
--
--   ```lean
--   theorem RLHF.rewardMass_eq_zero{r p : Ω → ℝ} {w : ℝ} (hw : w ∉ image r univ) :
--       rewardMass r p w = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFSpectralRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFSpectralRigidity.lean#L36

-- Thm stub generated from NumberTheory/RLHFSpectralRigidity.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFSpectralRigidity

/-!
# The reward spectrum of an RLHF problem and its rigidity

The partition function `Z(t) = ∑_y p y · exp (r y · t)` of an RLHF problem only sees the
reward `r` through the *reward spectrum*: the finitely many reward levels together with the
probability mass the reference policy puts on each of them.  This file introduces that
spectrum and proves the two structural facts used downstream
(`Catalog/NumberTheory/RLHFPronySampling.lean`,
`Catalog/NumberTheory/RLHFChebyshevSystem.lean`):

* `RLHF.rewardMass` — the mass `∑_{y : r y = w} p y` carried by the level `w`;
* `RLHF.rewardMass_eq_zero` — levels outside the range of the reward carry no mass;
* `RLHF.sum_exp_eq_rewardMass_sum` — **spectral form of the partition function**: for any
  finite list of candidate levels containing the range of `r`, the exponential sum
  `∑_y p y exp (r y t)` collapses to the sum over levels `∑_w rewardMass r p w · exp (w t)`.
  This is the fibrewise decomposition of the response space over the reward levels.
* `RLHF.spectral_rigidity` — the qualitative rigidity statement: if two RLHF problems have
  the same reward spectrum, their partition functions agree at every temperature; and the
  spectral form shows the partition function depends on `(r, p)` only through the spectrum.

Everything here is elementary but load-bearing: it is the dictionary that turns statements
about partition functions into statements about (generalized) exponential sums.
-/

open RLHF

open Finset

variable {Ω Ω₁ Ω₂ ι : Type*} [Fintype Ω] [Fintype Ω₁] [Fintype Ω₂] [Fintype ι]

theorem RLHF.rewardMass_eq_zero{r p : Ω → ℝ} {w : ℝ} (hw : w ∉ image r univ) :
    rewardMass r p w = 0 := by sorry
