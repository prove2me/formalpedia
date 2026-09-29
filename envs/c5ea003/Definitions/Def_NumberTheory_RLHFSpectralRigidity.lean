-- Prove2me | Definitions.Def_NumberTheory_RLHFSpectralRigidity
-- name    : NumberTheory_RLHFSpectralRigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:07.756741+00:00
-- url     : https://prove2.me/theorems/0bc28b7e-5086-4c4c-8910-e577e0b9e731
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFSpectralRigidity
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFSpectralRigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFSpectralRigidity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational

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

namespace RLHF

open Finset

variable {Ω Ω₁ Ω₂ ι : Type*} [Fintype Ω] [Fintype Ω₁] [Fintype Ω₂] [Fintype ι]

/-- The probability mass that the reference policy `p` puts on the reward level `w`. -/
noncomputable def rewardMass (r p : Ω → ℝ) (w : ℝ) : ℝ :=
  ∑ y ∈ univ.filter (fun y => r y = w), p y




end RLHF


