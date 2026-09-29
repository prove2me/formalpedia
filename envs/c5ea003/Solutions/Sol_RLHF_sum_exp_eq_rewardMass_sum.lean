-- Prove2me | solution 1 for RLHF.sum_exp_eq_rewardMass_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:17:43.455108+00:00
-- url     : https://prove2.me/submissions/bd411bb1-4596-4c7a-b5ff-12694c7a051b

-- Sol generated from NumberTheory/RLHFSpectralRigidity.lean
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






open RLHF in
theorem solution{r p : Ω → ℝ} {v : ι → ℝ}
    (hsub : image r univ ⊆ image v univ) (t : ℝ) :
    ∑ y, p y * Real.exp (r y * t)
      = ∑ w ∈ image v univ, rewardMass r p w * Real.exp (w * t) := by
  have hmaps : ∀ y ∈ (univ : Finset Ω), r y ∈ image v univ := fun y _ =>
    hsub (Finset.mem_image_of_mem r (Finset.mem_univ y))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun y => p y * Real.exp (r y * t))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [rewardMass, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [(Finset.mem_filter.1 hy).2]
