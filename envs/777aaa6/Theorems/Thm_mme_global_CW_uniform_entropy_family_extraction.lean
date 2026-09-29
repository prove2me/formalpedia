-- Prove2me | Theorems.Thm_mme_global_CW_uniform_entropy_family_extraction
-- name    : mme_global_CW_uniform_entropy_family_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T08:49:47.274077+00:00
-- url     : https://prove2.me/theorems/898d1df5-7e62-4021-ae1a-ad92ac35411a
-- title:
--   Actual global extraction from uniform entropy and finite-loss bounds
-- statement:
--   Consider a finite supported exact-profile cover by counted global stages. Suppose their entropy rates are at least E, joint entropies at most J, target error factors at most P, scale factors at most F and repair exponents at most h. Every nonnegative rate r <= E-log(P)-log(64F)-4 sqrt(log(F)+J-E)-h log(8) gives an actual extraction of ceil(exp(r)) copies of the covered interface, from one unrestricted source copy per profile. It also constructs the existing global Part used by the joint recipe.
-- source:
--   More Asymmetry Theorem 5.3 global stage: https://arxiv.org/html/2404.16349v2#S5. Generic finite entropy and tolerance estimates; not a completed numerical exponent certificate.

import Definitions.Def_mme_global_CW_real_entropy_profiles
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_uniform_entropy_family_extraction {K : Type u} [Field K] {M ell types : ℕ} (T : Predicate M)
    (steps : Fin types → CountedStage ell M)
    (rate E J P F h : ℝ) (hrate : 0 ≤ rate)
    (hbudget : rate ≤ E - Real.log P - Real.log (64 * F) -
      4 * Real.sqrt (Real.log F + J - E) - h * Real.log 8)
    (hE : ∀ j, E ≤ (steps j).entropyRate)
    (hJ : ∀ j, jointPotential (steps j).m ≤ J)
    (hP : ∀ j, polynomialFactor (steps j).n
      (Fintype.card (Cell (steps j).degree (steps j).R (steps j).bounds)) ≤ P)
    (hF : ∀ j, (steps j).entropyScaleFactor ≤ F)
    (hh : ∀ j, ((steps j).repairExponent : ℝ) ≤ h)
    (inside : ∀ j i x, (steps j).output i x → T i x)
    (cover : ∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
      ∃! j, ∀ i, (steps j).output i (x i)) :
    ∃ D : GlobalCW.Part M ell T, D.inputs = types ∧ D.rate = rate ∧
      Restrict (bigAdd (fun _ : Fin ⌈Real.exp rate⌉₊ ↦ tensor K T))
        (bigAdd (fun _ : Fin types ↦ tensor K (fun _ (_ : FineWord M) ↦ True)))  := by
  sorry
