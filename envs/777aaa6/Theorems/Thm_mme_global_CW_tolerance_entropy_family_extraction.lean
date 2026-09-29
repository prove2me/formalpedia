-- Prove2me | Theorems.Thm_mme_global_CW_tolerance_entropy_family_extraction
-- name    : mme_global_CW_tolerance_entropy_family_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T08:49:04.638535+00:00
-- url     : https://prove2.me/theorems/29ff06e6-788b-4aa5-a40a-5dde5d549e20
-- title:
--   Nearby-profile tolerance theorem for actual global extraction
-- statement:
--   For a finite family of counted stages and normalized reference profiles, every delta>0 admits one positive coordinate tolerance for the whole family. If the actual integer counts normalize to nearby profiles, the reference rates are at least E and each stage has at most S positions, then the uniform global extraction theorem applies with entropy rate E-delta S. The theorem retains the explicit joint-entropy, polynomial, hash and repair losses and returns an actual restriction and a global Part. It does not select the released numerical profiles, a numerical tolerance, or a concrete block size.
-- source:
--   More Asymmetry Theorem 5.3 global stage: https://arxiv.org/html/2404.16349v2#S5. Generic finite entropy and tolerance estimates; not a completed numerical exponent certificate.

import Definitions.Def_mme_global_CW_real_entropy_profiles
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_tolerance_entropy_family_extraction {K : Type u} [Field K] {M ell types : ℕ} (T : Predicate M)
    (steps : Fin types → CountedStage ell M)
    (p : ∀ j, EntropyProfile (steps j).degree (steps j).R (steps j).bounds (CompleteSplit.CompleteWord ell))
    (hp : ∀ j r c, 0 ≤ (p j).1 r c) (hmass : ∀ j r, ∑ c, (p j).1 r c = 1)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ∀ j, EntropyProfile (steps j).degree (steps j).R (steps j).bounds (CompleteSplit.CompleteWord ell),
      (∀ j r c, 0 ≤ (q j).1 r c) → (∀ j r, ∑ c, (q j).1 r c = 1) →
      (∀ j r c, ((steps j).m r c : ℝ) = ((steps j).n r : ℝ) * (q j).1 r c) →
      (∀ j i c w, ((steps j).mu i c w : ℝ) = ((steps j).n c.1 : ℝ) * (q j).2 i c w) →
      (∀ j r c, |(q j).1 r c - (p j).1 r c| ≤ eps) →
      (∀ j i c w, |(q j).2 i c w - (p j).2 i c w| ≤ eps) →
      ∀ rate E S J P F h : ℝ, 0 ≤ rate →
      rate ≤ (E - delta * S) - Real.log P - Real.log (64 * F) -
        4 * Real.sqrt (Real.log F + J - (E - delta * S)) - h * Real.log 8 →
      (∀ j, E ≤ (p j).rate (fun r ↦ ((steps j).n r : ℝ))) →
      (∀ j, (∑ r, ((steps j).n r : ℝ)) ≤ S) →
      (∀ j, jointPotential (steps j).m ≤ J) →
      (∀ j, polynomialFactor (steps j).n
        (Fintype.card (Cell (steps j).degree (steps j).R (steps j).bounds)) ≤ P) →
      (∀ j, (steps j).entropyScaleFactor ≤ F) →
      (∀ j, ((steps j).repairExponent : ℝ) ≤ h) →
      (∀ j i x, (steps j).output i x → T i x) →
      (∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i)) →
      ∃ D : GlobalCW.Part M ell T, D.inputs = types ∧ D.rate = rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp rate⌉₊ ↦ tensor K T))
          (bigAdd (fun _ : Fin types ↦ tensor K (fun _ (_ : FineWord M) ↦ True)))  := by
  sorry
