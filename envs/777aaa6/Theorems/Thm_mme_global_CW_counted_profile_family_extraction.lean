-- Prove2me | Theorems.Thm_mme_global_CW_counted_profile_family_extraction
-- name    : mme_global_CW_counted_profile_family_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T08:04:33.695271+00:00
-- url     : https://prove2.me/theorems/2e71763d-582c-4fd6-898e-ef30f39d749d
-- title:
--   Uniform global profile-family extraction from explicit counts
-- statement:
--   A finite supported exact-type cover whose pre-hash profiles share a nonnegative lower bound on the explicit global logarithmic copy certificate constructs a GlobalCW.Part of that rate and an actual uniform-copy extraction from the corresponding number of raw inputs. No prime, incidence or hole budget is assumed.
-- source:
--   Finite global stage of More Asymmetry Proposition 5.1 / Theorem 5.3.

import Definitions.Def_mme_global_CW_counted_stage
import Definitions.Def_mme_global_CW_joint_start_data
import Definitions.Def_mme_global_CW_counting_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ MME.GlobalCW MME.RecursiveXHash MME.HashExtraction
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_counted_profile_family_extraction {K : Type u} [Field K] {M ell types : ℕ} (T : Predicate M)
    (steps : Fin types → CountedStage ell M) (rate : ℝ) (hrate : 0 ≤ rate)
    (hbudget : ∀ j, rate ≤ (steps j).certifiedLogCopies)
    (inside : ∀ j i x, (steps j).output i x → T i x)
    (cover : ∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
      ∃! j, ∀ i, (steps j).output i (x i)) :
    ∃ D : GlobalCW.Part M ell T, D.inputs = types ∧ D.rate = rate ∧
      Restrict (bigAdd (fun _ : Fin ⌈Real.exp rate⌉₊ ↦ tensor K T))
        (bigAdd (fun _ : Fin types ↦ tensor K (fun _ (_ : FineWord M) ↦ True))) := by
  sorry
