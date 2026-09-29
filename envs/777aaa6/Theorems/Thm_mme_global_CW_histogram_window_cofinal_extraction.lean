-- Prove2me | Theorems.Thm_mme_global_CW_histogram_window_cofinal_extraction
-- name    : mme_global_CW_histogram_window_cofinal_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T10:24:39.392267+00:00
-- url     : https://prove2.me/theorems/59cd1e28-71e9-4567-b42e-7121cb29ef76
-- title:
--   Actual global window extraction after paying for every exact type
-- statement:
--   For any nonempty supported global histogram window with uniform entropy lower bound E k^2 and entropy-exponent upper bound B k^2, sufficiently large square scales produce an actual GlobalCW.Part and tensor restriction. For every nonnegative rho<E, its guaranteed log copies minus log(input copies) is at least rho k^2. The family is constructed and its size, repair parameters and finite losses are proved, not assumed.
-- source:
--   Finite global realization for More Asymmetry Theorem 5.3, https://arxiv.org/html/2404.16349v2#S5 . This constructs the global window extraction needed by the joint finite-witness architecture; released profile and numerical instantiation remain open.

import Definitions.Def_mme_global_CW_histogram_frame
import Definitions.Def_mme_global_CW_entropy_data
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RegionRate MME.RecursiveYZ MME.GlobalCW MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_histogram_window_cofinal_extraction {K : Type u} [Field K] (C H d : ℕ) (B E rho : ℝ)
    (hB : 0 ≤ B) (hrho : 0 ≤ rho) (hgap : rho < E) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ hk : 1 < k,
      ∀ {ell M : ℕ} (D : HistogramFrame ell M)
        (good : Fin 3 → (Cell D.degree D.R D.bounds → CompleteSplit.CompleteWord ell → ℕ) → Prop),
      (∃ x : Fin 3 → FineWord M, supported x ∧ ∀ i, D.window good i (x i)) →
      M ≤ C*k^2 → D.degree ≤ H →
      Fintype.card (Cell D.degree D.R D.bounds) ≤ d →
      D.R*(D.degree+1) ≤ d →
      D.R*(D.degree+1)*Fintype.card (CompleteSplit.CompleteWord ell) ≤ d →
      3*Fintype.card (Cell D.degree D.R D.bounds)*Fintype.card (CompleteSplit.CompleteWord ell) ≤ d →
      (∀ mu : D.AdmissibleProfile, (∀ i, good i (mu.val i)) →
        E*(k : ℝ)^2 ≤ (D.stage mu k hk).entropyRate) →
      (∀ mu : D.AdmissibleProfile, (∀ i, good i (mu.val i)) →
        (D.stage mu k hk).entropyExponent ≤ B*(k : ℝ)^2) →
      ∃ S : GlobalCW.Part M ell (D.window good),
        1 ≤ S.inputs ∧
        S.inputs ≤ (D.L+1)^(3*Fintype.card (Cell D.degree D.R D.bounds)*
          Fintype.card (CompleteSplit.CompleteWord ell)) ∧
        rho*(k : ℝ)^2 + Real.log (S.inputs : ℝ) ≤ S.rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp S.rate⌉₊ ↦ tensor K (D.window good)))
          (bigAdd (fun _ : Fin S.inputs ↦ tensor K (fun _ (_ : FineWord M) ↦ True))) := by
  sorry
