-- Prove2me | Theorems.Thm_mme_released_global_boundary_normalized_product_weight_rate
-- name    : mme_released_global_boundary_normalized_product_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T03:06:14.141507+00:00
-- url     : https://prove2.me/theorems/bfc1c5fa-86dd-4ff8-8ba7-55fbf4712efd
-- title:
--   Finite global boundary windows share a matrix-product rate
-- statement:
--   Any finite family of positive-mass released global boundary cells has one replication threshold and a positive square-matrix extraction from the sixfold-symmetrized product of its normalized windows. The tau weight attains the sum of the boundary entropy and CW-letter rates, uniformly over nonnegative tolerance and tau.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_sixSymmetrization_restrict
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_basis_projected_family_restrict
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj MME.RecursiveYZ.Boundary
open Filter
open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_boundary_normalized_product_weight_rate
    (owner : Fin 6) (n : ℕ) (c : Fin n → Cell 8 1 (fun _ _ ↦ 8))
    (hmass : ∀ r, 0 < coarseCounts owner (c r).2) (z : Fin n → Fin 3)
    (hz : ∀ r, ((c r).2.val (z r)).val = 0) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : ∀ r, Boundary.Profile 3
        (coarseCounts owner (c r).2),
      (∀ r i w, wordCounts owner i (c r).2 w = (B r).mu (z r) i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (eps : ℝ), 0 ≤ eps → ∀ (K : Type u) [Field K],
          Restrict (MMObj K M M M)
            (sixSymmetrization (kronFin n (fun r =>
              let L := k * coarseCounts owner (c r).2
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
        (∀ p, CWCells.grade (label 5 3 L (Equiv.refl _) x p) = ((c r).2.val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i (c r) w| ≤ eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
          ((blocks k : ℝ) / (L : ℝ)) * (profile owner).2 i (c r) w| ≤
          ((blocks k : ℝ) / (L : ℝ)) * eps)))))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (∑ r, 6 * tau * ((k : ℝ) *
            (((coarseCounts owner (c r).2 : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((coarseCounts owner (c r).2 : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by sorry
