-- Prove2me | Theorems.Thm_mme_boundary_scaled_volume_rate
-- name    : mme_boundary_scaled_volume_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:14:22.04742+00:00
-- url     : https://prove2.me/theorems/1b61ea81-990e-43f8-b2a4-1985ac32862c
-- title:
--   Scaled boundary profiles attain their entropy and CW-letter volume rate
-- statement:
--   For any positive-length boundary profile B and any positive tolerance delta, eventually every replication k and every boundary profile C whose counts are k times those of B satisfy log(C.dim) >= k times the base histogram entropy contribution plus the base CW-letter contribution minus delta. The threshold is uniform over C. The proof absorbs the multinomial logarithmic loss into the arbitrary linear tolerance.
-- source:
--   Multinomial entropy lower bound and exact boundary matrix dimension.

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Definitions.Def_mme_recursive_yz_boundary_data
open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false
universe u

theorem mme_boundary_scaled_volume_rate {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ C : Profile ell (L * k),
      (∀ s, C.count s = B.count s * k) →
      (k : ℝ) * ((L : ℝ) * Real.log 2 *
          mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) +
        ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.dim : ℝ) := by sorry
