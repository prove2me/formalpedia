-- Prove2me | Definitions.Def_mme_region_count_entropy_data
-- name    : mme_region_count_entropy_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T16:23:29.162523+00:00
-- url     : https://prove2.me/theorems/6b6c0ae2-b667-4f00-a30e-1fd7882700c4
-- title:
--   Entropy potentials and polynomial count errors for finite regions
-- statement:
--   Define the entropy potential and explicit polynomial error factor for products of cell multinomials, allowing empty cells.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Definitions.Def_mme_recursive_yz_compatibility
import Definitions.Def_mme_modern_entropy_data

open BigOperators
set_option autoImplicit false
namespace MME.RegionRealization

/-- Natural-log entropy potential of finite cell histograms, including empty cells. -/
noncomputable def potential {C W : Type*} [Fintype C] [Fintype W]
    (mu : C → W → ℕ) : ℝ :=
  ∑ c, (((∑ w, mu c w : ℕ) : ℝ) * Real.log 2 *
    mme_modern_entropyBits (fun w ↦ (mu c w : ℝ) / ((∑ z, mu c z : ℕ) : ℝ)))

/-- Explicit polynomial error term for the product of cell multinomials. -/
noncomputable def errorFactor {C W : Type*} [Fintype C] [Fintype W]
    (mu : C → W → ℕ) (m : ℕ) : ℝ :=
  ∏ c, (6 * (((∑ w, mu c w) * m + 1 : ℕ) : ℝ)) ^ Fintype.card W

end MME.RegionRealization


