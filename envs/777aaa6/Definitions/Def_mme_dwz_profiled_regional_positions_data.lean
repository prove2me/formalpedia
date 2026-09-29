-- Prove2me | Definitions.Def_mme_dwz_profiled_regional_positions_data
-- name    : mme_dwz_profiled_regional_positions_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T09:01:19.327578+00:00
-- url     : https://prove2.me/theorems/d03653a2-ed21-4cc0-96ca-e703b1b90e8d
-- title:
--   Canonical scaled position layout for regional recipes
-- statement:
--   The canonical layout of the scaled regional positions (region, then position, then half) as an equivalence Fin (sum_r 2 t n_r) = Position (t n), and the matching atomic size.
-- source:
--   Canonical position layout for the More-Asymmetry regional construction (arXiv 2404.16349, Section 6).

import Definitions.Def_mme_dwz_profiled_regional_keep_data
import Mathlib.Algebra.BigOperators.Fin

open BigOperators MME MME.RecursiveYZ

set_option autoImplicit false

namespace MME.DWZProfiledRegional

/-- Number of half-word slots when every region's position count is scaled by `t`. -/
def lenAt {R : ℕ} (n : Fin R → ℕ) (t : ℕ) : ℕ := ∑ r, t * n r * 2

/-- The canonical layout of the scaled positions: region by region, then position, then half. -/
def positionsAt {R : ℕ} (n : Fin R → ℕ) (t : ℕ) :
    Fin (lenAt n t) ≃ Position (fun r ↦ t * n r) :=
  finSigmaFinEquiv.symm.trans (Equiv.sigmaCongrRight fun _ ↦ finProdFinEquiv.symm)

/-- The number of atomic CW factors at scale `t` (two per half-word slot). -/
def sizeAt {R : ℕ} (n : Fin R → ℕ) (t : ℕ) : ℕ := lenAt n t * 2 ^ (2 - 1)

theorem lengthAt {R : ℕ} (n : Fin R → ℕ) (t : ℕ) : lenAt n t * 2 ^ (2 - 1) = sizeAt n t := rfl

end MME.DWZProfiledRegional


