-- Prove2me | Definitions.Def_mme_common_hash_scale
-- name    : mme_common_hash_scale
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T16:24:36.851999+00:00
-- url     : https://prove2.me/theorems/5c0ced0e-dd8f-444a-9fd1-e5f4a57768f1
-- title:
--   The maximum of all finite hash load quotients
-- statement:
--   One natural scale is the maximum of a grade floor and all integer numerator/positive-denominator quotients plus one. It does not assert budget feasibility or a rate.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
namespace MME.RegionRealization

/-- One scale for the entire region: the maximum, rather than a sum or product,
of the integer quotients in every required mode. -/
noncomputable def commonScale {J : Type*} [Fintype J]
    (grade : ℕ) (num den : J → ℕ) : ℕ := by
  classical
  exact max (grade + 1) (Finset.univ.sup (fun j ↦ num j / den j + 1))

end MME.RegionRealization


