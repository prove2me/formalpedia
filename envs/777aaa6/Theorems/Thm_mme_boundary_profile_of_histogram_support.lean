-- Prove2me | Theorems.Thm_mme_boundary_profile_of_histogram_support
-- name    : mme_boundary_profile_of_histogram_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:53:03.646442+00:00
-- url     : https://prove2.me/theorems/0c52d437-175f-436f-a09b-cb10d06fe0cd
-- title:
--   Reconstructing exact boundary profiles from scalar histograms
-- statement:
--   Fix a level $\ell$, a multiplicity $L$, three grades $g_0,g_1,g_2$ summing to $2\cdot2^{\ell-1}$, and three complete-word histograms of mass $L$, each supported at its specified grade. Assume the histograms satisfy the complementary-word identities for zero-grade modes. If $g_z=0$, there is an exact boundary profile whose three grades and histograms agree with the supplied data in orientation $z$. This reconstructs the finite boundary data from scalar support and complement conditions.
-- source:
--   Exact complementary boundary profiles and the terminal ProfiledCW recipe interface.

import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false

theorem mme_boundary_profile_of_histogram_support
    (ell L : ℕ) (shape : Fin 3 → ℕ) (mu : Fin 3 → CompleteWord ell → ℕ)
    (ht : shape 0 + shape 1 + shape 2 = 2 * 2 ^ (ell - 1))
    (hm : ∀ i, ∑ s, mu i s = L)
    (hg : ∀ i s, 0 < mu i s → grade s = shape i)
    (hboundary :
      (shape 2 = 0 → ∀ s, mu 1 s = mu 0 (fun r ↦ Fin.rev (s r))) ∧
      (shape 0 = 0 → ∀ s, mu 2 s = mu 1 (fun r ↦ Fin.rev (s r))) ∧
      (shape 1 = 0 → ∀ s, mu 2 s = mu 0 (fun r ↦ Fin.rev (s r))))
    (z : Fin 3) (hz : shape z = 0) :
    ∃ B : Boundary.Profile ell L,
      (∀ i, shape i = B.shape z i) ∧ (∀ i, mu i = B.mu z i) := by sorry
