-- Prove2me | Theorems.Thm_mme_dwz_source_broken_family_restrict_of_induced_outer
-- name    : mme_dwz_source_broken_family_restrict_of_induced_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:17:21.615091+00:00
-- url     : https://prove2.me/theorems/00d9db9c-76fe-49f7-833e-06a20ecdec68
-- title:
--   An induced outer family extracts literal source broken owners
-- statement:
--   Let a finite family of Table-2 outer addresses be induced in the coordinatewise support hypergraph of the five-grading of the square q=6 Coppersmith--Winograd tensor: whenever one independently chooses an owner in each of the three modes and all mixed coordinate blocks are nonzero, the three choices come from one owner. For every arbitrary choice of source-aligned broken copy over each owner, the tensor power restricts to the direct sum of those literal broken owners. Each broken owner retains its complete shared X and Y spaces and applies only its internal nonhole projection in the Z mode.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2 and Additional Zeroing-Out Steps 1--2 in Sections 5--6; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_dwz_source_aligned_broken_address_projection_certificate
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME Module

universe u

set_option autoImplicit false

theorem mme_dwz_source_broken_family_restrict_of_induced_outer
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        (MME.cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦ MME.DWZSourceAligned.coarseAddress
            (outer (js i)) i r) ≠ 0) →
      ∃ j : Fin k, js = fun _ ↦ j) :
    MME.TensorObj.Restrict
      (MME.TensorObj.bigAdd (fun j ↦
        MME.DWZSourceAligned.brokenAddressObj K m
          (outer j) (copy j)))
      ((MME.TensorObj.kron (MME.CWObj K 6) (MME.CWObj K 6)).kronPow N) := by
  sorry
