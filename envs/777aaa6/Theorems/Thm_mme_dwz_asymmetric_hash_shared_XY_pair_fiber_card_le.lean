-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
-- name    : mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:42:22.744721+00:00
-- url     : https://prove2.me/theorems/083ed3d4-36b6-4093-a5fa-542f3e330da6
-- title:
--   Shared-coordinate pair incidence for the DWZ affine hash
-- statement:
--   Fix two distinct DWZ addresses of length $N+1$ over a prime field that share their $X$ coordinate word or share their $Y$ coordinate word, with the other relevant word unequal. For a finite common-label set $S$, the number of literal affine states simultaneously retaining both addresses is at most
--
--   $$|S|p^N.$$
--
--   This is the per-pair collision incidence estimate in the first asymmetric-hashing pruning step.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10, Lemma 3.11 and the per-pair collision estimate on printed pp. 26–27.

import Definitions.Def_mme_dwz_asymmetric_affine_hash

set_option autoImplicit false
open MME

theorem mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
    {p N : ℕ} [Fact p.Prime]
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K I' J' K' : Fin (N + 1) → ZMod p)
    (hshare : (I = I' ∧ J ≠ J') ∨ (J = J' ∧ I ≠ I')) :
    ((dwzAsymmetricAffineStatesRetaining levelSum S I J K) ∩
      (dwzAsymmetricAffineStatesRetaining levelSum S I' J' K')).card ≤
        S.card * p ^ N := by
  sorry
