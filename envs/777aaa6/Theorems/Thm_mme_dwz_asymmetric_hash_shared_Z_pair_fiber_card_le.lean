-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le
-- name    : mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T07:40:04.473056+00:00
-- url     : https://prove2.me/theorems/b3adda00-3012-45a1-bf4f-e8d8e0f50e98
-- title:
--   Shared-Z collision fibers of the actual DWZ affine hash
-- statement:
--   Let \(p\) be prime, \(S\subseteq\mathbb F_p\) a finite set of allowed labels, and \(I,J,K,I',J'\in\mathbb F_p^{N+1}\), with \(I\ne I'\). Fix the level-sum parameter of the standard DWZ affine hash. Writing \(\mathcal R(I,J,K)\) for the set of affine states that retain all three words at one common allowed label, we have
--
--   \[
--   \bigl|\mathcal R(I,J,K)\cap\mathcal R(I',J',K)\bigr|\ \le\ |S|p^N.
--   \]
--
--   This is the shared-Z collision bound for the literal affine-state construction. Together with its shared-X and shared-Y counterparts, it supplies the pair-count input to symmetric hashing. The inequality concerns already-retained states and requires neither oddness of the prime nor a coordinatewise support or profile hypothesis. It does not itself construct an isolated family or establish a tensor value.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Lemma 3.11 and the symmetric-hashing analysis, printed pp. 26–27. Uses the same affine hash displayed on printed p.25. For actual supported triples at odd prime modulus, this is the |S| times p^N count underlying the source's |S| p^(-3) pair-retention probability in a state space of size p^(N+3). The proof reuses mme_ZMod_two_linear_hash_finset_fiber_card_le and the exact private counting argument of the existing Proved shared-X/Y pair theorem; the only new argument obtains the common label from the shared Z word. The upper bound remains valid without oddness because it concerns states already satisfying all three common-label equations.

import Definitions.Def_mme_dwz_asymmetric_affine_hash

open MME

set_option autoImplicit false

theorem mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le
    {p N : ℕ} [Fact p.Prime]
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K I' J' : Fin (N + 1) → ZMod p) (hII' : I ≠ I') :
    ((dwzAsymmetricAffineStatesRetaining levelSum S I J K) ∩
      (dwzAsymmetricAffineStatesRetaining levelSum S I' J' K)).card ≤
        S.card * p ^ N := by sorry
