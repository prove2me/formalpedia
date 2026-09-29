-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_broken_copy_mass
-- name    : mme_dwz_asymmetric_hash_retaining_states_broken_copy_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:17:13.503592+00:00
-- url     : https://prove2.me/theorems/0f6c8cbd-7190-4610-bea9-62e4931f3184
-- title:
--   Claim 6.8 aggregate broken-copy mass lifts to retaining affine states
-- statement:
--   Let a supported component triple be fixed. Suppose every retaining affine state determines a literal Step-2 broken copy through its weight coordinates. Assume the retained owner is useful, compatible, and retained for every weight, and that Claim 6.8's bad-weight fiber bound holds for every block. Then the aggregate number of nonholes over retaining affine states is at least seven eighths of |S| times the full weight-block mass; equivalently, 7|S|p^(N+1)|B| is at most eight times the state-indexed nonhole sum.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8 and asymmetric hash-state averaging; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_weight_sum
import Theorems.Thm_mme_dwz_step2_broken_copy_aggregate_seven_eighths

open BigOperators

set_option autoImplicit false

theorem mme_dwz_asymmetric_hash_retaining_states_broken_copy_mass
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    {Block Outer : Type}
    [Fintype Block] [DecidableEq Block]
    [Fintype Outer] [DecidableEq Outer]
    (compatible useful : Block → Outer → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (hashRetained : Outer → (Fin (N + 1) → ZMod p) → Prop)
    [DecidableRel hashRetained]
    (retained : Outer)
    (copyAtState : ((Fin (N + 2) → ZMod p) × ZMod p) →
      MME.DWZSquare.BrokenBlockCopy Block)
    (hcopy : ∀ q,
      MME.dwzAsymmetricAffineRetains levelSum S I J K q →
        copyAtState q =
          MME.DWZStep2.brokenCopy
            (fun z A ↦ compatible z A ∧
              hashRetained A (fun t ↦ q.1 t.castSucc))
            useful retained)
    (hUseful : ∀ z : Block, useful z retained)
    (hCompatible : ∀ z : Block, compatible z retained)
    (hHash : ∀ w : Fin (N + 1) → ZMod p,
      hashRetained retained w)
    (hpointwise : ∀ z : Block,
      8 * (Finset.univ.filter (fun w : Fin (N + 1) → ZMod p ↦
        1 < (Finset.univ.filter (fun A : Outer ↦
          compatible z A ∧ hashRetained A w)).card)).card ≤
        Fintype.card (Fin (N + 1) → ZMod p)) :
    7 * S.card * p ^ (N + 1) * Fintype.card Block ≤
      8 * ∑ q ∈ MME.dwzAsymmetricAffineStatesRetaining
          levelSum S I J K,
          (copyAtState q).nonholes.card := by
  sorry
