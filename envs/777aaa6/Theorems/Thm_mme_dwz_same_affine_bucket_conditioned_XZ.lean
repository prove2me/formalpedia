-- Prove2me | Theorems.Thm_mme_dwz_same_affine_bucket_conditioned_XZ
-- name    : mme_dwz_same_affine_bucket_conditioned_XZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:26:59.904836+00:00
-- url     : https://prove2.me/theorems/e0629b5b-30e9-45e1-807b-473f3f691df6
-- title:
--   A common asymmetric-hash bucket supplies Claim 6.8's conditioned X--Z hash
-- statement:
--   Let $(I,J,K)$ and $(I',J',K)$ be two coordinatewise supported triples over $\mathbb Z/p\mathbb Z$ with the same Z address, where $p$ is odd. Suppose both triples survive the same asymmetric affine-hash state with labels in a three-term-progression-free set. Then the AP-free common-label property and the conditioned central offset imply
--
--   $$
--   h_X(I')=h_Z\!\left(2\sum_t I_tw_t-\sum_t(L-K_t)w_t,\,K\right).
--   $$
--
--   This is precisely the retained-hash predicate used for a compatible competitor in Claim 6.8. It formalizes that all large triples kept in one first-hash bucket automatically satisfy the later conditioned X--Z hash test; no additional tensor-support hypothesis is required.
--
--   **Formalization Note** The conclusion keeps the affine weight and offset read directly from the shared hash state and works for an arbitrary common level sum.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, asymmetric hashing in Section 3.10 and Claim 6.8, PDF pp. 25--27 and 56--57 / printed pp. 24--26 and 55--56; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label

open BigOperators
open MME

set_option autoImplicit false

theorem mme_dwz_same_affine_bucket_conditioned_XZ
    {p n : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (levelSum : ZMod p)
    (I J K I' J' : Fin (n + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (hsupport' : ∀ t, I' t + J' t + K t = levelSum)
    (q : (Fin (n + 2) → ZMod p) × ZMod p)
    (hcentral :
      let castS : Finset (ZMod p) :=
        S.image (fun a : ℕ ↦ (a : ZMod p))
      let ω := dwzAsymmetricHashStateOfAffine q
      dwzAsymmetricHashX ω I ∈ castS ∧
        dwzAsymmetricHashY ω J ∈ castS ∧
        dwzAsymmetricHashZ levelSum ω K ∈ castS)
    (hcandidate :
      let castS : Finset (ZMod p) :=
        S.image (fun a : ℕ ↦ (a : ZMod p))
      let ω := dwzAsymmetricHashStateOfAffine q
      dwzAsymmetricHashX ω I' ∈ castS ∧
        dwzAsymmetricHashY ω J' ∈ castS ∧
        dwzAsymmetricHashZ levelSum ω K ∈ castS) :
    let weight : Fin (n + 1) → ZMod p := fun t ↦ q.1 t.castSucc
    let b0 : ZMod p := q.1 (Fin.last (n + 1))
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → ZMod p) → ZMod p := fun w A ↦
      b0 + ∑ t, A t * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → ZMod p) → ZMod p := fun w0 w C ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, (levelSum - C t) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
      2 * (∑ t, I t * w t) -
        ∑ t, (levelSum - K t) * w t
    hX weight I' = hZ (conditionedW0 weight) weight K := by
  sorry
