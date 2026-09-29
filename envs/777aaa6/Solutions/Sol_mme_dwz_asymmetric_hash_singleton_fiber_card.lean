-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_singleton_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:27:37.170204+00:00
-- url     : https://prove2.me/submissions/a6489955-4997-4943-9abe-d8de3c23a3bc

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_identity
import Theorems.Thm_mme_ZMod_prime_linear_hash_affine_graph_finset_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

open MME

theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum) :
    (dwzAsymmetricAffineStatesRetaining
      levelSum S I J K).card = S.card * p ^ (N + 1) := by
  classical
  let c : Fin (N + 2) → ZMod p :=
    Fin.lastCases 1 (fun t : Fin (N + 1) ↦ I t)
  let offset : (Fin (N + 2) → ZMod p) → ZMod p := fun W ↦
    (∑ t : Fin (N + 1), I t * W t.castSucc) -
      ∑ t : Fin (N + 1), J t * W t.castSucc
  have hc : c (Fin.last (N + 1)) ≠ 0 := by
    simp [c]
  have hlinear (W : Fin (N + 2) → ZMod p) :
      (∑ i, c i * W i) =
        W (Fin.last (N + 1)) +
          ∑ t : Fin (N + 1), I t * W t.castSucc := by
    rw [Fin.sum_univ_castSucc]
    simp [c, add_comm]
  have hpred (q : (Fin (N + 2) → ZMod p) × ZMod p) :
      dwzAsymmetricAffineRetains levelSum S I J K q ↔
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1 := by
    let ω := dwzAsymmetricHashStateOfAffine q
    constructor
    · rintro ⟨s, hsS, hX, hY, _hZ⟩
      have hX' :
          q.1 (Fin.last (N + 1)) +
              ∑ t : Fin (N + 1), I t * q.1 t.castSucc = s := by
        simpa only [dwzAsymmetricHashX,
          dwzAsymmetricHashStateOfAffine] using hX
      have hY' :
          q.1 (Fin.last (N + 1)) + q.2 +
              ∑ t : Fin (N + 1), J t * q.1 t.castSucc = s := by
        simpa only [dwzAsymmetricHashY,
          dwzAsymmetricHashStateOfAffine] using hY
      constructor
      · rw [hlinear, hX']
        exact hsS
      · dsimp only [offset]
        apply (eq_sub_iff_add_eq).2
        have heq := hY'.trans hX'.symm
        exact add_left_cancel (a := q.1 (Fin.last (N + 1)))
          (by simpa [add_assoc] using heq)
    · rintro ⟨hlinS, hw0⟩
      let s : ZMod p := ∑ i, c i * q.1 i
      have hsS : s ∈ S := hlinS
      have hs : (∑ i, c i * q.1 i) = s := rfl
      refine ⟨s, hsS, ?_, ?_, ?_⟩
      · simpa only [dwzAsymmetricHashX,
          dwzAsymmetricHashStateOfAffine, hlinear] using hs
      · simp only [dwzAsymmetricHashY,
          dwzAsymmetricHashStateOfAffine]
        rw [hw0]
        dsimp only [offset]
        rw [hlinear] at hs
        calc
          q.1 (Fin.last (N + 1)) +
                (∑ t, I t * q.1 t.castSucc -
                  ∑ t, J t * q.1 t.castSucc) +
              ∑ t, J t * q.1 t.castSucc =
              q.1 (Fin.last (N + 1)) +
                ∑ t, I t * q.1 t.castSucc := by abel
          _ = s := hs
      · have hap := mme_dwz_asymmetric_hash_AP_identity
          hpodd levelSum ω I J K hsupport
        have hX : dwzAsymmetricHashX ω I = s := by
          simpa only [ω, dwzAsymmetricHashX,
            dwzAsymmetricHashStateOfAffine, hlinear] using hs
        have hY : dwzAsymmetricHashY ω J = s := by
          simp only [ω, dwzAsymmetricHashY,
            dwzAsymmetricHashStateOfAffine]
          rw [hw0]
          dsimp only [offset]
          rw [hlinear] at hs
          calc
            q.1 (Fin.last (N + 1)) +
                  (∑ t, I t * q.1 t.castSucc -
                    ∑ t, J t * q.1 t.castSucc) +
                ∑ t, J t * q.1 t.castSucc =
                q.1 (Fin.last (N + 1)) +
                  ∑ t, I t * q.1 t.castSucc := by abel
            _ = s := hs
        rw [hX, hY] at hap
        have htwo : (2 : ZMod p) ≠ 0 :=
          ((ZMod.isUnit_iff_coprime 2 p).2
            hpodd.coprime_two_left).ne_zero
        apply Eq.symm
        apply mul_left_cancel₀ htwo
        simpa [two_mul] using hap
  have hfilter :
      dwzAsymmetricAffineStatesRetaining levelSum S I J K =
      Finset.univ.filter (fun q :
          (Fin (N + 2) → ZMod p) × ZMod p ↦
        (∑ i, c i * q.1 i) ∈ S ∧ q.2 = offset q.1) := by
    simp only [dwzAsymmetricAffineStatesRetaining]
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpred q
  rw [hfilter]
  exact mme_ZMod_prime_linear_hash_affine_graph_finset_card
    c (Fin.last (N + 1)) hc S offset
