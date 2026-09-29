-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_retaining_states_broken_copy_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T21:17:35.224217+00:00
-- url     : https://prove2.me/submissions/fa417e35-03fa-4e31-b972-5a1c6b072258

import Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_weight_sum
import Theorems.Thm_mme_dwz_step2_broken_copy_aggregate_seven_eighths

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
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
  classical
  let Weight := Fin (N + 1) → ZMod p
  let weightCopy : Weight → MME.DWZSquare.BrokenBlockCopy Block := fun w ↦
    MME.DWZStep2.brokenCopy
      (fun z A ↦ compatible z A ∧ hashRetained A w)
      useful retained
  have hweight := mme_dwz_step2_broken_copy_aggregate_seven_eighths
    compatible useful hashRetained retained hUseful hCompatible hHash hpointwise
  have hweightCard : Fintype.card Weight = p ^ (N + 1) := by
    simp only [Weight, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [hweightCard] at hweight
  have hsum := mme_dwz_asymmetric_hash_retaining_states_weight_sum
    hpodd levelSum S I J K hsupport
      (fun w ↦ (weightCopy w).nonholes.card)
  have hstateSum :
      (∑ q ∈ MME.dwzAsymmetricAffineStatesRetaining
          levelSum S I J K,
          (copyAtState q).nonholes.card) =
        S.card * ∑ w : Weight, (weightCopy w).nonholes.card := by
    calc
      (∑ q ∈ MME.dwzAsymmetricAffineStatesRetaining
          levelSum S I J K,
          (copyAtState q).nonholes.card) =
          ∑ q ∈ MME.dwzAsymmetricAffineStatesRetaining
              levelSum S I J K,
            (weightCopy (fun t ↦ q.1 t.castSucc)).nonholes.card := by
        apply Finset.sum_congr rfl
        intro q hq
        have hret :
            MME.dwzAsymmetricAffineRetains levelSum S I J K q := by
          simpa only [MME.dwzAsymmetricAffineStatesRetaining,
            Finset.mem_filter, Finset.mem_univ, true_and] using hq
        rw [hcopy q hret]
      _ = S.card * ∑ w : Weight,
          (weightCopy w).nonholes.card := by
        simpa only [Weight] using hsum
  rw [hstateSum]
  calc
    7 * S.card * p ^ (N + 1) * Fintype.card Block =
        S.card * (7 * p ^ (N + 1) * Fintype.card Block) := by ring
    _ ≤ S.card *
        (8 * ∑ w : Weight, (weightCopy w).nonholes.card) :=
      Nat.mul_le_mul_left S.card hweight
    _ = 8 * (S.card *
        ∑ w : Weight, (weightCopy w).nonholes.card) := by ring
