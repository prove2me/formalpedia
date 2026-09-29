-- Prove2me | solution 1 for mme_dwz_prescribed_Z_product_uniform_basis_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:29:53.022973+00:00
-- url     : https://prove2.me/submissions/408a13c2-6505-4472-ae14-bce5fb5a447e

import Definitions.Def_mme_dwz_hole_cover_data
import Theorems.Thm_mme_dwz_prescribed_Z_power_uniform_basis_shuffle
import Theorems.Thm_mme_kronFin_modewise_basis_automorphisms_preserve_tensor
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Choose

open MME MME.TensorObj MME.DWZSquare MME.DWZRestrictedValue MME.DWZComponentRestriction
  Module PiTensorProduct BigOperators
open scoped Classical

universe u v w
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZProductShuffle

noncomputable def productSystem {C : Type w} [Fintype C] [DecidableEq C]
    {Block : C → Type u} {Shuffle : C → Type v}
    [∀ c, Fintype (Block c)] [∀ c, DecidableEq (Block c)]
    [∀ c, Fintype (Shuffle c)] [∀ c, DecidableEq (Shuffle c)]
    (system : ∀ c, AvailableBlockShuffle (Block c) (Shuffle c)) :
    AvailableBlockShuffle (∀ c, Block c) (∀ c, Shuffle c) where
  move g := Equiv.piCongrRight (fun c ↦ (system c).move (g c))
  uniform_fiber source target := by
    classical
    let fiber := fun c ↦ {g : Shuffle c // (system c).move g (source c) = target c}
    have hcard :
        (Finset.univ.filter (fun g : ∀ c, Shuffle c ↦
          (Equiv.piCongrRight (fun c ↦ (system c).move (g c))) source = target)).card =
          ∏ c, Fintype.card (fiber c) := by
      rw [← Fintype.card_subtype]
      calc
        Fintype.card {g : ∀ c, Shuffle c //
            (Equiv.piCongrRight (fun c ↦ (system c).move (g c))) source = target} =
            Fintype.card {g : ∀ c, Shuffle c //
              ∀ c, (system c).move (g c) (source c) = target c} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquivRight (fun g ↦ by simp [funext_iff])
        _ = Fintype.card (∀ c, fiber c) := Fintype.card_congr
          (Equiv.subtypePiEquivPi (p := fun c g ↦ (system c).move g (source c) = target c))
        _ = ∏ c, Fintype.card (fiber c) := Fintype.card_pi
    rw [hcard, Fintype.card_pi, Fintype.card_pi, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro c _
    simpa only [fiber, Fintype.card_subtype] using (system c).uniform_fiber (source c) (target c)

theorem productSystem_move {C : Type w} [Fintype C] [DecidableEq C]
    {Block : C → Type u} {Shuffle : C → Type v}
    [∀ c, Fintype (Block c)] [∀ c, DecidableEq (Block c)]
    [∀ c, Fintype (Shuffle c)] [∀ c, DecidableEq (Shuffle c)]
    (system : ∀ c, AvailableBlockShuffle (Block c) (Shuffle c))
    (g : ∀ c, Shuffle c) (b : ∀ c, Block c) (c : C) :
    (productSystem system).move g b c = (system c).move (g c) (b c) := rfl

end MME.DWZProductShuffle

theorem solution {K : Type u} [Field K] (k : ℕ)
    (T : Fin k → TensorObj K 3) {I : Fin k → Fin 3 → Type u}
    (b : ∀ c i, Basis (I c i) K ((T c).V i)) (t : Fin k → ℕ)
    (grade : ∀ c, I c 2 → Fin (t c))
    (p : ∀ c, IntegerZSplitProfile (t c)) (m : Fin k → ℕ) :
    let Coord := fun c ↦ {w : PowIndex (I c 2) ((p c).length (m c)) //
      prescribedZWord (grade c) (p c) (m c) w}
    let Block := fun c ↦ {w : PowIndex (Fin (t c)) ((p c).length (m c)) //
      prescribedZWord id (p c) (m c) w}
    let S := fun c ↦ prescribedZPower (T c) (b c 2) (grade c) (p c) (m c)
    let G := fun c ↦ ((T c).kronPow ((p c).length (m c))).basisZAllowedGrading
      (kronPowModeBasis (T c) 2 (b c 2) ((p c).length (m c)))
      (prescribedZWord (grade c) (p c) (m c))
    let P := TensorObj.kronFin k S
    ∃ factorBasis : ∀ c, Basis (Coord c) K ((G c).classOf 2 0),
    ∃ label : (∀ c, Coord c) → (∀ c, Block c),
    ∃ system : AvailableBlockShuffle (∀ c, Block c)
      (∀ c, Equiv.Perm (Fin ((p c).length (m c)))),
      (∀ c w, (factorBasis c w : ((T c).kronPow ((p c).length (m c))).V 2) =
        kronPowModeBasis (T c) 2 (b c 2) ((p c).length (m c)) w.1) ∧
      (∀ w c, (label w c).1 = PowIndex.ofFun ((p c).length (m c))
        (fun r ↦ grade c (PowIndex.get ((p c).length (m c)) (w c).1 r))) ∧
      (Nonempty (∀ c, Coord c) → Function.Surjective label) ∧
      (∀ g w c, ((system.move g w) c).1 = PowIndex.reindex (g c).symm (w c).1) ∧
      ∀ g : ∀ c, Equiv.Perm (Fin ((p c).length (m c))),
        ∃ F : ∀ i, P.V i ≃ₗ[K] P.V i,
        ∃ perm : Equiv.Perm (∀ c, Coord c),
          PiTensorProduct.map (fun i ↦ (F i).toLinearMap) P.t = P.t ∧
          (∀ w c, (perm w c).1 = PowIndex.reindex (g c).symm (w c).1) ∧
          (∀ w, F 2 (kronFinModePiBasis k S 2 factorBasis w) =
            kronFinModePiBasis k S 2 factorBasis (perm w)) ∧
          (∀ w, label (perm w) = system.move g (label w)) := by
  classical
  dsimp only
  let S := fun c ↦ prescribedZPower (T c) (b c 2) (grade c) (p c) (m c)
  choose B label system hB hlabel hsurj hmove hfactor using
    (fun c ↦ mme_dwz_prescribed_Z_power_uniform_basis_shuffle
      (T c) (b c) (grade c) (p c) (m c))
  refine ⟨B, (fun w c ↦ label c (w c)), MME.DWZProductShuffle.productSystem system,
    hB, (fun w c ↦ hlabel c (w c)), ?_, ?_, ?_⟩
  · rintro ⟨w⟩ target
    choose preimage hpreimage using (fun c ↦ hsurj c ⟨w c⟩ (target c))
    exact ⟨preimage, funext hpreimage⟩
  · intro g w c
    exact hmove c (g c) (w c)
  · intro g
    choose E perm ht hp hb hl using (fun c ↦ hfactor c (g c))
    obtain ⟨F, hF, hFB⟩ := mme_kronFin_modewise_basis_automorphisms_preserve_tensor
      S 2 B E perm ht hb
    refine ⟨F, Equiv.piCongrRight perm, hF, ?_, hFB, ?_⟩
    · intro w c
      exact hp c (w c)
    · intro w
      funext c
      exact hl c (w c)
