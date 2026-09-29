-- Prove2me | Theorems.Thm_mme_dwz_table2_grouped_kronFin_shuffle_automorphism
-- name    : mme_dwz_table2_grouped_kronFin_shuffle_automorphism
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:27:23.902385+00:00
-- url     : https://prove2.me/theorems/e51a5204-9db9-4041-998d-4b3170cb0432
-- title:
--   Grouped useful-block shuffles are literal automorphisms of the fifteen-factor DWZ standard tensor
-- statement:
--   Fix a field $K$, a scale $m$, and a permutation $g$ of the canonically grouped positions which preserves each of the fifteen Table-2 component fibers. Let $S_m$ be the ordered Kronecker product of the fifteen literal restricted component powers. Then there are modewise linear automorphisms $F_0,F_1,F_2$ of $S_m$ which fix its tensor exactly: $$\left(\bigotimes_{i=0}^{2}F_i\right)S_m=S_m.$$ Moreover, for every canonical grouped available-word basis vector $B_W$, its image under $F_2$ is another canonical basis vector $B_{W'}$, and the useful-block label of $W'$ is exactly the public shuffle of the useful-block label of $W$ by $g$: $$F_2(B_W)=B_{W'},\qquad \operatorname{block}(W')=g\cdot\operatorname{block}(W).$$ This is the literal fifteen-component linear realization required in Claim 5.9: it aligns the tensor automorphism with the same fine-label shuffle used by the Hole Lemma, rather than giving only an abstract tensor isomorphism.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, especially the common shuffle of available blocks and its linear realization in Claim 5.9, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_broken_standard_obj
import Definitions.Def_mme_dwz_table2_useful_block_shuffle_action
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kronFin_mode_pi_basis

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module

universe u

set_option autoImplicit false

theorem mme_dwz_table2_grouped_kronFin_shuffle_automorphism
    {K : Type u} [Field K] (m : ℕ)
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m))) :
    ∃ F : ∀ i : Fin 3,
        (TensorObj.kronFin 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m)).V i ≃ₗ[K]
        (TensorObj.kronFin 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m)).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin 15
            (fun s : Fin 15 ↦ restrictedComponentPower K s m)).t =
        (TensorObj.kronFin 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m)).t ∧
      ∀ W : GroupedAllowedWords.{u} m,
        ∃ W' : GroupedAllowedWords.{u} m,
          F 2 (TensorObj.kronFinModePiBasis 15
              (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
              (fun s ↦ restrictedComponentZBasis K s m) W) =
              TensorObj.kronFinModePiBasis 15
                (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
                (fun s ↦ restrictedComponentZBasis K s m) W' ∧
            groupedUsefulBlock m W' =
              MME.DWZTable2StandardForm.shuffleUsefulBlock m
                (groupedOuter (m := m)) g (groupedUsefulBlock m W) := by
  sorry
