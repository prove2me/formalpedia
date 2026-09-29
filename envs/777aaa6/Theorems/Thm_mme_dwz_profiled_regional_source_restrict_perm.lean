-- Prove2me | Theorems.Thm_mme_dwz_profiled_regional_source_restrict_perm
-- name    : mme_dwz_profiled_regional_source_restrict_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T10:28:32.085629+00:00
-- url     : https://prove2.me/theorems/48d5e40b-36db-4d18-86a8-3c09cb4d468e
-- title:
--   DWZ regional source with rotated regions restricts to rotated prescribed-Z powers
-- statement:
--   This is Lemma B (`mme_dwz_profiled_regional_source_restrict`), with each region allowed its own mode orientation. That is what the six-region rotated frame of the Duan–Wu–Zhou construction needs.
--
--   Fix $R$ regions. Region $r$ carries the following data:
--
--   - a Stothers fourth-power block $(I_r, J_r, L_r) \in \{0,\dots,8\}^3$;
--   - a mode permutation $\sigma_r$;
--   - an integer Z-split profile $p_r$ with scale $m_r$;
--   - $n_r = |p_r|\cdot m_r$ fourth-power positions.
--
--   Its physical parent type is the rotated block type, $\mathrm{parent}(r)_i = \mathrm{cwFourthBlockType}(I_r,J_r,L_r)_{\sigma_r^{-1}(i)}$. Its kept (prescribed) mode is $\sigma_r(2)$, the physical mode carrying the constituent's original $Z$ mode.
--
--   Lay the $N = \sum_r n_r$ fourth-power slots out as $M = 4N$ atomic $CW_5$ factors, compatibly via `group` and `positions`, exactly as in Lemma B. Let $T$ be the all-mode projection of $CW_5^{\otimes M}$ onto the flat words kept by `dwzKeep`. In mode $i$, every region position's two half-word grades sum to $\mathrm{parent}(r)_i$. In the kept mode $\sigma_r(2)$, the left-half grade histogram is exactly $p_r$ scaled by $m_r$. Then
--
--   $$T \;\text{ is a restriction of }\; \bigotimes_{r=1}^{R} \mathrm{permObj}\big(\sigma_r,\ \mathrm{prescribedZPower}(C(I_r,J_r,L_r),\ p_r,\ m_r)\big).$$
--
--   Here `permObj σ` moves original mode $\sigma^{-1}(i)$ to physical mode $i$, and $C(I,J,L)$ is the $(I,J,L)$ constituent of $CW_5^{\otimes 4}$ with Z-grade given by its left square grade. Taking every $\sigma_r = 1$ recovers Lemma B.
--
--   This is the source identification step of the More-Asymmetry regional extraction applied to a six-region frame. It is a finite, exact statement about tensor restrictions, with no asymptotic claim.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite tensor statement; no asymptotic exponent claim.

import Definitions.Def_mme_dwz_profiled_regional_keep_data
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_permutation

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.CompleteSplit
  MME.StothersFourth MME.DWZRestrictedValue MME.DWZComponentRestriction
  MME.CompleteSplit.CWFourth MME.DWZProfiledRegional
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_dwz_profiled_regional_source_restrict_perm {K : Type u} [Field K] {R L M N : ℕ}
    (I J Lz : Fin R → Fin 9) (σ : Fin R → Equiv.Perm (Fin 3))
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (parent : Fin R → Fin 3 → ℕ)
    (hparent : ∀ r i, parent r i = (cwFourthBlockType (I r) (J r) (Lz r) ((σ r).symm i)).val)
    (keptMode : Fin R → Fin 3) (hkept : ∀ r, keptMode r = σ r 2)
    (n : Fin R → ℕ) (hn : n = fun r ↦ (p r).length (scale r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (2 - 1) = M)
    (group : Fin N ≃ (Σ r : Fin R, Fin (n r))) (hM : N * 4 = M)
    (hcompat : ∀ (u : Fin N) (s k : Fin 2),
      Fin.cast length (finProdFinEquiv (positions.symm ⟨(group u).1, (group u).2, s⟩, k)) =
        Fin.cast hM (finProdFinEquiv (u, finProdFinEquiv (s, k)))) :
    TensorObj.Restrict
      (ProfiledCW.tensor K (dwzKeep parent n keptMode p scale positions length))
      (kronFin R (fun r ↦ permObj (σ r)
        (prescribedZPower (cwFourthConstituent K 5 (I r) (J r) (Lz r))
          (constituentBasis K 5 (I r) (J r) (Lz r) 2)
          (fun a : LiftedCoarseCoordinate.{u} 5 (Lz r) ↦ cwSquarePairGrade 5 a.down.val.1)
          (p r) (scale r)))) := by sorry
