-- Prove2me | Theorems.Thm_mme_dwz_profiled_regional_source_restrict
-- name    : mme_dwz_profiled_regional_source_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T07:04:50.822021+00:00
-- url     : https://prove2.me/theorems/99b86486-e08d-4c65-9b01-dad3eb25120e
-- title:
--   DWZ regional source is a restriction of the prescribed-Z product
-- statement:
--   Fix $R$ regions. Region $r$ has a Stothers fourth-power block $(I_r, J_r, L_r) \in \{0,\dots,8\}^3$, an integer Z-split profile $p_r$ with scale $m_r$, and $n_r = |p_r|\cdot m_r$ fourth-power positions (the profile's length at that scale). Its parent type is the block type, $\mathrm{parent}(r)_i = \mathrm{cwFourthBlockType}(I_r,J_r,L_r)_i$, and its kept mode is $Z$ ($i = 2$).
--
--   Lay the $N = \sum_r n_r$ fourth-power slots out as $M = 4N$ atomic $CW_5$ factors in two compatible ways:
--
--   - `group` : $\mathrm{Fin}\,N \simeq \Sigma_r\,\mathrm{Fin}\,n_r$ assigns each slot to a region position;
--   - `positions` : $\mathrm{Fin}\,L \simeq \mathrm{Position}(n)$ places the two half-words (each two atomic factors) of every region position.
--
--   The compatibility hypothesis says that half $s$ of slot $u$ consists exactly of atomic factors $4u + 2s$ and $4u + 2s + 1$.
--
--   Let $T$ be the all-mode projection of $CW_5^{\otimes M}$ onto the flat words kept by `dwzKeep`. In mode $i$, these are the words where, for every region position, the two half-word grades sum to $\mathrm{parent}(r)_i$. In the kept mode they must also have left-half grade histogram exactly $p_r$ scaled by $m_r$. Then
--
--   $$T \;\text{ is a restriction of }\; \bigotimes_{r=1}^{R} \mathrm{prescribedZPower}\big(C(I_r,J_r,L_r),\ p_r,\ m_r\big),$$
--
--   the Kronecker product over regions of the prescribed-Z powers of the constituents $C(I_r,J_r,L_r)$ of $CW_5^{\otimes 4}$, whose Z-mode grade is the left square grade.
--
--   This is the source identification step (Lemma B) of the More-Asymmetry regional construction. It is a finite, exact statement about tensor restrictions. It makes no asymptotic or exponent claim.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_profiled_regional_keep_data
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.CompleteSplit
  MME.StothersFourth MME.DWZRestrictedValue MME.DWZComponentRestriction
  MME.CompleteSplit.CWFourth MME.DWZProfiledRegional
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_dwz_profiled_regional_source_restrict {K : Type u} [Field K] {R L M N : ℕ}
    (I J Lz : Fin R → Fin 9)
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (parent : Fin R → Fin 3 → ℕ)
    (hparent : ∀ r i, parent r i = (cwFourthBlockType (I r) (J r) (Lz r) i).val)
    (keptMode : Fin R → Fin 3) (hkept : ∀ r, keptMode r = 2)
    (n : Fin R → ℕ) (hn : n = fun r ↦ (p r).length (scale r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (2 - 1) = M)
    (group : Fin N ≃ (Σ r : Fin R, Fin (n r))) (hM : N * 4 = M)
    (hcompat : ∀ (u : Fin N) (s k : Fin 2),
      Fin.cast length (finProdFinEquiv (positions.symm ⟨(group u).1, (group u).2, s⟩, k)) =
        Fin.cast hM (finProdFinEquiv (u, finProdFinEquiv (s, k)))) :
    TensorObj.Restrict
      (ProfiledCW.tensor K (dwzKeep parent n keptMode p scale positions length))
      (kronFin R (fun r ↦
        prescribedZPower (cwFourthConstituent K 5 (I r) (J r) (Lz r))
          (constituentBasis K 5 (I r) (J r) (Lz r) 2)
          (fun a : LiftedCoarseCoordinate.{u} 5 (Lz r) ↦ cwSquarePairGrade 5 a.down.val.1)
          (p r) (scale r))) := by sorry
