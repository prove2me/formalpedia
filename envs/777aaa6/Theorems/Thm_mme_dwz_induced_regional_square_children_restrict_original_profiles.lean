-- Prove2me | Theorems.Thm_mme_dwz_induced_regional_square_children_restrict_original_profiles
-- name    : mme_dwz_induced_regional_square_children_restrict_original_profiles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T15:53:57.759316+00:00
-- url     : https://prove2.me/theorems/63a3ea75-ae81-401b-8bd7-10f2cb0928f4
-- title:
--   Induced square-child families restrict original projected regional parents simultaneously
-- statement:
--   Let $K$ be a field and $q,R,k\ge0$. In each region $r$, choose an actual canonical fourth-power CW constituent $T_{I_r,J_r,L_r}$, its original integer prescribed split profile $p_r$ with counts $p_{r,a}$, and scale $m_r$. Set $N_r=\operatorname{length}(p_r,m_r)$ and
--   $$
--   A_r=T_{I_r,J_r,L_r}^{\otimes N_r}[p_r].
--   $$
--   Choose a mode permutation $\sigma_r$; physical mode $i$ of $\sigma_r A_r$ is old mode $\sigma_r^{-1}(i)$.
--
--   For each owner $j<k$ and position $t<N_r$, prescribe left and right square grade triples $s_{j,r,t},u_{j,r,t}\in\{0,\ldots,4\}^3$. Assume their modewise sums equal $(I_r,J_r,L_r)$ and that every owner's left Z histogram is the unchanged parent profile:
--   $$
--   \#\{t:s_{j,r,t,Z}=a\}=m_rp_{r,a}\qquad(a=0,\ldots,4).
--   $$
--   Assume the following finite induced-address condition. If independently chosen owners $j_X,j_Y,j_Z$ satisfy
--   $$
--   \sum_{h\in\{X,Y,Z\}}s_{j_{\sigma_r(h)},r,t,h}=4
--   \quad\text{for every region and position},
--   $$
--   then $j_X=j_Y=j_Z$.
--
--   Write $S_v$ for the actual canonical square constituent of grade $v$. Then there is a simultaneous tensor restriction
--   $$
--   \bigotimes_{r<R}\sigma_r A_r
--   \longrightarrow
--   \bigoplus_{j<k}\bigotimes_{r<R}\sigma_r
--   \left(\bigotimes_{t<N_r}(S_{s_{j,r,t}}\otimes S_{u_{j,r,t}})\right).
--   $$
--   The regional permutations act on the original already-projected parents, preserving their inherited filters. A single owner is used across every region in each extracted summand. The proof constructs the actual mode maps and derives cross-term vanishing from the publicly proved CW-square support; neither a tensor restriction nor coefficient isolation is a premise.
--
--   This includes empty products, zero multiplicities, $k=0$, and $q=0$; unsupported child grades may give zero summands. It supplies the simultaneous finite tensor step. It does not establish the size of the supplied induced family, group the factors into prescribed-child powers, or prove a component-value or matrix-multiplication exponent bound.
-- source:
--   Derived finite tensor realization for Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Sections 3.5 and 3.9 (leveled partitions and prescribed splitting), and Sections 7.1–7.2 (regional orientations and child extraction). The explicit finite sum-of-slot identities reuse the accepted proof of mme_induced_graded_address_blocks_restrict, submission 587bf2c5-23d9-4298-be60-6b43795b823d. The original parent filters and simultaneous heterogeneous regional assembly are established here; this theorem is not a value endpoint.

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_permutation

open MME MME.TensorObj MME.StothersFourth MME.CompleteSplit.CWFourth
  MME.DWZRestrictedValue
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_dwz_induced_regional_square_children_restrict_original_profiles
    {K : Type u} [Field K] (q R k : ℕ)
    (I J L : Fin R → Fin 9) (p : Fin R → IntegerZSplitProfile 5)
    (m : Fin R → ℕ) (σ : Fin R → Equiv.Perm (Fin 3))
    (sx sy : ∀ _j : Fin k, ∀ r : Fin R, Fin ((p r).length (m r)) → Fin 3 → Fin 5)
    (hsum : ∀ j r t i, (sx j r t i).val + (sy j r t i).val =
      (cwFourthBlockType (I r) (J r) (L r) i).val)
    (hprofile : ∀ j r a, (Finset.univ.filter
      (fun t : Fin ((p r).length (m r)) ↦ sx j r t 2 = a)).card = (p r).count a * m r)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r t,
        (sx (js (σ r 0)) r t 0).val + (sx (js (σ r 1)) r t 1).val +
          (sx (js (σ r 2)) r t 2).val = 4) →
      ∃ j, js = fun _ ↦ j) :
    TensorObj.Restrict
      (bigAdd (fun j : Fin k ↦ kronFin R (fun r ↦
        permObj (σ r) (kronFin ((p r).length (m r)) (fun t ↦
          kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx j r t))
            ((cwSquareCanonicalGrading K q).blockSubtensor (sy j r t)))))))
      (kronFin R (fun r ↦ permObj (σ r)
        (prescribedZPower (cwFourthConstituent K q (I r) (J r) (L r))
          (constituentBasis K q (I r) (J r) (L r) 2)
          (fun a : LiftedCoarseCoordinate.{u} q (L r) ↦ cwSquarePairGrade q a.down.val.1)
          (p r) (m r)))) := by sorry
