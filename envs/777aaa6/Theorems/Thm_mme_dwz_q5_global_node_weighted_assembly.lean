-- Prove2me | Theorems.Thm_mme_dwz_q5_global_node_weighted_assembly
-- name    : mme_dwz_q5_global_node_weighted_assembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T17:48:41.792255+00:00
-- url     : https://prove2.me/theorems/7d25cd7c-a814-4025-a0ce-1b618903df3a
-- title:
--   The q=5 global fourth-power node satisfies its partition-node assembly datum
-- statement:
--   Let $\tau$ be fixed and let $\rho$ be below the accepted extraction rate of the $q=5$ fourth-power construction. For every choice of per-child bases $v_c > 0$ and every positive integer $j$, there is a threshold beyond which the global (181st) node of the recursive ledger satisfies its partition-node assembly datum, with
--
--   $$\text{child weight}(c) = \mathrm{component}(c)\cdot D\cdot j, \qquad \text{parent weight} = 4\,(\mathrm{scale}\cdot D\cdot j),$$
--
--   where $D$ is the common denominator of the 45 released component profiles, $\mathrm{component}(c)$ their integer masses and $\mathrm{scale} = \sum_c \mathrm{component}(c)$. The parent is $\mathrm{CW}_5$ carried by a one-class Z profile of denominator $4$, so its prescribed power at multiplicity $m$ is $\mathrm{CW}_5^{\otimes 4m}$, i.e. the fourth-power object at length $m$; the children are the 45 canonical fourth-level constituents at their released profiles.
--
--   The content is that DWZ's global hashing step fits the recursive node interface. Given the 45 children synchronized at one common length $L_0 r$, choosing the scaling parameter $t = L_0 r j$ makes the accepted extraction's lengths land exactly on the required multiples: child $c$ occupies $L_0 r\,(\mathrm{component}(c) D j)$ positions and the parent $4 L_0 r\,(\mathrm{scale}\, D j)$, and those child lengths sum to the parent's, which is what "partition" means. The copies the extraction produces, at least $e^{\rho N(t)}$ of them, are exactly $(e^{\rho/4})^{L_0 r \cdot \text{parent weight}}$, and the matrix extraction across the 45 factors carries total weight $\big(\prod_c v_c^{\text{weight}(c)}\big)^{6 L_0 r}$.
--
--   Combined with the partition-node closure, this turns the accepted asymptotic extraction into a value for the fourth-power tensor computed from the 45 component values, with the rational exponents $\mathrm{component}(c)/\mathrm{scale}$ that the scalar ledger stores for that node.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_prescribed_z_finite_weighted_node_assembly_from_length
import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_CW_2376_address_block

open Filter MME MME.TensorObj MME.StothersFourth
  MME.DWZRestrictedValue MME.DWZComponentRestriction MME.CompleteSplit.CWFourth
  MME.DWZQ5ExactData MME.DWZFourthGlobalWitness MME.DWZQ5AsymptoticData
  Module BigOperators
open scoped Classical Topology

universe u

set_option autoImplicit false

theorem mme_dwz_q5_global_node_weighted_assembly {K : Type u} [Field K] {ιP : Type u}
    (parentBasis : Basis ιP K ((CWObj K 5).V 2))
    (parentProfile : IntegerZSplitProfile 1)
    (hden : parentProfile.denominator = 4)
    (rho : ℝ) (hrho : 0 ≤ rho) (hgap : rho < extractionRate)
    (tau : ℝ) (v : Fin 45 → ℝ) (hv : ∀ c, 0 < v c)
    (j : ℕ) (hj : 0 < j) :
    ∃ threshold : ℕ,
      PrescribedZFiniteWeightedNodeAssemblyFromLength
        (CWObj K 5)
        (fun c ↦ cwFourthConstituent K 5
          (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
        parentBasis (fun _ ↦ (0 : Fin 1)) parentProfile
        (fun c ↦ constituentBasis K 5
          (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
        (fun c ↦ fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
          cwSquarePairGrade 5 a.down.val.1)
        (fun c ↦ rawProfile c)
        (fun c ↦ component c * D * j) (4 * (scale * D * j))
        threshold tau (Real.exp (rho / 4)) v := by sorry
