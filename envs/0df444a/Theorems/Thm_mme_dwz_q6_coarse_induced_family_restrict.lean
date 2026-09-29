-- Prove2me | Theorems.Thm_mme_dwz_q6_coarse_induced_family_restrict
-- name    : mme_dwz_q6_coarse_induced_family_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T10:42:20.204738+00:00
-- url     : https://prove2.me/theorems/a7cf70c5-c92a-4a2c-a3d6-fc724519b370
-- title:
--   Induced Table 2 component words restrict from the q=6 CW-square power
-- statement:
--   Let $K$ be a field. For each of $k$ retained words and each of $N$ tensor-square coordinates, choose one of the fifteen level-2 components in Duan--Wu--Zhou Table 2 order. Convert a label $s$ to the exact q=6 coarse constituent $C_s$: the first three are scalar matrix products; the six rectangular constituents have the appropriate orientation of volume $12=2q$; the three central constituents have the appropriate orientation of volume $38=q^2+2$; and the final three are the coupled constituent $D_6$ and its two cyclic mode rotations.
--
--   Assume the retained words are fully induced in the canonical five-graded support: if one independently chooses a retained word in each tensor mode and every coordinatewise mixed grade triple supports a nonzero CW-square block, then all three chosen words are the same. Then
--
--   $$
--   \bigoplus_{j<k}\;\bigotimes_{r<N} C_{s_{j,r}}\;\preceq\; (CW_6\otimes CW_6)^{\otimes N}.
--   $$
--
--   Thus an induced family of Table-2 coarse words gives an actual finite direct-sum restriction, not merely a component-count or scalar-value surrogate. This is the tensor-algebra bridge consumed after asymmetric collision pruning and before restricted-splitting substitutions and Hole-Lemma repair.
--
--   **Formalization Note** The theorem intentionally imposes no Table-2 multiplicity or cardinality bound. Those are separate combinatorial inputs. Its fifteen-entry constituent vector follows the published Table-2 row order exactly.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, PDF pp. 30--31 / printed pp. 29--30 (independent tensor-square component words and Lemma 4.1), PDF pp. 51--54 / printed pp. 50--53 (Section 6.1 asymmetric pruning and independent coarse triples), and PDF pp. 59--60 / printed pp. 58--59 (Section 6.3 and Table 2); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_permutation
open MME
open MME.DWZSquare
universe u

theorem mme_dwz_q6_coarse_induced_family_restrict
    {K : Type u} [Field K] {N k : ℕ}
    (component : Fin k → Fin N → Fin 15)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        (cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦
            (![shapeX (component (js i) r),
               shapeY (component (js i) r),
               shapeZ (component (js i) r)] : Fin 3 → Fin 5) i) ≠ 0) →
      ∃ j : Fin k, js = fun _ ↦ j) :
    let coarseComponent : Fin 15 → TensorObj K 3 :=
      ![MMObj K 1 1 1,
        MMObj K 1 1 1,
        MMObj K 1 1 1,
        MMObj K 1 1 12,
        MMObj K 1 1 12,
        MMObj K 12 1 1,
        MMObj K 1 12 1,
        MMObj K 12 1 1,
        MMObj K 1 12 1,
        MMObj K 1 1 38,
        MMObj K 38 1 1,
        MMObj K 1 38 1,
        coupledObj K 6,
        TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6),
        TensorObj.permObj cyclicPerm (coupledObj K 6)]
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        TensorObj.kronFin N (fun r ↦ coarseComponent (component j r))))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N) := by sorry
