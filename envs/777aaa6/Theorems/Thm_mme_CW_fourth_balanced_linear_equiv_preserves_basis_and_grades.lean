-- Prove2me | Theorems.Thm_mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades
-- name    : mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:22:37.620389+00:00
-- url     : https://prove2.me/theorems/09035131-2055-4836-85f5-8dee5729a34e
-- title:
--   Balanced CW fourth-power equivalence with exact basis and grade preservation
-- statement:
--   Let $K$ be any field and $q\ge0$. Let $T=\mathrm{CW}_q$, let $T^{\otimes4}$ use the recursive tensor-power convention, and let
--   $$
--   T_{\mathrm{bal}}=(T\otimes T)\otimes(T\otimes T).
--   $$
--   There are linear equivalences $\Phi_i$ between the corresponding mode spaces, for $i\in\{\mathrm X,\mathrm Y,\mathrm Z\}$, such that
--   $$
--   (\Phi_{\mathrm X}\otimes\Phi_{\mathrm Y}\otimes\Phi_{\mathrm Z})
--   (T^{\otimes4})=T_{\mathrm{bal}}.
--   $$
--   If $b_i^{\otimes4}(a)$ is the canonical word-basis vector indexed by $a=(a_0,a_1,a_2,a_3)$, then
--   $$
--   \Phi_i\bigl(b_i^{\otimes4}(a)\bigr)
--   =b_i^{\mathrm{bal}}\bigl((a_0,a_1),(a_2,a_3)\bigr).
--   $$
--   Here every $a_j\in\{0,\ldots,q+1\}$, and the balanced basis is the literal tensor product of the two canonical square bases.
--
--   Write $\gamma_q(0)=0$, $\gamma_q(q+1)=2$, and $\gamma_q(a)=1$ for the remaining coordinates. This exact router preserves both the total fourth-power grade and the left-square grade:
--   $$
--   \Gamma\bigl((a_0,a_1),(a_2,a_3)\bigr)
--   =\sum_{j=0}^{3}\gamma_q(a_j),\qquad
--   \Lambda(a_0,a_1)=\sum_{j=0}^{1}\gamma_q(a_j).
--   $$
--   Thus the map retains the lower-level block label needed to transport prescribed Z-split profiles, rather than merely the total coarse grade. The result includes $q=0$ and has no restriction on the field characteristic. It is the four-factor basis-aware regrouping step; it does not yet regroup arbitrary owner positions or identify prescribed-profile products.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S3.SS5 and https://arxiv.org/html/2210.10173v5#S5.SS1, Section 3.5 (leveled partitions and consecutive-coordinate grade sums), and Section 5.1, Definitions 5.2–5.3 (standard-form tensors and lower-level blocks). Explicit four-factor tensor-algebra regrouping underlying these definitions; not a separately numbered source theorem.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME MME.TensorObj MME.StothersFourth MME.DWZStep1Support
open Module PiTensorProduct TensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades {K : Type u} [Field K] (q : ℕ) :
    ∃ Φ : ∀ i, ((CWObj K q).kronPow 4).V i ≃ₗ[K] (cwFourthObj K q).V i,
      PiTensorProduct.map (fun i => (Φ i).toLinearMap) ((CWObj K q).kronPow 4).t =
        (cwFourthObj K q).t ∧
      (∀ i (w : Fin 4 → ULift.{u} (Fin (q + 2))),
        Φ i (kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) 4 w) =
        cwFourthCanonicalBasis K q i
          (((w 0).down, (w 1).down), ((w 2).down, (w 3).down))) ∧
      ∀ w : Fin 4 → ULift.{u} (Fin (q + 2)),
        (cwFourthPairGrade q
          (((w 0).down, (w 1).down), ((w 2).down, (w 3).down))).val =
          ∑ r : Fin 4, (cwSquareCoordGrade q (w r).down).val ∧
        (cwSquarePairGrade q ((w 0).down, (w 1).down)).val =
          ∑ r : Fin 2, (cwSquareCoordGrade q (w (Fin.castAdd 2 r)).down).val := by sorry
