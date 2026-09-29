-- Prove2me | Theorems.Thm_mme_CW_atomic_fourth_component_grouping_projection_transport
-- name    : mme_CW_atomic_fourth_component_grouping_projection_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:55:00.286589+00:00
-- url     : https://prove2.me/theorems/ae8ae0cb-3999-46ad-8ce2-a2a1b2c706a2
-- title:
--   Atomic CW powers to grouped balanced fourth powers, with exact coordinate projections
-- statement:
--   Let $K$ be a field, let $q,N,k\ge 0$, and let $n_c\ge 0$ for $c\in\{0,\ldots,k-1\}$. Fix a bijection
--
--   $$
--   \pi:\{0,\ldots,N-1\}\longrightarrow\bigsqcup_{c=0}^{k-1}\{0,\ldots,n_c-1\}.
--   $$
--
--   Write $T=\mathrm{CW}_q^{\otimes 4N}$ and let $U$ be the ordered product of the powers $((\mathrm{CW}_q\otimes\mathrm{CW}_q)\otimes(\mathrm{CW}_q\otimes\mathrm{CW}_q))^{\otimes n_c}$. Both use their actual canonical tensor-product coordinate bases, denoted $B_i$ and $D_i$ in mode $i$.
--
--   There is a bijection $e$ of coordinate-word indices and mode linear equivalences $\Phi_i:T_i\to U_i$ such that
--
--   $$
--   \left(\bigotimes_i\Phi_i\right)T=U,
--   \qquad \Phi_i B_i(w)=D_i(e(w)).
--   $$
--
--   The index bijection is exact: if $t=\pi^{-1}(c,r)$, then
--
--   $$
--   e(w)_{c,r}=((w_{4t},w_{4t+1}),(w_{4t+2},w_{4t+3})).
--   $$
--
--   Consequently its total fourth-power grade is the sum of the four atomic grades, and its left-square grade is the sum of the first two atomic grades, exactly the `fourthLeftTag` of the corresponding atomic complete word.
--
--   Moreover, let $P_i$ be any predicates on atomic coordinate words, and define $Q_i(v)=P_i(e^{-1}(v))$. Denote simultaneous coordinate projection by brackets. The equivalences descend to the actual selected mode spaces, giving equivalences $f_i$ with
--
--   $$
--   \left(\bigotimes_i f_i\right)T[P]=U[Q].
--   $$
--
--   They preserve the projected basis vectors, and their ambient inclusions agree with $\Phi_i$. Thus arbitrary coarse, profile, and owner-exclusion filters can be transported without a coefficient-isolation assumption. The component labels retain every distinction encoded by the chosen partition; no different labels are identified.
--
--   Empty powers, zero component multiplicities, and $q=0$ are included. This is an explicit tensor-algebra normalization and projection theorem. It does not identify the grouped factors with prescribed constituent powers, prove block availability or positive nonhole mass, or establish a matrix-multiplication exponent bound.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S3.SS5 and https://arxiv.org/html/2210.10173v5#S5.SS1, Section 3.5 (consecutive-coordinate leveled partitions), Section 5.1, Definitions 5.2–5.4 (standard-form tensors, lower-level blocks, and complete split distributions). Explicit tensor/basis regrouping and coordinate-projection transport underlying these constructions; a derived formalization lemma, not a separately numbered source theorem.

import Theorems.Thm_mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_dwz_simultaneous_CW_projection_data

open MME MME.TensorObj MME.StothersFourth MME.DWZStep1Support MME.DWZSimultaneous
open Module PiTensorProduct TensorProduct BigOperators
universe u v
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem mme_CW_atomic_fourth_component_grouping_projection_transport {K : Type u} [Field K] (q : ℕ) {N k : ℕ}
    (count : Fin k → ℕ) (positions : Fin N ≃ (Σ c, Fin (count c))) :
    let T := (CWObj K q).kronPow (N*4)
    let U := kronFin k (fun c ↦ (cwFourthObj K q).kronPow (count c))
    let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N*4)
    let D := fun i ↦ kronFinModePiBasis k (fun c ↦ (cwFourthObj K q).kronPow (count c)) i
      (fun c ↦ kronPowModeWordBasis (cwFourthObj K q) i
        ((cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm) (count c))
    ∃ e : (Fin (N*4) → ULift.{u} (Fin (q+2))) ≃
        (∀ c, Fin (count c) →
          ULift.{u} ((Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2)))),
      (∀ w c r, let t := positions.symm ⟨c,r⟩
        (e w c r).down =
          (((w (finProdFinEquiv (t,0))).down, (w (finProdFinEquiv (t,1))).down),
           ((w (finProdFinEquiv (t,2))).down, (w (finProdFinEquiv (t,3))).down))) ∧
      ∃ Φ : ∀ i, T.V i ≃ₗ[K] U.V i,
        PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) T.t = U.t ∧
        (∀ i w, Φ i (B i w) = D i (e w)) ∧
        (∀ w c r, (cwFourthPairGrade q (e w c r).down).val =
          ∑ s : Fin 4, (label q 3 N w (positions.symm ⟨c,r⟩) s).val) ∧
        (∀ w c r, cwSquarePairGrade q (e w c r).down.1 =
          fourthLeftTag (label q 3 N w (positions.symm ⟨c,r⟩))) ∧
        ∀ P : Fin 3 → (Fin (N*4) → ULift.{u} (Fin (q+2))) → Prop,
          let Q := fun i w ↦ P i (e.symm w)
          ∃ f : ∀ i, (T.basisAllAllowedGrading B P).classOf i 0 ≃ₗ[K]
              (U.basisAllAllowedGrading D Q).classOf i 0,
            PiTensorProduct.map (fun i ↦ (f i).toLinearMap)
              (T.basisAllAllowedSubtensor B P).t = (U.basisAllAllowedSubtensor D Q).t ∧
            (∀ i w, f i ((T.basisAllAllowedGrading B P).blockProj i 0 (B i w)) =
              (U.basisAllAllowedGrading D Q).blockProj i 0 (D i (e w))) ∧
            ∀ i x, (f i x : U.V i) = Φ i (x : T.V i) := by sorry
