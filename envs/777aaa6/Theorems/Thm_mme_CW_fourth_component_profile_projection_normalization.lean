-- Prove2me | Theorems.Thm_mme_CW_fourth_component_profile_projection_normalization
-- name    : mme_CW_fourth_component_profile_projection_normalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T09:14:16.279355+00:00
-- url     : https://prove2.me/theorems/e9fa2224-9e4f-4e09-aa66-d0a5988c16fb
-- title:
--   Canonical fourth-power coarse/profile projections are actual prescribed-Z products
-- statement:
--   Let $K$ be a field, $q\geq0$, and let $c$ range over a finite ordered set $[k]=\{0,\ldots,k-1\}$. For each label choose a coarse triple $(I_c,J_c,L_c)\in\{0,\ldots,8\}^3$, a positive integer denominator $d_c$, nonnegative integer counts $p_c(a)$ for $a\in\{0,\ldots,4\}$ satisfying $\sum_a p_c(a)=d_c$, and a multiplicity $m_c\geq0$. Put
--   $$
--   n_c=d_cm_c,\qquad \mu_c(a)=p_c(a)m_c.
--   $$
--   Labels are retained separately even if their coarse triples coincide.
--
--   Let $T=\mathrm{CW}_q^{\otimes4}$ with its literal balanced parenthesization and canonical coordinate basis. A coordinate is $x=((x_0,x_1),(x_2,x_3))$. Write $g(x)$ for its total CW grade and $\lambda(x)$ for the grade of the left square $(x_0,x_1)$. Let $C_c=T_{I_c,J_c,L_c}$ be the actual canonical constituent, with its canonical subset basis in each mode.
--
--   Consider the ordered tensor product $R=\bigotimes_{c<k}T^{\otimes n_c}$. Its mode-$i$ basis words are tuples $w=(w_c)$ of words of length $n_c$. Define $P_i(w)$ by requiring every letter of $w_c$ to have grade $I_c$, $J_c$, or $L_c$, according as $i=X,Y,Z$. In mode $Z$ impose the additional exact constraints
--   $$
--   \#\{t<n_c:\lambda(w_c(t))=a\}=\mu_c(a)
--   \qquad(c<k,\ 0\leq a\leq4).
--   $$
--   Let $R[P]$ be this simultaneous coordinate projection.
--
--   For each $c$, let $S_c$ be the actual prescribed-Z power of $C_c^{\otimes n_c}$, formed with its public canonical Z basis and the literal left-square grade. Thus only the Z words are filtered by the preceding exact counts. Then there are mode linear equivalences
--   $$
--   F_i:(R[P])_i\simeq_K\left(\bigotimes_{c<k}S_c\right)_i
--   $$
--   with the exact tensor identity
--   $$
--   (F_X\otimes F_Y\otimes F_Z)R[P]
--   =\bigotimes_{c<k}S_c.
--   $$
--
--   The theorem also supplies canonical selected bases $\beta_{c,i}$ of the actual mode spaces of $S_c$. Their inclusions into $(C_c^{\otimes n_c})_i$ are exactly the canonical recursive word-basis vectors. The index set is all canonical constituent words in X and Y, and the exact-profile canonical constituent words in Z. If $v_c$ is such a word and $\iota(v_c)$ forgets its coarse-fiber membership proofs, the normalization satisfies
--   $$
--   F_i\!\left(\pi_{P,i} B_{R,i}\big((\iota(v_c))_c\big)\right)
--   =\bigotimes_{c<k}\beta_{c,i}(v_c).
--   $$
--   The formal statement gives this router between ordinary position-indexed words and recursive tensor-power words exactly.
--
--   This is an actual tensor-and-basis normalization, with no realization or restriction premise. It includes empty products, zero multiplicities, and empty selected spaces. It does not assert nonemptiness, profile attainability, ownership isolation, a hole-repair bound, or a new matrix-multiplication exponent. The algebraic identity holds for arbitrary coarse triples; the usual supported level-three components additionally satisfy $I_c+J_c+L_c=8$.
-- source:
--   Derived concrete basis-aware normalization for Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 (28 November 2023), https://arxiv.org/html/2210.10173v5#S5.SS1, Section 5.1, Definitions 5.2–5.4; compare the identification with standard form in Section 6.1. This theorem supplies the literal fourth-power canonical tensor and basis maps underlying that identification, rather than a separately numbered statement of the paper. The algebraic formulation deliberately permits repeated full labels, zero multiplicities, arbitrary coarse triples, and q=0; supported positive-multiplicity data recover the usual level-three standard-form setting.

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_complete_split_cw_fourth_label_certificate
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_complete_split_profile_projection
import Theorems.Thm_mme_kronFin_family_mode_map_selected_basis
import Theorems.Thm_mme_kronFin_all_mode_projection_factorization
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Basis.Submodule

open MME MME.TensorObj Module PiTensorProduct
open scoped Classical

universe u
set_option autoImplicit false
set_option maxHeartbeats 1000000


open MME.DWZComponentRestriction MME.DWZRestrictedValue MME.StothersFourth
open MME.CompleteSplit.CWFourth

theorem mme_CW_fourth_component_profile_projection_normalization
    {K : Type u} [Field K] {k : ℕ} (q : ℕ)
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ) :
    let n := fun r ↦ (p r).length (m r)
    let T := cwFourthObj K q
    let C := fun r ↦ cwFourthConstituent K q (I r) (J r) (L r)
    let b := fun i ↦ (cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm
    let B := fun r i ↦ kronPowModeWordBasis T i (b i) (n r)
    let c := fun r ↦ constituentBasis K q (I r) (J r) (L r)
    let A := fun r i ↦ kronPowModeBasis (C r) i (c r i) (n r)
    let grade := fun r (a : LiftedCoarseCoordinate.{u} q (L r)) ↦
      cwSquarePairGrade q a.down.val.1
    let X := fun r ↦ T.kronPow (n r)
    let S := fun r ↦ prescribedZPower (C r) (c r 2) (grade r) (p r) (m r)
    let P := fun r i (w : Fin (n r) → ULift.{u} (Coordinate q)) ↦
      (∀ t, cwFourthPairGrade q (w t).down = cwFourthBlockType (I r) (J r) (L r) i) ∧
      (i = 2 → ∀ a : Fin 5,
        (Finset.univ.filter
          (fun t : Fin (n r) ↦ cwSquarePairGrade q (w t).down.1 = a)).card =
            (p r).count a * m r)
    let Q := fun r (i : Fin 3)
      (w : PowIndex (LiftedCoarseCoordinate.{u} q
        (cwFourthBlockType (I r) (J r) (L r) i)) (n r)) ↦
      if h : i = 2 then prescribedZWord (grade r) (p r) (m r)
        (Eq.ndrec (motive := fun j : Fin 3 ↦ PowIndex (LiftedCoarseCoordinate.{u} q
          (cwFourthBlockType (I r) (J r) (L r) j)) (n r)) w h) else True
    let H := fun r ↦ ((C r).kronPow (n r)).basisZAllowedGrading
      (A r 2) (prescribedZWord (grade r) (p r) (m r))
    let BB := fun i ↦ kronFinModePiBasis k X i (fun r ↦ B r i)
    let G := (kronFin k X).basisAllAllowedGrading BB (fun i w ↦ ∀ r, P r i (w r))
    ∃ β : ∀ r i, Basis {w : PowIndex
          (LiftedCoarseCoordinate.{u} q (cwFourthBlockType (I r) (J r) (L r) i)) (n r) //
          Q r i w} K ((H r).classOf i 0),
      (∀ r i w, (β r i w : ((C r).kronPow (n r)).V i) = A r i w.val) ∧
      ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] (kronFin k S).V i,
        PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (G.blockSubtensor (fun _ ↦ 0)).t = (kronFin k S).t ∧
        ∀ i (w : ∀ r, Fin (n r) →
            LiftedCoarseCoordinate.{u} q (cwFourthBlockType (I r) (J r) (L r) i))
          (hw : ∀ r, Q r i (PowIndex.ofFun (n r) (w r))),
          F i (G.blockProj i 0 (BB i (fun r t ↦ ⟨(w r t).down.val⟩))) =
            kronFinModePiBasis k S i (fun r ↦ β r i)
              (fun r ↦ ⟨PowIndex.ofFun (n r) (w r), hw r⟩) := by sorry
