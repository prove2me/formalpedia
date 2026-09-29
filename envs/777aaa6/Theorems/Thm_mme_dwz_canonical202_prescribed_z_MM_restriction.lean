-- Prove2me | Theorems.Thm_mme_dwz_canonical202_prescribed_z_MM_restriction
-- name    : mme_dwz_canonical202_prescribed_z_MM_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:33:02.382337+00:00
-- url     : https://prove2.me/theorems/2e54dbae-7069-4a08-961c-202a3498d0f1
-- title:
--   Canonical 202 prescribed-Z powers restrict to exact matrix-multiplication tensors
-- statement:
--   Let $K$ be a field, $q,m\in\mathbb N$, and $p=(p_0,p_1,p_2;d)$ be an integer fine-$Z$ profile with $d>0$ and $p_0+p_1+p_2=d$. Let $D$ be the number of length-$dm$ words in the canonical coarse-grade-$2$ $Z$ basis having exactly $mp_a$ letters of left fine grade $a$. Then the literal canonical CW-square component satisfies the finite restriction
--   \[\langle D,1,1\rangle_K\preceq T_{202}(q)^{\otimes dm}[p].\]
--   The prescribed-$Z$ projection uses the explicit canonical basis and left fine grade. This is the $Z$-preserving $X/Y$ exchange counterpart of the canonical $022$ restriction. The result applies to arbitrary rational $202$ profiles, without assuming that cyclic permutations preserve the distinguished mode.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Section 6.3, canonical central components. Formal finite counterpart of public mme_dwz_canonical022_prescribed_z_MM_restriction, using the proved 202 all-word router fcfc36ba-3da3-4cf4-816b-4888877acbb6 and the paired 202 coordinate projectors. This oriented finite lemma is not separately numbered in the paper.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.DWZFineChannel MME.DWZComponentRestriction MME.DWZRestrictedValue Module
universe u
set_option autoImplicit false

theorem mme_dwz_canonical202_prescribed_z_MM_restriction
    (K : Type u) [Field K] (q : ℕ) (p : IntegerZSplitProfile 3) (m : ℕ) :
    let bZ : Basis (LiftedCoarsePair.{u} q 2) K ((Central202Block K q).V 2) :=
      (coarseClassBasis (K := K) q 2 2).reindex Equiv.ulift.symm
    let D := Nat.card {w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w}
    TensorObj.Restrict (MMObj K D 1 1)
      (prescribedZPower (Central202Block K q) bZ LiftedCoarsePair.leftGrade p m)  := by sorry
