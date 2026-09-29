-- Prove2me | Theorems.Thm_mme_dwz_canonical022_prescribed_z_MM_restriction
-- name    : mme_dwz_canonical022_prescribed_z_MM_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T06:35:11.323721+00:00
-- url     : https://prove2.me/theorems/cafeafd9-0247-4024-8865-8ee09f237295
-- title:
--   Canonical 022 prescribed-Z powers extract their exact surviving scalar-product dimension
-- statement:
--   Let $T_{0,2,2}$ be the literal canonical $(0,2,2)$ component of the square of the Coppersmith–Winograd tensor, over any field and for any natural parameter $q$. Fix a rational Z-split profile with positive integer denominator $d$ and counts $c_0,c_1,c_2$ summing to $d$. At every compatible power $n=dm$, retain exactly those canonical Z-coordinate words having $mc_a$ positions of left fine grade $a$ for each $a\in\{0,1,2\}$. Let $D$ be the number of these retained canonical words. Then the matrix-multiplication tensor $\langle1,1,D\rangle$ restricts from this very prescribed-Z power of $T_{0,2,2}$. The source basis is the canonical coarse-class subset basis, and the profile is measured by the actual left CW grade. The theorem does not replace the source by its unrestricted power or by an assumed tensor-value bound. It includes zero powers, $q=0$, and empty retained sets. The closed multinomial-times-$q$ formula for $D$ is a separate counting presentation, not a premise or a claimed conclusion here.
-- source:
--   Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 (28 November 2023), https://arxiv.org/abs/2210.10173v5, Definition 3.9 (printed p.23), Section 6.3 (printed p.59), and Section 7.3 following Lemma 7.14 (printed pp.71–72). Local pinned primary source research/papers/2022_asymmetric_hashing.pdf and research/text/2022_asymmetric_hashing.txt. This theorem is the finite actual canonical-tensor lower restriction underlying the prescribed-splitting boundary merging argument; it does not assert the limsup equivalence or an exponent bound.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.DWZFineChannel MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u

set_option autoImplicit false

theorem mme_dwz_canonical022_prescribed_z_MM_restriction
    (K : Type u) [Field K] (q : ℕ) (p : IntegerZSplitProfile 3) (m : ℕ) :
    let bZ : Basis (LiftedCoarsePair.{u} q 2) K ((Central022Block K q).V 2) :=
      (coarseClassBasis (K := K) q 2 2).reindex Equiv.ulift.symm
    let D := Nat.card {w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w}
    TensorObj.Restrict (MMObj K 1 1 D)
      (prescribedZPower (Central022Block K q) bZ LiftedCoarsePair.leftGrade p m) := by sorry
