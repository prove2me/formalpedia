-- Prove2me | solution 1 for MovingSofa.isMovingSofa_gerversSofaWith
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:35:30.897539+00:00
-- url     : https://prove2.me/submissions/df92e0e6-6d31-4986-8b13-d97ea8461cea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MovingSofa_Basic
import Theorems.Thm_MovingSofa_GerversSofa_ABphiThetaSpec_existsUnique
import Theorems.Thm_MovingSofa_uniqueParameterTuple_hasMotion

set_option autoImplicit false

open MovingSofa
open scoped EuclideanGeometry Real

theorem solution (A B phi theta : ℝ)
    (h : GerversSofa.ABphiThetaSpec A B phi theta) :
    ∃ m, IsMovingSofa (gerversSofaWith A B phi theta) m := by
  let q := GerversSofa.ABphiThetaSpec.existsUnique.choose
  have hq := GerversSofa.ABphiThetaSpec.existsUnique.choose_spec.1
  have hu := GerversSofa.ABphiThetaSpec.existsUnique.choose_spec.2
  have hparams : (A, B, phi, theta) = q := hu _ h
  have hmotion := MovingSofa.uniqueParameterTuple_hasMotion q hq hu
  have hA : A = q.1 := by simpa using congrArg Prod.fst hparams
  have hB : B = q.2.1 := by
    simpa using congrArg (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1) hparams
  have hphi : phi = q.2.2.1 := by
    simpa using congrArg (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.1) hparams
  have htheta : theta = q.2.2.2 := by
    simpa using congrArg (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.2) hparams
  rw [hA, hB, hphi, htheta]
  exact hmotion
