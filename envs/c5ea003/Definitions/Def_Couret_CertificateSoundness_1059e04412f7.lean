-- Prove2me | Definitions.Def_Couret_CertificateSoundness_1059e04412f7
-- name    : Couret_CertificateSoundness_1059e04412f7
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:56.732828+00:00
-- url     : https://prove2.me/theorems/194f193b-17b3-4cf5-a0f5-9ef070a0fcf5
-- title:
--   Evaluation of integer relation vectors
-- statement:
--   For six group elements $x_i$ in an abelian group, an integer relation vector $v$ evaluates by $$\operatorname{ev}_x(v)=\sum_{i=0}^{5}v_i x_i.$$ The additive homomorphism structure makes certificate linear combinations transport to group equalities. This is the semantic interface between finite integer certificates and arbitrary abelian-group configurations.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/CertificateSoundness.lean; source file SHA-256 10bfe9fce95e54024ac1f979cda844bfbd42adbb9a4bcc608954b4c55b77c9f0

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G]

def evaluation (x : Fin 6 → G) : Vec →+ G where
  toFun v := ∑ k, v k • x k
  map_zero' := by simp
  map_add' := by
    intro v w
    simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]







end Couret.InterIA.SingletonNecessity


