-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_basis
-- name    : Couret.InterIA.SingletonNecessity.evaluation_basis
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:53:01.180551+00:00
-- url     : https://prove2.me/theorems/4a4ff7a4-06ea-415e-a476-333dcc5646e6
-- title:
--   Evaluation of a coordinate basis vector
-- statement:
--   Let $G$ be an abelian group and $x:\{0,\ldots,5\}\to G$. Define $E_x(v)=\sum_{i=0}^5v_i x_i$ for $v\in\mathbb Z^6$. For every coordinate $n<6$,
--
--   $$E_x(e_n)=x_n.$$
--
--   This identifies the abstract integral basis with the six group labels.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/CertificateSoundness.lean, lines 16–22; source file SHA-256 10bfe9fce95e54024ac1f979cda844bfbd42adbb9a4bcc608954b4c55b77c9f0; theorem Couret.InterIA.SingletonNecessity.evaluation_basis

import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
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

theorem evaluation_basis (x : Fin 6 → G) (n : Fin 6) :
    evaluation x (basis n.val) = x n := by sorry






end Couret.InterIA.SingletonNecessity
