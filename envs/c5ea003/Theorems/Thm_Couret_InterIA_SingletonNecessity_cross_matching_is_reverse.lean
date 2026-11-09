-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_cross_matching_is_reverse
-- name    : Couret.InterIA.SingletonNecessity.cross_matching_is_reverse
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:07:11.16197+00:00
-- url     : https://prove2.me/theorems/dd3ff05d-b9e6-46bf-8bc4-3b93225b118d
-- title:
--   Only reverse cross matching survives distinct labels
-- statement:
--   Let $G$ be an abelian group. Let $x_0,\ldots,x_5$ be nonzero pairwise distinct elements. Form $L=(x_0,x_1,x_2,x_0+x_1,x_0+x_2,x_1+x_2)$ and $R=(x_3,x_4,x_5,x_3+x_4,x_3+x_5,x_4+x_5)$. Let $p$ permute $0,\ldots,5$. Assume $2x_0=2x_3$, $2x_1=2x_4$, $2x_2=2x_5$ and $L_i=R_{p_i}$ for all six indices. Then
--
--   $$p=(5,4,3,2,1,0).$$
--
--   This isolates the surviving cross-matching pattern.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingElimination.lean, lines 43–48; source file SHA-256 5d9c53994ff9dbf4384c58f156be2344b6607d814710b9fb230bc1739b8c8dbd; theorem Couret.InterIA.SingletonNecessity.cross_matching_is_reverse

import Definitions.Def_Couret_MatchingElimination_8675038abe55
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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_certificate_sound
import Theorems.Thm_Couret_InterIA_SingletonNecessity_crossData_coverage
import Theorems.Thm_Couret_InterIA_SingletonNecessity_crossData_valid
import Definitions.Def_Couret_MatchingCertificateData_656be71337d8
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
variable {G : Type*} [AddCommGroup G]

theorem cross_matching_is_reverse (x : Fin 6 → G) (hd : DistinctLabels x)
    (p : List ℕ) (hp : p.Perm (List.range 6))
    (hr : RelationsHold x false p) : p=reversePerm := by sorry




end Couret.InterIA.SingletonNecessity
