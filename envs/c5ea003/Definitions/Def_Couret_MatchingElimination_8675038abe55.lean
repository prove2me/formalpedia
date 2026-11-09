-- Prove2me | Definitions.Def_Couret_MatchingElimination_8675038abe55
-- name    : Couret_MatchingElimination_8675038abe55
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:47.014945+00:00
-- url     : https://prove2.me/theorems/caa58d11-92de-4155-9b15-431708f8243b
-- title:
--   Distinct-label and matching-relation predicates
-- statement:
--   For six elements $x_0,\ldots,x_5$ of an abelian group, distinct labels means that $0,x_0,\ldots,x_5$ are pairwise distinct. The matching-relation predicate requires every integer relation in the supplied cross or mixed permutation system to evaluate to zero at these six elements.
--
--   These predicates separate abstract group hypotheses from the explicit finite matching certificates, so certificate elimination can be applied to any abelian group.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingElimination.lean; source file SHA-256 5d9c53994ff9dbf4384c58f156be2344b6607d814710b9fb230bc1739b8c8dbd

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
import Definitions.Def_Couret_MatchingCertificateData_656be71337d8
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
variable {G : Type*} [AddCommGroup G]





def DistinctLabels (x : Fin 6 → G) : Prop :=
  Function.Injective (fun i : Fin 7 => evaluation x (label i.val))

def RelationsHold (x : Fin 6 → G) (mixed : Bool) (p : List ℕ) : Prop :=
  ∀ v ∈ relations mixed p, evaluation x v = 0







end Couret.InterIA.SingletonNecessity


