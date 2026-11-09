-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_permutation_indices
-- name    : Couret.InterIA.SingletonNecessity.permutation_indices
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:45.664912+00:00
-- url     : https://prove2.me/theorems/d23db7fa-3bc6-4998-b713-17df240fc3a7
-- title:
--   A list permutation can be indexed explicitly
-- statement:
--   Let $L,R$ be finite lists over an inhabited type. If $L$ is a permutation of $R$, there is a list $p$ that permutes $0,\ldots,|R|-1$ and $$L=[R_j:j\text{ occurs in }p].$$ Empty lists and repeated entries are allowed; out-of-range indexing has the type default but the permutation condition prevents it.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/PermutationIndices.lean, lines 14–25; source file SHA-256 5efe3b1e4cab0d437f8cf9313def353f9b3c64d2ffe12333fea4edd2282f64f2; theorem Couret.InterIA.SingletonNecessity.permutation_indices

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
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity

theorem permutation_indices {α : Type*} [Inhabited α] (L R : List α)
    (h : L.Perm R) :
    ∃ p : List ℕ, p.Perm (List.range R.length) ∧ L=p.map (fun j => R[j]!) := by sorry




end Couret.InterIA.SingletonNecessity
