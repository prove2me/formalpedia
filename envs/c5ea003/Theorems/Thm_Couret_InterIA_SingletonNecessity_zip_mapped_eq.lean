-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_zip_mapped_eq
-- name    : Couret.InterIA.SingletonNecessity.zip_mapped_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:00:58.551592+00:00
-- url     : https://prove2.me/theorems/18b7205e-57d4-4b76-8edf-d6ff64134752
-- title:
--   Equal mapped lists agree at every zipped pair
-- statement:
--   Let $L$ and $R$ be lists over types $A$ and $B$, with maps $f:A\to C$ and $g:B\to C$. If their mapped lists are equal, then
--
--   $$(a,b)\in\operatorname{zip}(L,R)\Longrightarrow f(a)=g(b).$$
--
--   The statement does not require injective maps or distinct list entries.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/PermutationIndices.lean, lines 27–42; source file SHA-256 5efe3b1e4cab0d437f8cf9313def353f9b3c64d2ffe12333fea4edd2282f64f2; theorem Couret.InterIA.SingletonNecessity.zip_mapped_eq

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

theorem zip_mapped_eq {α β γ : Type*} (L : List α) (R : List β)
    (f : α → γ) (g : β → γ) (h : L.map f=R.map g) :
    ∀ a b, (a,b)∈L.zip R → f a=g b := by sorry


end Couret.InterIA.SingletonNecessity
