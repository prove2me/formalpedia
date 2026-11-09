-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_MembershipTree_fixed_run
-- name    : Couret.InterIA.Fibres.MembershipTree.fixed_run
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:42.825622+00:00
-- url     : https://prove2.me/theorems/c1c9e2e1-7186-4c93-b53c-9482f9c54906
-- title:
--   A fixed membership tree returns its answer decoder
-- statement:
--   Let $\alpha$ have decidable equality, $d\ge0$, $q:\{0,\ldots,d-1\}\to\alpha$, and $D:\{0,1\}^d\to\operatorname{Finset}(\alpha)$ be any decoder. For every finite target set $T$, $$\operatorname{run}(\operatorname{fixed}(q,D),T)=D((1_{q_i\in T})_i).$$ Zero queries are allowed.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/MembershipDecisionTree.lean, lines 88–112; source file SHA-256 5e2fd5ee9c8bf68b4cdf22b33c6271447fa8b254d46cd000dc67939ef57a2581; theorem Couret.InterIA.Fibres.MembershipTree.fixed_run

import Definitions.Def_Couret_MembershipDecisionTree_ec39964080f5
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset



namespace MembershipTree

theorem fixed_run {α : Type*} [DecidableEq α] (d : ℕ) (q : Fin d → α)
    (decode : (Fin d → Bool) → Finset α) (T : Finset α) :
    (fixed d q decode).run T=decode (probeAnswers q T) := by sorry


end MembershipTree
end Couret.InterIA.Fibres
