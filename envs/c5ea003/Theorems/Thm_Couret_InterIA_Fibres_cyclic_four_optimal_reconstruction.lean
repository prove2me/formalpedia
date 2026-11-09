-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_optimal_reconstruction
-- name    : Couret.InterIA.Fibres.cyclic_four_optimal_reconstruction
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:44.959241+00:00
-- url     : https://prove2.me/theorems/5b7be36b-4b18-4424-8825-e1a738af0246
-- title:
--   Optimal reconstruction of cyclic four-support fibres
-- statement:
--   Let $n>0$, let $S\subseteq\mathbb Z/n\mathbb Z$ have four elements, and let $\mathcal F(S)$ consist of all four-sets with the same ordered-square counts. There exists $d\le2$, equal to the dimension of the binary affine direction of this fibre, with
--
--   $$|\mathcal F(S)|=2^d.$$
--
--   There are $d$ fixed membership probes whose answer vectors biject $\mathcal F(S)$ with $\{0,1\}^d$, and a decoder recovering every fibre member. The resulting fixed-query tree has depth exactly $d$ and is correct on the fibre. Every correct membership tree has depth at least $d$. This gives an optimal query scheme, including the case $d=0$.
-- source:
--   Alexandre Couret, Complete four-point convolution fibres and predictive observations on C12: supplementary proof archive, https://zenodo.org/records/23981750; archive Couret_Supplement_Fibres_Cayley_20261105.zip, SHA-256 a12dde197808771ce3beb81d9e6ff1ab2074db9b06695b6816b0f28adbe8be8b; file fibres/lean/OptimalReconstruction.lean, lines 32–51; source file SHA-256 1457b138661a3d14b47428659d147565f70f2bf4fc62982febb5f8ff25a3b478; theorem Couret.InterIA.Fibres.cyclic_four_optimal_reconstruction

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
import Theorems.Thm_Couret_InterIA_Fibres_MembershipTree_depth_lower_bound
import Theorems.Thm_Couret_InterIA_Fibres_MembershipTree_fixed_depth
import Theorems.Thm_Couret_InterIA_Fibres_MembershipTree_fixed_run
import Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fibre_card_pow_finrank
import Theorems.Thm_Couret_InterIA_Fibres_cyclic_four_fixed_probes
import Theorems.Thm_Couret_InterIA_Fibres_probeAnswers_bijective
import Theorems.Thm_Couret_InterIA_Fibres_probeDecode_correct
import Definitions.Def_Couret_MembershipDecisionTree_ec39964080f5

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

theorem cyclic_four_optimal_reconstruction (n : ℕ) (hn : 0 < n)
    (S : Finset (ZMod n)) (hS : S.card=4) :
    ∃ d : ℕ, d ≤ 2 ∧
      d=Module.finrank (ZMod 2) (cyclicFibreAffine n hn S hS).direction ∧
      (cyclicFourFibre n S).ncard=2^d ∧
      (∃ (q : Fin d → ZMod n) (decode : (Fin d → Bool) → Finset (ZMod n)),
        Function.Bijective (fun T : cyclicFourFibre n S => probeAnswers q T.val) ∧
        (∀ T ∈ cyclicFourFibre n S, decode (probeAnswers q T)=T) ∧
        (MembershipTree.fixed d q decode).depth=d ∧
        (MembershipTree.fixed d q decode).CorrectOn (cyclicFourFibre n S)) ∧
      (∀ tree : MembershipTree (ZMod n), tree.CorrectOn (cyclicFourFibre n S) → d ≤ tree.depth) := by sorry


end Couret.InterIA.Fibres
