-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_canonical_pair_admissibility_iff
-- name    : Couret.InterIA.Catalogue.Quarter.canonical_pair_admissibility_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:00.327207+00:00
-- url     : https://prove2.me/theorems/a16e530b-4346-482a-92db-97c9c172857e
-- title:
--   canonical pair admissibility iff
-- statement:
--   In ℤ/(4q)ℤ put A={0,q,x,x+2q}, B={0,q,x+q,x+3q}, and D={0,q,2q,3q}; these are sets, so repeated entries count once. For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. For every positive natural q and x∈ℤ/(4q)ℤ, the conjunction |A|=4, |B|=4 and Q(A,z)=Q(B,z) for every z∈ℤ/(4q)ℤ holds if and only if x∉D.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPatternConverse.lean, lines 58–67; source file SHA-256 41da6cd22f81baaf77052df26dcf8825ae5a0546a46be6b741b1b68fdb82f147; theorem Couret.InterIA.Catalogue.Quarter.canonical_pair_admissibility_iff

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_patterns_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternA_card_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_card_iff
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo

theorem canonical_pair_admissibility_iff (q : ℕ) (hq : 0 < q) (x : ZMod (4*q)) :
    (patternA q x).card=4 ∧ (patternB q x).card=4 ∧
      (∀ z, orderedSquare (patternA q x) z=orderedSquare (patternB q x) z) ↔
        x ∉ badParameters q := by sorry


end Couret.InterIA.Catalogue.Quarter
