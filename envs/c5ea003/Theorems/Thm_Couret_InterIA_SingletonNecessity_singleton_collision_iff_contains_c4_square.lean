-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_singleton_collision_iff_contains_c4_square
-- name    : Couret.InterIA.SingletonNecessity.singleton_collision_iff_contains_c4_square
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:22:31.785564+00:00
-- url     : https://prove2.me/theorems/c49e2915-3d80-4dd2-9953-8ca5458635a0
-- title:
--   Singleton-intersection square collisions characterize an embedded square of order four
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. For every abelian group $G$,
--
--   $$[\exists A,B\subseteq G:\ |A|=|B|=4,\ |A\cap B|=1,\ R_A=R_B]\iff[\exists\phi:(\mathbb Z/4\mathbb Z)^2\hookrightarrow G\text{ additive}].$$
--
--   No finiteness or cyclicity assumption on $G$ is made.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/FullNecessity.lean, lines 37–45; source file SHA-256 0cf350362495df380a95f93d0f74361540b30b45c3f7e0565988146968fb64d4; theorem Couret.InterIA.SingletonNecessity.singleton_collision_iff_contains_c4_square

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_AbelianBoundary_contains_c4_square_sufficient
import Theorems.Thm_Couret_InterIA_SingletonNecessity_contains_c4_square_of_matching
import Theorems.Thm_Couret_InterIA_SingletonNecessity_cross_count_cancellation
import Theorems.Thm_Couret_InterIA_SingletonNecessity_cross_encoding
import Theorems.Thm_Couret_InterIA_SingletonNecessity_exclusive_enumeration
import Theorems.Thm_Couret_InterIA_SingletonNecessity_fibreParity_of_collision
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixed_count_cancellation
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixed_encoding
import Theorems.Thm_Couret_InterIA_SingletonNecessity_normalize_singleton_collision
import Theorems.Thm_Couret_InterIA_SingletonNecessity_parity_relabel
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.Parity Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem singleton_collision_iff_contains_c4_square :
    (∃ A B : Finset G, A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      ∀ z, orderedSquare A z=orderedSquare B z) ↔
    (∃ φ : G4 →+ G, Function.Injective φ) := by sorry


end Couret.InterIA.SingletonNecessity
