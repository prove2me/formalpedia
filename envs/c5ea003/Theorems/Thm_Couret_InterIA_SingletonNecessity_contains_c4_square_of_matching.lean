-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_contains_c4_square_of_matching
-- name    : Couret.InterIA.SingletonNecessity.contains_c4_square_of_matching
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:19:45.21137+00:00
-- url     : https://prove2.me/theorems/2312931f-ec37-47b2-98c1-baa6e7a95d44
-- title:
--   A valid six- or seven-term matching forces an embedded square of order four
-- statement:
--   Let $G$ be an abelian group and let $0,x_0,\ldots,x_5$ be seven distinct elements. Write $L=[x_0,x_1,x_2,x_0+x_1,x_0+x_2,x_1+x_2]$ and $R=[x_3,x_4,x_5,x_3+x_4,x_3+x_5,x_4+x_5]$. Suppose either (i) $2x_i=2x_{i+3}$ for $i=0,1,2$, and a permutation of six positions matches $L$ termwise to $R$; or (ii) $2x_0=2x_1$, $2x_3=2x_4$, $2x_2=2x_5$, and a permutation of seven positions matches $L$ followed by $2x_0$ to $R$ followed by $2x_3$. Then
--
--   $$\exists\phi:(\mathbb Z/4\mathbb Z)^2\hookrightarrow G\quad\text{additive}.$$
--
--   The matching conditions are equalities of the indicated group-valued list entries.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/ConditionalNecessity.lean, lines 76–84; source file SHA-256 cb9bb017b413d40837c57c50cc3c78b5f8fc5f8253e41ffaffda5cd427f7047c; theorem Couret.InterIA.SingletonNecessity.contains_c4_square_of_matching

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_cross_matching_is_reverse
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixed_matching_impossible
import Theorems.Thm_Couret_InterIA_SingletonNecessity_reverse_relations_contains_c4_square
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]

theorem contains_c4_square_of_matching (x : Fin 6 → G) (hd : DistinctLabels x)
    (hm : (∃ p : List ℕ, p.Perm (List.range 6) ∧ RelationsHold x false p) ∨
      (∃ p : List ℕ, p.Perm (List.range 7) ∧ RelationsHold x true p)) :
    ∃ φ : G4 →+ G, Function.Injective φ := by sorry


end Couret.InterIA.SingletonNecessity
