-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_matching_rows_zero
-- name    : Couret.InterIA.SingletonNecessity.matching_rows_zero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:39.692209+00:00
-- url     : https://prove2.me/theorems/483d49f8-612f-426f-8fa4-aa84bf0c756e
-- title:
--   A matching of evaluations yields zero relation rows
-- statement:
--   Let $G$ be an abelian group, $x:\{0,\ldots,5\}\to G$, and $E_x(v)=\sum_i v_i x_i$ on $\mathbb Z^6$. Let $L,R$ be lists of vectors whose evaluation lists are permutations. There exists a list $p$ permuting $0,\ldots,|R|-1$ such that
--
--   $$E_x(v-R_{p_j})=0\quad\text{for each paired }(v,p_j)\in\operatorname{zip}(L,p).$$
--
--   The statement allows empty lists and repeated evaluated values.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingEncoding.lean, lines 20–37; source file SHA-256 a0d826191571fb63dcc640fefffc281719b6b20eb83cbb257aa021d20bf19b83; theorem Couret.InterIA.SingletonNecessity.matching_rows_zero

import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_permutation_indices
import Theorems.Thm_Couret_InterIA_SingletonNecessity_zip_mapped_eq
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem matching_rows_zero (x : Fin 6 → G) (L R : List Vec)
    (hp : (L.map (evaluation x)).Perm (R.map (evaluation x))) :
    ∃ p : List ℕ, p.Perm (List.range R.length) ∧
      ∀ v ∈ ((L.zip p).map fun (v,j) => v-R[j]!), evaluation x v=0 := by sorry






end Couret.InterIA.SingletonNecessity
