-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_mixed_encoding
-- name    : Couret.InterIA.SingletonNecessity.mixed_encoding
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:17.073421+00:00
-- url     : https://prove2.me/theorems/a183d0a1-89e1-4c9f-8f5c-b30049d1f069
-- title:
--   A mixed matching has a permutation encoding
-- statement:
--   Let $G$ be an abelian group and $x:\{0,\ldots,5\}\to G$ satisfy the mixed-double relations. Suppose the left sum list followed by $2x_0$ is a permutation of the right sum list followed by $2x_3$. There is a permutation list $p$ of $0,\ldots,6$ with $$v(x)=0\qquad(v\in\mathcal R_{\mathrm{mixed}}(p)).$$
--
--   This encodes the augmented seven-term matching. The mixed double constraints are $2x_0=2x_1$, $2x_3=2x_4$, $2x_2=2x_5$. The unaugmented sum lists are the three entries and their three pair sums in each block $(0,1,2)$ and $(3,4,5)$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingEncoding.lean, lines 71–103; source file SHA-256 a0d826191571fb63dcc640fefffc281719b6b20eb83cbb257aa021d20bf19b83; theorem Couret.InterIA.SingletonNecessity.mixed_encoding

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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_basis
import Theorems.Thm_Couret_InterIA_SingletonNecessity_matching_rows_zero
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem mixed_encoding (x : Fin 6 → G) (hx : MixedDoubles x)
    (hp : (sumTermsLeft x ++ [x 0+x 0]).Perm (sumTermsRight x ++ [x 3+x 3])) :
    ∃ p : List ℕ, p.Perm (List.range 7) ∧
      ∀ v ∈ relations true p, evaluation x v=0 := by sorry


end Couret.InterIA.SingletonNecessity
