-- Prove2me | Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_normal_or_translation
-- name    : Couret.InterIA.NormalForm.even_cyclic_normal_or_translation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:52.267861+00:00
-- url     : https://prove2.me/theorems/a1bc9b96-ee10-4934-802d-22cd6bc6f3a1
-- title:
--   even cyclic normal or translation
-- statement:
--   For every integer $m>0$ and four-element subsets $S,T⊆R=ℤ/(2m)ℤ$ whose ordered-pair sum counts agree at every residue, either $S+u=T$ for some $u∈R$, or the pair $(S,T)$ has the following property, or the pair $(S,T+m)$ has that property: its intersection has cardinality two, and its two respective set differences are $\{a,a+m\}$ and $\{b,b+m\}$ for some $a,b∈R$. The alternatives need not be mutually exclusive.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/DisjointReduction.lean, lines 107–123; source file SHA-256 f25a642b4795363a49c52f9ac0f3b54862225a8fe7459401aab2e65462b4c8da; theorem Couret.InterIA.NormalForm.even_cyclic_normal_or_translation

import Definitions.Def_Couret_DisjointReduction_b47db5028f89
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_NormalForm_disjoint_cyclic_collision
import Definitions.Def_Couret_StableProjection_78f7ee270976

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem even_cyclic_normal_or_translation (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    (∃ u, S.image (fun x => x+u)=T) ∨
      Normal (m : ZMod (2*m)) S T ∨
      Normal (m : ZMod (2*m)) S (T.image (fun x : ZMod (2*m) => x+(m : ZMod (2*m)))) := by sorry


end Couret.InterIA.NormalForm
