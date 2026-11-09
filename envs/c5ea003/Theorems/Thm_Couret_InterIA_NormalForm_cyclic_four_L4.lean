-- Prove2me | Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4
-- name    : Couret.InterIA.NormalForm.cyclic_four_L4
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:42.623839+00:00
-- url     : https://prove2.me/theorems/2ee08efc-93a1-4cdc-b614-3498b3d4333c
-- title:
--   Cyclic four-point normal form
-- statement:
--   For every natural $n\ge4$ and four-element subsets $S,T\subseteq\mathbb Z/n\mathbb Z$ with equal ordered-pair sum counts everywhere, if no unit $u$ and residue $v$ satisfy $uS+v=T$, then $n$ is even and there is a residue $t$ equal to $0$ or the natural quotient $\lfloor n/2\rfloor$, such that, writing $T'=T+t$ and $h=\lfloor n/2\rfloor$ in $\mathbb Z/n\mathbb Z$, $|S\cap T'|=2$ and there exist residues $a,b$ with $S\setminus T'=\{a,a+h\}$ and $T'\setminus S=\{b,b+h\}$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/L4Assembly.lean, lines 30–49; source file SHA-256 963e8dd3e3584e7170596d25b739b90c527798bb137acf05581e70913cf1549c; theorem Couret.InterIA.NormalForm.cyclic_four_L4

import Definitions.Def_Couret_L4Assembly_154a326d9c14
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
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
import Theorems.Thm_Couret_InterIA_NormalForm_translation_is_affine
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres

theorem cyclic_four_L4 (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) :
    Even n ∧ ∃ t : ZMod n, (t=0 ∨ t=(n/2 : ℕ)) ∧
      Normal ((n/2 : ℕ) : ZMod n) S (T.image (fun x => x+t)) := by sorry




end Couret.InterIA.NormalForm
