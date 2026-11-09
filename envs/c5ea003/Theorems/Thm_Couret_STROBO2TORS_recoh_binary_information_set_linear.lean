-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_binary_information_set_linear
-- name    : Couret.STROBO2TORS.recoh_binary_information_set_linear
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:24.880888+00:00
-- url     : https://prove2.me/theorems/bc774b8d-3ecb-4eb2-a0cd-40dba2260ea7
-- title:
--   An injective binary bank contains an information set
-- statement:
--   For natural $r,k$, let $b_i$ be linear functionals on $\mathbb F_2^r$, $i<k$, whose joint evaluation is injective. There is an injective selection $p:\{0,\ldots,r-1\}\to\{0,\ldots,k-1\}$ such that $$x\mapsto(b_{p(j)}(x))_{j<r}$$ is surjective onto $\mathbb F_2^r$. Zero-dimensional cases are included.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohInformationSet.lean, lines 75–117; source file SHA-256 2c995fdd3163c7d085d3e54cdc03e3de75d6531a6e78bbfae2a5598e0da70298; theorem Couret.STROBO2TORS.recoh_binary_information_set_linear

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_spanning_subbank_preserves_injectivity
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false

/-!
RECOH: information-set extraction for a family of linear coordinate probes.

The general independent-subfamily theorem is standard linear algebra:
retain an independent subfamily spanning the original coordinate forms.
For a binary r-dimensional coordinate space, injectivity implies that
precisely r extracted coordinates suffice. These are not additional
conditions on the bank. Converting arbitrary additive binary characters
to linear forms is a separate interface.
-/

namespace Couret.STROBO2TORS

universe u

theorem recoh_binary_information_set_linear
    (r k : ℕ)
    (bank : Fin k → Module.Dual (ZMod 2) (Fin r → ZMod 2))
    (hinj : Function.Injective
      (fun x : Fin r → ZMod 2 => fun i : Fin k => bank i x)) :
    ∃ (pivot : Fin r → Fin k),
      Function.Injective pivot ∧
      Function.Surjective
        (fun x : Fin r → ZMod 2 =>
          fun j : Fin r => bank (pivot j) x) := by sorry


end Couret.STROBO2TORS
