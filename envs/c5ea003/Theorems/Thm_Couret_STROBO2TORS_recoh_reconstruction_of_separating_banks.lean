-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_reconstruction_of_separating_banks
-- name    : Couret.STROBO2TORS.recoh_reconstruction_of_separating_banks
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:36.013173+00:00
-- url     : https://prove2.me/theorems/53b7a870-50f3-4df4-8574-916b20a9fea5
-- title:
--   Two separating primary banks reconstruct a triple
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Let banks $B_2=(\chi_i)$ and $B_3=(\psi_j)$ have arbitrary index types. Assume every $\chi_i$ has nonzero probe on every three-element support; their common kernel on $H$ is zero; every $\psi_j$ is trivial on $H$; and their common kernel on $K$ is zero. For three-element supports $S,T$, if $Q_S=Q_T$ and all readings of both banks agree, then $$S=T.$$ Finiteness of $G$ is not required.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohReconstruction.lean, lines 148–185; source file SHA-256 513a4060ff87ff1fa62542ec6ee81bb251e2eebfa05d359dd9f60f5fb115b612; theorem Couret.STROBO2TORS.recoh_reconstruction_of_separating_banks

import Aesop
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_normal_form
import Theorems.Thm_Couret_STROBO2TORS_recoh_third_probe_separates_exceptional
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH: reconstructing a cardinality-three support from its labelled ordered
square and a fixed bank of individual complex character coefficients.

The observation and the support cardinality are explicit. The classification
used below is the existing STROBO theorem, not an additional hypothesis.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_reconstruction_of_separating_banks
    {I J : Type*} (bank2 : I → AddChar G ℂ) (bank3 : J → AddChar G ℂ)
    (hnonzero : ∀ i : I, ∀ S : Finset G, S.card = 3 →
      recohSupportProbe (bank2 i) S ≠ 0)
    (hsep2 : ∀ u : G, u + u = 0 → (∀ i : I, bank2 i u = 1) → u = 0)
    (htrivial2 : ∀ j : J, ∀ u : G, u + u = 0 → bank3 j u = 1)
    (hsep3 : ∀ v : G, (v + v) + v = 0 → (∀ j : J, bank3 j v = 1) → v = 0)
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3)
    (hsquare : ∀ z : G, orderedSquare S z = orderedSquare T z)
    (hprobe2 : ∀ i : I, recohSupportProbe (bank2 i) S = recohSupportProbe (bank2 i) T)
    (hprobe3 : ∀ j : J, recohSupportProbe (bank3 j) S = recohSupportProbe (bank3 j) T) :
    S = T := by sorry






end Couret.STROBO2TORS
