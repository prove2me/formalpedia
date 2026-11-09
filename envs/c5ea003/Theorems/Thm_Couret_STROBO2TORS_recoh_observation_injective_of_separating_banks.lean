-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_observation_injective_of_separating_banks
-- name    : Couret.STROBO2TORS.recoh_observation_injective_of_separating_banks
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:04.278278+00:00
-- url     : https://prove2.me/theorems/5efd1050-39d3-4ec6-921f-7a3c421b0a39
-- title:
--   Two suitable character banks reconstruct triples from the square
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. Let $\alpha_i$ and $\beta_j$ be complex character banks indexed by arbitrary types $I,J$. Assume each $P_{\alpha_i}(S)\ne0$ on every triple; the common $\alpha$ kernel on $G[2]$ is trivial; every $\beta_j$ is trivial on $G[2]$; and the common $\beta$ kernel on $G[3]$ is trivial. Then
--
--   $$S\longmapsto(R_S,(P_{\alpha_i}(S))_i,(P_{\beta_j}(S))_j)\quad\text{is injective on three-element supports}.$$
--
--   Neither the group nor the index types need be finite.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohReconstruction.lean, lines 193–210; source file SHA-256 513a4060ff87ff1fa62542ec6ee81bb251e2eebfa05d359dd9f60f5fb115b612; theorem Couret.STROBO2TORS.recoh_observation_injective_of_separating_banks

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_reconstruction_of_separating_banks
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

theorem recoh_observation_injective_of_separating_banks
    {I J : Type*} (bank2 : I → AddChar G ℂ) (bank3 : J → AddChar G ℂ)
    (hnonzero : ∀ i : I, ∀ S : Finset G, S.card = 3 →
      recohSupportProbe (bank2 i) S ≠ 0)
    (hsep2 : ∀ u : G, u + u = 0 → (∀ i : I, bank2 i u = 1) → u = 0)
    (htrivial2 : ∀ j : J, ∀ u : G, u + u = 0 → bank3 j u = 1)
    (hsep3 : ∀ v : G, (v + v) + v = 0 → (∀ j : J, bank3 j v = 1) → v = 0) :
    Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohObservation (Sum.elim bank2 bank3) S.1) := by sorry


end Couret.STROBO2TORS
