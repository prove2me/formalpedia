-- Prove2me | Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
-- name    : Couret_RecohReconstruction_b9109c17baa8
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:46.620115+00:00
-- url     : https://prove2.me/theorems/3894aaa7-68c6-4028-8f74-ecc1238768f2
-- title:
--   Character-probe observations of a support
-- statement:
--   For a finite support $S$ and a complex additive character $\chi$, define $$P_\chi(S)=\sum_{x\in S}\chi(x).$$ A bank observation pairs the full ordered-square function with all its character probes: $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$. This is the semantic observation reconstructed by the decoder family.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohReconstruction.lean; source file SHA-256 513a4060ff87ff1fa62542ec6ee81bb251e2eebfa05d359dd9f60f5fb115b612

import Aesop
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

/-- One labelled Fourier coefficient of the support indicator. -/
def recohSupportProbe (chi : AddChar G ℂ) (S : Finset G) : ℂ :=
  ∑ x ∈ S, chi x



theorem recoh_support_probe_translate (chi : AddChar G ℂ) (S : Finset G) (u : G) :
    recohSupportProbe chi (translateSupport S u) = chi u * recohSupportProbe chi S := by
  classical
  unfold recohSupportProbe translateSupport
  rw [Finset.sum_image]
  · simp_rw [chi.map_add_eq_mul]
    rw [← Finset.sum_mul]
    ring
  · intro x hx y hy h
    exact add_right_cancel h









/-- The full labelled observation, with its fixed bank indexed independently
of the unknown support and of the observed square. -/
def recohObservation {I : Type*} (bank : I → AddChar G ℂ) (S : Finset G) :
    (G → ℕ) × (I → ℂ) :=
  (orderedSquare S, fun i => recohSupportProbe (bank i) S)



end Couret.STROBO2TORS


