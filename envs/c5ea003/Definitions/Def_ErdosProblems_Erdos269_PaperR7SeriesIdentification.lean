-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
-- name    : ErdosProblems_Erdos269_PaperR7SeriesIdentification
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:15:59.167063+00:00
-- url     : https://prove2.me/theorems/3d2e33bb-1533-4ca4-ac56-639059d964a7
-- title:
--   PaperR7SeriesIdentification
-- statement:
--   Defines exponent triples, their smooth values and reciprocal-height kernel, the corresponding smooth-value subtype and equivalence, the paper's real scalar series, and its dyadic-shell indexing.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR7SeriesIdentification.lean#L1-L210
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Round 7: identify the original smooth-number series with the shell tsum

The distinction is material: a theorem about `dyadicShellTsumTailR235 0` is
not an end-to-end theorem about the paper's `S` until reindexing has been
proved. We build the exponent/smooth-number and shell/exponent equivalences,
prove summability, and identify the literal running-LCM series.

No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators

abbrev Exponent235 := ℕ × ℕ × ℕ

def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2

noncomputable def exponentKernel235 (e : Exponent235) : ℝ :=
  (threePrimeHeight 2 3 5 (exponentValue235 e) : ℝ)⁻¹

theorem exponentValue235_pos (e : Exponent235) : 0 < exponentValue235 e := by
  unfold exponentValue235 smooth3Val
  positivity

/-- Unique factorisation, with the three exponent coordinates retained. -/
theorem exponentValue235_factorization (e : Exponent235) :
    (exponentValue235 e).factorization =
      Finsupp.single 2 e.1 + Finsupp.single 3 e.2.1 + Finsupp.single 5 e.2.2 := by
  unfold exponentValue235 smooth3Val
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2),
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3),
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5)]

theorem exponentValue235_injective : Function.Injective exponentValue235 := by
  intro e f hef
  have h := congrArg Nat.factorization hef
  rw [exponentValue235_factorization, exponentValue235_factorization] at h
  have h2 := congrArg (fun f : ℕ →₀ ℕ => f 2) h
  have h3 := congrArg (fun f : ℕ →₀ ℕ => f 3) h
  have h5 := congrArg (fun f : ℕ →₀ ℕ => f 5) h
  simp at h2 h3 h5
  exact Prod.ext h2 (Prod.ext h3 h5)

/-- Positive smooth integers, counted once as numbers rather than as exponents. -/
def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}

noncomputable def exponentSmoothEquiv235 : Exponent235 ≃ Smooth235 where
  toFun e := ⟨exponentValue235 e, ⟨e, rfl⟩⟩
  invFun x := Classical.choose x.property
  left_inv e := exponentValue235_injective (Classical.choose_spec
    (show exponentValue235 e ∈ Set.range exponentValue235 from ⟨e, rfl⟩))
  right_inv x := Subtype.ext (Classical.choose_spec x.property)

/-- The original running-LCM summand at a smooth integer. -/
noncomputable def smoothReciprocal235 (x : Smooth235) : ℝ :=
  (smoothPrefixLcm 2 3 5 x.val : ℝ)⁻¹





/-- The scalar `S` as a sum over actual distinct smooth integers and actual LCMs. -/
noncomputable def paperSeries235 : ℝ := ∑' x : Smooth235, smoothReciprocal235 x

def shellIndex235 (e : Exponent235) : ℕ := Nat.log 2 (exponentValue235 e)

theorem exponent_mem_own_shell235 (e : Exponent235) :
    e ∈ dyadicSmoothShell235 (shellIndex235 e) := by
  apply mem_dyadicSmoothShell235_iff.mpr
  exact ⟨Nat.pow_log_le_self 2 (exponentValue235_pos e).ne',
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (exponentValue235 e)⟩

theorem shellIndex235_eq_of_mem {a : ℕ} {e : Exponent235}
    (he : e ∈ dyadicSmoothShell235 a) : shellIndex235 e = a := by
  obtain ⟨hlo, hhi⟩ := mem_dyadicSmoothShell235_iff.mp he
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi

/-- Each exponent vector belongs to exactly one finite dyadic shell. -/
noncomputable def shellExponentEquiv235 :
    (Σ a : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 a}) ≃ Exponent235 where
  toFun z := z.2.val
  invFun e := ⟨shellIndex235 e, ⟨e, exponent_mem_own_shell235 e⟩⟩
  left_inv z := by
    rcases z with ⟨a, ⟨e, he⟩⟩
    have ha := shellIndex235_eq_of_mem he
    change (⟨shellIndex235 e, ⟨e, exponent_mem_own_shell235 e⟩⟩ :
      Σ a : ℕ, {e : Exponent235 // e ∈ dyadicSmoothShell235 a}) = ⟨a, ⟨e, he⟩⟩
    cases ha
    rfl
  right_inv _ := rfl

















end ErdosProblems.Erdos269.PaperR7


