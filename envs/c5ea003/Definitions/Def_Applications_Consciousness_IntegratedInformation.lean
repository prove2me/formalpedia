-- Prove2me | Definitions.Def_Applications_Consciousness_IntegratedInformation
-- name    : Applications_Consciousness_IntegratedInformation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:42.51487+00:00
-- url     : https://prove2.me/theorems/53111caf-1208-4289-a68d-c4c092d20c6b
-- title:
--   Aether Catalog definitions — Applications_Consciousness_IntegratedInformation
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Consciousness.IntegratedInformation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Consciousness/IntegratedInformation.lean by skeleton subtraction
import Mathlib

/-! # Integrated Information Theory: Mathematical Foundations

A rigorous mathematical formalization of the core combinatorial skeleton of
Tononi's Integrated Information Theory (IIT).

In IIT, a *system* of `n` interacting elements is analyzed by considering all
the ways it can be cut into two interacting parts (its *bipartitions*).  Each
candidate cut `A` carries an *effective information* value `ei A ≥ 0` measuring
how much information is lost when the cut is made.  The integrated information

  Φ  :=  minimum over all nontrivial bipartitions of  ei A

is, by definition, the effective information of the *Minimum Information
Partition* (MIP): the cut that does the **least** damage to the system.  A
system whose MIP already destroys no information (`Φ = 0`) is *reducible* — it
is "really" two independent systems.

This file makes that skeleton precise over a finite element set `Fin n`, and
proves the foundational structural theorems: the MIP exists and realizes `Φ`,
`Φ` is the greatest lower bound of the effective-information landscape, `Φ` is
nonnegative, the reducibility characterization `Φ = 0 ↔ ∃` a zero cut, and a
monotonicity principle relating the integrated information of two systems.

This extends `Catalog/Speculative/Consciousness/CayleyDicksonLadder.lean`, which
models the *dimension* ladder of consciousness, by supplying the complementary
*information-theoretic* invariant `Φ` of a finite system.
-/

open Finset

namespace IIT

variable {n : ℕ}

/-- The set of **nontrivial bipartitions** of an `n`-element system: subsets `A`
of the elements that are neither empty nor the whole system.  Each such `A`
encodes the cut separating `A` from its complement. -/
def parts (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset.filter (fun A => A.Nonempty ∧ A ≠ univ)


-- !-- A singleton cut `{0}` is nonempty and (when `n ≥ 2`) proper, so it
-- witnesses that the bipartition landscape is nonempty. -- !--
/-- For a system with at least two elements there is always a nontrivial cut. -/
theorem parts_nonempty (h : 2 ≤ n) : (parts n).Nonempty := by
  simp +decide [parts]
  refine' ⟨{⟨0, by linarith⟩}, _⟩
  simp +decide
  exact ne_of_apply_ne Finset.card (by simp +decide [Finset.card_univ]; linarith)

-- !-- With `n ≤ 1` every subset is `∅` or the whole system, so no proper
-- nonempty cut exists; check the two cases `n = 0, 1`. -- !--

/-- An **IIT system** on `n` elements: an effective-information functional on
candidate cuts, assumed nonnegative (information loss is never negative). -/
structure System (n : ℕ) where
  /-- Effective information of the cut separating `A` from its complement. -/
  ei : Finset (Fin n) → ℝ
  /-- Effective information is never negative. -/
  ei_nonneg : ∀ A, 0 ≤ ei A

/-- **Integrated information** `Φ`: the minimum effective information over all
nontrivial bipartitions — i.e. the effective information at the Minimum
Information Partition. -/
noncomputable def Phi (S : System n) (h : 2 ≤ n) : ℝ :=
  ((parts n).image S.ei).min' ((parts_nonempty h).image S.ei)

-- !-- Φ ≤ ei A for every cut: Φ is the minimum of the finite, nonempty image of
-- `ei`, so `Finset.min'_le` applies to the image point `ei A`. -- !--

-- !-- The MIP exists: `min'_mem` places Φ inside the image of `ei`, and
-- `mem_image` extracts a witnessing partition realizing it. -- !--

-- !-- Φ is the *greatest* lower bound: any common lower bound `c` of the image
-- is below the minimum, by `Finset.le_min'`. -- !--

-- !-- Nonnegativity follows from `le_phi` with `c = 0` and `ei_nonneg`. -- !--

-- !-- Reducibility: Φ = 0 iff the MIP cut already loses no information.  Forward
-- uses `exists_MIP`; backward sandwiches `0 ≤ Φ ≤ ei A = 0`. -- !--

-- !-- Monotonicity: evaluate `T`'s MIP `A`; then Φ S ≤ ei_S A ≤ ei_T A = Φ T. -- !--

-- !-- If `A₀` is the common minimizer of both systems, then `Φ S = ei_S A₀` and
-- `Φ T = ei_T A₀` by antisymmetry (`phi_le_ei` and `le_phi`); conclude by
-- `hagree`. -- !--

end IIT


