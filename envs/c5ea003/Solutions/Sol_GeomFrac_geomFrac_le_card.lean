-- Prove2me | solution 1 for GeomFrac.geomFrac_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:06:42.803577+00:00
-- url     : https://prove2.me/submissions/69797757-b7ee-4af5-b705-ce29c679c93c

/-
# `GeomFrac.geomFrac_le_card`
Target `5fd0cdf2` (Open, not deprecated at draft time; re-read live immediately before submitting).

An ORDINARY PROOF, not a reduction: nothing is imported from `Theorems`, so `#print axioms solution`
carries no `sorryAx` and no axiom-audit module is required.

`geomFrac G` is the infimum of `c.total` over all fractional colourings `c`. An infimum is bounded
above by any member of its set, so it is enough to exhibit one colouring whose total is
`Fintype.card V`. The module already supplies it: `FracColoring.singleton G` puts weight `1` on
every one-element set and `0` elsewhere, so its total counts the singletons of `V`, of which there
are exactly `Fintype.card V`.

`csInf_le` additionally needs the range to be bounded below. It is, by `0`: every weight is
non-negative, hence so is every total.
-/
import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic

set_option autoImplicit false

open GeomFrac Finset in
/-- **The target, verbatim.** -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    geomFrac G ≤ (Fintype.card V : ℝ) := by
  classical
  -- the objective is bounded below by 0, since all weights are nonnegative
  have hbdd : BddBelow (Set.range (fun c : FracColoring G => c.total)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨c, rfl⟩
    exact Finset.sum_nonneg fun S _ => c.nonneg S
  -- the singleton colouring is feasible, and its total counts the one-element subsets of V
  have htot : (FracColoring.singleton G).total = (Fintype.card V : ℝ) := by
    have hsum : (FracColoring.singleton G).total
        = ∑ S : Finset V, (if S.card = 1 then (1 : ℝ) else 0) := rfl
    rw [hsum]
    first
    | · rw [Finset.sum_boole]
        norm_cast
        first
        | simp [Finset.filter_card_eq_one]
        | · have : (Finset.univ.filter fun S : Finset V => S.card = 1)
                = Finset.powersetCard 1 Finset.univ := by
              ext S; simp [Finset.mem_powersetCard, Finset.subset_univ]
            rw [this, Finset.card_powersetCard]
            simp
    | simp
  calc geomFrac G ≤ (FracColoring.singleton G).total :=
        csInf_le hbdd ⟨FracColoring.singleton G, rfl⟩
    _ = (Fintype.card V : ℝ) := htot
