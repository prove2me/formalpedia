-- Prove2me | solution 1 for Catalog.UniformDial.discordanceMass_eq_zero_iff_comonotone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:19:24.421568+00:00
-- url     : https://prove2.me/submissions/f59d2822-b0e6-4a31-8d12-a060ecef2677

-- Sol generated from Combinatorics/UniformDialRegimeHomotopy.lean
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
import Definitions.Def_Combinatorics_UniformDialRegimeHomotopy
/-
# Regime homotopy and the concordance budget of the yield dial

Second cycle of the `UniformDial` thread (see `Combinatorics.UniformDialDrawInvariance`
for the pairwise identity and the sign-invariance theorems).

Two structural questions are settled here.

**(1) What happens *between* two draw regimes?**  Interpolating linearly from a balanced
regime `p` to a genuinely unbalanced regime `q` gives a one-parameter family
`mixWeights p q t`.  `wcov_mix` shows the dial reading is an *exact quadratic* in `t`
with an explicit cross term, and `wcov_mix_ge` / `wcov_mix_ge_half_min` show that for a
comonotone population the reading along the whole homotopy never drops below
`½ · min(endpoint readings)`.  So the dial cannot be diluted *anywhere* on the path, not
merely at the two measured endpoints — a strictly stronger statement than comparing two
experiments.

**(2) How unbalanced may a draw be before the dial could break?**  `wcov_budget` bounds
the dial from below by `ε²·C − M²·Δ`, where `C` and `Δ` are the total concordant and
discordant pair masses of the *population* (regime-free quantities) and `[ε, M]` bounds
the regime's per-key mass.  `dial_pos_of_concordance_ratio` turns this into a triage
rule: the dial is positive in *every* regime whose mass ratio `κ = M/ε` satisfies
`κ² · Δ < C`.  Dilution is therefore impossible until the draw's conditioning number
exceeds an explicit population-determined threshold.
-/

open Finset

open Catalog.UniformDial

variable {ι : Type*} [Fintype ι]

/-! ### Homotopy between two draw regimes -/












/-! ### The concordance budget: how unbalanced can a draw get? -/




lemma discordanceMass_nonneg (x y : ι → ℝ) : 0 ≤ discordanceMass x y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _






open Catalog.UniformDial in
theorem solution(x y : ι → ℝ) :
    discordanceMass x y = 0 ↔ Comonotone x y := by
  constructor
  · intro h i j
    by_contra hij
    push_neg at hij
    have hterm : 0 < max (-((x i - x j) * (y i - y j))) 0 :=
      lt_max_of_lt_left (by linarith)
    have hpos : 0 < discordanceMass x y := by
      refine Finset.sum_pos' (fun a _ => Finset.sum_nonneg fun b _ => le_max_right _ _)
        ⟨i, Finset.mem_univ i, ?_⟩
      exact Finset.sum_pos' (fun b _ => le_max_right _ _) ⟨j, Finset.mem_univ j, hterm⟩
    linarith
  · intro h
    refine le_antisymm ?_ (discordanceMass_nonneg x y)
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    exact max_le (by linarith [h i j]) le_rfl
