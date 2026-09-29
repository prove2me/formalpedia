-- Prove2me | solution 1 for Catalog.UniformDial.wcov_budget
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:19:26.2479+00:00
-- url     : https://prove2.me/submissions/d593d328-bf5d-4415-b744-d3d66b8c86a9

-- Sol generated from Combinatorics/UniformDialRegimeHomotopy.lean
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
import Definitions.Def_Combinatorics_UniformDialRegimeHomotopy
import Theorems.Thm_Catalog_UniformDial_wcov_eq_half_double_sum
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










open Catalog.UniformDial in
theorem solution{p x y : ι → ℝ} {ε M : ℝ} (hp : ∑ i, p i = 1) (hε : 0 ≤ ε)
    (hlo : ∀ i, ε ≤ p i) (hhi : ∀ i, p i ≤ M) :
    ε ^ 2 * concordanceMass x y - M ^ 2 * discordanceMass x y ≤ 2 * wcov p x y := by
  rw [wcov_eq_half_double_sum hp]
  have hrw : ε ^ 2 * concordanceMass x y - M ^ 2 * discordanceMass x y
      = ∑ i, ∑ j, (ε ^ 2 * max ((x i - x j) * (y i - y j)) 0
          - M ^ 2 * max (-((x i - x j) * (y i - y j))) 0) := by
    simp only [concordanceMass, discordanceMass]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hrw]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  set D := (x i - x j) * (y i - y j) with hD
  have hsplit : max D 0 - max (-D) 0 = D := by
    rcases le_total 0 D with hd | hd
    · rw [max_eq_left hd, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hd, max_eq_left (by linarith)]; ring
  have hmass_lo : ε ^ 2 ≤ p i * p j := by
    have := mul_le_mul (hlo i) (hlo j) hε (le_trans hε (hlo i))
    nlinarith
  have hmass_hi : p i * p j ≤ M ^ 2 := by
    have h1 : 0 ≤ p i := le_trans hε (hlo i)
    have h2 : 0 ≤ p j := le_trans hε (hlo j)
    nlinarith [hhi i, hhi j]
  have hc : 0 ≤ max D 0 := le_max_right _ _
  have hd : 0 ≤ max (-D) 0 := le_max_right _ _
  calc ε ^ 2 * max D 0 - M ^ 2 * max (-D) 0
      ≤ (p i * p j) * max D 0 - (p i * p j) * max (-D) 0 := by
        have h1 : ε ^ 2 * max D 0 ≤ (p i * p j) * max D 0 :=
          mul_le_mul_of_nonneg_right hmass_lo hc
        have h2 : (p i * p j) * max (-D) 0 ≤ M ^ 2 * max (-D) 0 :=
          mul_le_mul_of_nonneg_right hmass_hi hd
        linarith
    _ = p i * p j * D := by rw [← mul_sub, hsplit]
    _ = p i * p j * ((x i - x j) * (y i - y j)) := by rw [hD]
