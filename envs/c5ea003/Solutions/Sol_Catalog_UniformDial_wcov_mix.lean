-- Prove2me | solution 1 for Catalog.UniformDial.wcov_mix
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:19:26.744674+00:00
-- url     : https://prove2.me/submissions/b0dc2d6f-5daa-4e2c-b463-306a585a88f7

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


lemma mixWeights_total {p q : ι → ℝ} (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (t : ℝ) :
    ∑ i, mixWeights p q t i = 1 := by
  simp only [mixWeights]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp, hq]
  ring



private lemma sum_four_comb (f1 f2 f3 f4 : ι → ℝ) (a b c d : ℝ) :
    ∑ i, (a * f1 i + b * f2 i + c * f3 i + d * f4 i)
      = a * (∑ i, f1 i) + b * (∑ i, f2 i) + c * (∑ i, f3 i) + d * (∑ i, f4 i) := by
  simp [Finset.sum_add_distrib, Finset.mul_sum]







/-! ### The concordance budget: how unbalanced can a draw get? -/










open Catalog.UniformDial in
theorem solution{p q x y : ι → ℝ} (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (t : ℝ) :
    wcov (mixWeights p q t) x y
      = (1 - t) ^ 2 * wcov p x y + 2 * t * (1 - t) * crossTerm p q x y
        + t ^ 2 * wcov q x y := by
  have hmix := mixWeights_total hp hq t
  have h0 := wcov_eq_half_double_sum (p := mixWeights p q t) (x := x) (y := y) hmix
  have h1 := wcov_eq_half_double_sum (p := p) (x := x) (y := y) hp
  have h2 := wcov_eq_half_double_sum (p := q) (x := x) (y := y) hq
  have hcross : ∑ i, ∑ j, q i * p j * ((x i - x j) * (y i - y j))
      = ∑ i, ∑ j, p i * q j * ((x i - x j) * (y i - y j)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have inner : ∀ i, ∑ j, mixWeights p q t i * mixWeights p q t j * ((x i - x j) * (y i - y j))
      = (1 - t) ^ 2 * (∑ j, p i * p j * ((x i - x j) * (y i - y j)))
        + ((1 - t) * t) * (∑ j, p i * q j * ((x i - x j) * (y i - y j)))
        + (t * (1 - t)) * (∑ j, q i * p j * ((x i - x j) * (y i - y j)))
        + t ^ 2 * (∑ j, q i * q j * ((x i - x j) * (y i - y j))) := by
    intro i
    rw [← sum_four_comb]
    exact Finset.sum_congr rfl fun j _ => by simp only [mixWeights]; ring
  have expand : ∑ i, ∑ j, mixWeights p q t i * mixWeights p q t j * ((x i - x j) * (y i - y j))
      = (1 - t) ^ 2 * (∑ i, ∑ j, p i * p j * ((x i - x j) * (y i - y j)))
        + ((1 - t) * t) * (∑ i, ∑ j, p i * q j * ((x i - x j) * (y i - y j)))
        + (t * (1 - t)) * (∑ i, ∑ j, q i * p j * ((x i - x j) * (y i - y j)))
        + t ^ 2 * (∑ i, ∑ j, q i * q j * ((x i - x j) * (y i - y j))) := by
    rw [Finset.sum_congr rfl fun i _ => inner i, sum_four_comb]
  rw [expand, hcross, ← h1, ← h2] at h0
  simp only [crossTerm]
  linarith
