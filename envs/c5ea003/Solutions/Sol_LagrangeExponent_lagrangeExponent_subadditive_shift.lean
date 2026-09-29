-- Prove2me | solution 1 for LagrangeExponent.lagrangeExponent_subadditive_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:33:32.079185+00:00
-- url     : https://prove2.me/submissions/48c41799-47b0-4cab-a42c-8c0d96679543

-- Sol generated from Novelty/LagrangeExponentGrowth.lean
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentCore
import Definitions.Def_Novelty_LagrangeExponentGrowth
import Theorems.Thm_LagrangeExponent_lagrangeExponent_concaveOn
import Theorems.Thm_LagrangeExponent_lagrangeExponent_critical
/-
# Consequences of concavity: cube–root growth, subadditivity, and the AM–GM equality case

Second research cycle on the Lagrange exponent `σ t = (1 + ∛(27 t - 1)) / 3`
(`Novelty.LagrangeExponentCore`, `Novelty.LagrangeExponentConcavity`).

Having established that `σ` is (strictly) concave exactly on `[1/27, ∞)`, we now extract
the structural consequences that concavity is *for*.

## Main results

* `lagrangeExponent_le_cbrt_add_third` / `cbrt_le_lagrangeExponent` — the **cube–root
  sandwich** `∛t ≤ σ t ≤ ∛t + 1/3` on the physical range (the upper bound holds on all of
  `ℝ`).  So the growth rate is a cube root up to an additive constant `≤ 1/3`, and the
  constant is optimal: the gap is `0` at `t = 1/27` and tends to `1/3`.
* `lagrangeExponent_subadditive_shift` — concavity anchored at the critical point yields
  `σ (s + t - 1/27) + 1/3 ≤ σ s + σ t`: merging two mass distributions is *cheaper* than
  running them separately, once the critical mass is accounted for exactly once.
* `lagrangeExponent_merge_finset` — the `n`-fold merging law, by induction over a finite
  family of admissible masses: `σ (∑ mᵢ - (n-1)/27) + (n-1)/3 ≤ ∑ σ (mᵢ)`.
* `lagrangeExponentOrderIso` — `σ` is an order isomorphism of `ℝ` with inverse the critical
  cubic, hence continuous and cofinal.
* `lagrangeExponent_mass_eq_third_iff` — the **equality case** of the mass bridge: a
  three–point distribution attains the critical exponent `1/3` iff it is uniform.  This
  shows the boundary `1/27` of the concavity region is attained by exactly one
  distribution, so the guard in `lagrangeExponent_concaveOn` is tight, not slack.
-/

open LagrangeExponent

open Set Filter

/-! ## Cube–root growth -/






/-! ## Subadditivity from concavity anchored at the critical mass -/




/-! ## `σ` as an order isomorphism of the mass line -/





/-! ## Equality case of the mass bridge -/





open LagrangeExponent in
theorem solution{s t : ℝ} (hs : 1 / 27 ≤ s) (ht : 1 / 27 ≤ t) :
    lagrangeExponent (s + t - 1 / 27) + 1 / 3 ≤ lagrangeExponent s + lagrangeExponent t := by
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ s + t - 2 / 27) with hzero | hD
  · -- degenerate case: both masses are exactly critical
    have hs' : s = 1 / 27 := by linarith
    have ht' : t = 1 / 27 := by linarith
    subst hs'; subst ht'
    norm_num [lagrangeExponent_critical]
  · have hDne : s + t - 2 / 27 ≠ 0 := ne_of_gt hD
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (s - 1 / 27) / (s + t - 2 / 27) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (t - 1 / 27) / (s + t - 2 / 27) := ⟨_, rfl⟩
    have ha0 : 0 ≤ a := ha ▸ div_nonneg (by linarith) hD.le
    have hb0 : 0 ≤ b := hb ▸ div_nonneg (by linarith) hD.le
    have hab : a + b = 1 := by
      rw [ha, hb, ← add_div, div_eq_one_iff_eq hDne]; ring
    have hmemX : s + t - 1 / 27 ∈ Ici (1 / 27 : ℝ) := mem_Ici.2 (by linarith)
    have hmemC : (1 / 27 : ℝ) ∈ Ici (1 / 27 : ℝ) := mem_Ici.2 le_rfl
    have h1 := lagrangeExponent_concaveOn.2 hmemX hmemC ha0 hb0 hab
    have h2 := lagrangeExponent_concaveOn.2 hmemX hmemC hb0 ha0 (by linarith)
    simp only [smul_eq_mul] at h1 h2
    have e1 : a * (s + t - 1 / 27) + b * (1 / 27) = s := by
      rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDne]; ring
    have e2 : b * (s + t - 1 / 27) + a * (1 / 27) = t := by
      rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hDne]; ring
    rw [e1] at h1
    rw [e2] at h2
    rw [lagrangeExponent_critical] at h1 h2
    have hb1 : b = 1 - a := by linarith
    rw [hb1] at h1 h2
    have hcancel : a * lagrangeExponent (s + t - 1 / 27)
        + (1 - a) * lagrangeExponent (s + t - 1 / 27) = lagrangeExponent (s + t - 1 / 27) := by
      ring
    linarith [h1, h2, hcancel]
