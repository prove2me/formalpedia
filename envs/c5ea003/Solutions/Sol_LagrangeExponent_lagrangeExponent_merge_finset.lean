-- Prove2me | solution 1 for LagrangeExponent.lagrangeExponent_merge_finset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:34:55.998838+00:00
-- url     : https://prove2.me/submissions/18ef4e9c-0380-4ccf-9b7d-78ffed985d5b

-- Sol generated from Novelty/LagrangeExponentGrowth.lean
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentCore
import Definitions.Def_Novelty_LagrangeExponentGrowth
import Theorems.Thm_LagrangeExponent_lagrangeExponent_subadditive_shift
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


/-- Admissible masses have total mass at least `card / 27`. -/
lemma sum_ge_card_div_27 {ι : Type*} (T : Finset ι) (m : ι → ℝ)
    (hm : ∀ i ∈ T, (1 : ℝ) / 27 ≤ m i) : (T.card : ℝ) / 27 ≤ ∑ i ∈ T, m i := by
  have := Finset.card_nsmul_le_sum T m (1 / 27) hm
  simpa [nsmul_eq_mul, div_eq_mul_inv, mul_comm] using this


/-! ## `σ` as an order isomorphism of the mass line -/





/-! ## Equality case of the mass bridge -/





open LagrangeExponent in
theorem solution{ι : Type*} {T : Finset ι} (hT : T.Nonempty) (m : ι → ℝ)
    (hm : ∀ i ∈ T, (1 : ℝ) / 27 ≤ m i) :
    lagrangeExponent ((∑ i ∈ T, m i) - ((T.card : ℝ) - 1) / 27) + ((T.card : ℝ) - 1) / 3
      ≤ ∑ i ∈ T, lagrangeExponent (m i) := by
  revert hm
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro _
    simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one]
    norm_num
  | cons a s hnotmem hs ih =>
    intro hm
    have hma : (1 : ℝ) / 27 ≤ m a := hm a (by simp)
    have hms : ∀ i ∈ s, (1 : ℝ) / 27 ≤ m i := fun i hi => hm i (by simp [hi])
    have ihs := ih hms
    have hcard : (0 : ℝ) < (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 hs
    have hsum : ((s.card : ℝ)) / 27 ≤ ∑ i ∈ s, m i := sum_ge_card_div_27 s m hms
    have hrest : (1 : ℝ) / 27 ≤ (∑ i ∈ s, m i) - ((s.card : ℝ) - 1) / 27 := by
      linarith
    have hmerge := lagrangeExponent_subadditive_shift hma hrest
    have harg : m a + ((∑ i ∈ s, m i) - ((s.card : ℝ) - 1) / 27) - 1 / 27
        = (m a + ∑ i ∈ s, m i) - ((s.card : ℝ) + 1 - 1) / 27 := by ring
    rw [harg] at hmerge
    rw [Finset.sum_cons, Finset.sum_cons, Finset.card_cons]
    push_cast
    linarith [hmerge, ihs]
