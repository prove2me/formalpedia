-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.two_component_gen_implied_exponent_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:28.419429+00:00
-- url     : https://prove2.me/submissions/3026fe21-8ba1-4409-832f-9ab676405afa

-- Sol generated from Probability/GeneralMixtureWindowLaw.lean
import Mathlib
import Definitions.Def_Probability_GeneralMixtureWindowLaw
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
import Theorems.Thm_HarmonicBulkSteeperEdge_genHeadMass_strict_single_crossing
import Theorems.Thm_HarmonicBulkSteeperEdge_headMass_le_of_exponent_le
/-
  # The window law for arbitrary exponent heterogeneity

  `Probability.HarmonicBulkSteeperEdgeStrict` proves that the window-implied exponent of a
  *two-component* power-law kernel is strictly antitone in the window width.  Nothing in
  that proof used the number two: it used only that the kernel-to-power-law ratio is
  strictly convex in `log k`.  This file carries the argument out for an arbitrary finite
  positive combination of power laws

  `k ↦ ∑ i ∈ s, w i · k ^ (-e i)`,

  and shows that the antitone window law is a signature of *exponent heterogeneity as
  such*: it holds as soon as two of the exponents differ, with any number of components and
  any positive weights.

  * `genRatio_strict_log_convex` — strict convexity in the logarithmic index, from the
    two-power lemmas of `HarmonicBulkSteeperEdgeStrict` plus a strict sum comparison.
  * `genRatio_lt_of_crossed_strict` — strict no-return past a weak crossing.
  * `genHeadMass_strict_single_crossing` — a pure power law matching the mixture's head mass
    on a window reports strictly less head mass on every narrower window.
  * `gen_implied_exponent_strictAnti` — the window-implied exponent is strictly antitone.
  * `two_component_gen_implied_exponent_strictAnti` — the two-component theorem recovered as
    the instance `s = {0, 1}`, confirming the generalisation is faithful.
-/

open Finset

open HarmonicBulkSteeperEdge

variable {ι : Type*}

/-! ## A finite positive combination of power laws -/








/-! ## Strict log-convexity for an arbitrary heterogeneous mixture -/




/-! ## The window law -/


/-- **Universal antitone window law.**  For *any* finite positive combination of power laws
with at least two distinct exponents, the window-implied exponent is strictly antitone in
the window width.  Exponent heterogeneity as such — not the number of components — is what
produces a steeper-than-bulk left edge. -/
theorem gen_implied_exponent_strictAnti {s : Finset ι} {w e : ι → ℝ} {c₁ c₂ : ℝ}
    (hw : ∀ i ∈ s, 0 < w i) {p q : ι} (hp : p ∈ s) (hq : q ∈ s) (hpq : e p ≠ e q)
    {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (h₁ : headMass c₁ n m₁ = genHeadMass s w e n m₁)
    (h₂ : headMass c₂ n m₂ = genHeadMass s w e n m₂) :
    c₂ < c₁ := by
  by_contra hcon
  push_neg at hcon
  have hmono : headMass c₁ n m₁ ≤ headMass c₂ n m₁ :=
    headMass_le_of_exponent_le hcon hm₁ (by omega)
  have hstrict : headMass c₂ n m₁ < genHeadMass s w e n m₁ :=
    genHeadMass_strict_single_crossing hw hp hq hpq hm₁ h₁₂ h₂n h₂
  rw [h₁] at hmono
  linarith

/-- The two-component law is the instance `s = {0, 1}` of the general law: with weights
`1 - w` and `w` and exponents `a < b`, the general kernel *is* the bulk × edge mixture. -/
lemma genKernel_two_component (w a b : ℝ) (k : ℕ) :
    genKernel ({0, 1} : Finset ℕ) (fun i => if i = 0 then 1 - w else w)
      (fun i => if i = 0 then a else b) k = mix w a b k := by
  rw [genKernel, mix]
  simp



open HarmonicBulkSteeperEdge in
theorem solution{w a b c₁ c₂ : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (hab : a < b) {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (h₁ : headMass c₁ n m₁ = mixHeadMass w a b n m₁)
    (h₂ : headMass c₂ n m₂ = mixHeadMass w a b n m₂) :
    c₂ < c₁ := by
  have hsum : ∀ m : ℕ, genHeadSum ({0, 1} : Finset ℕ) (fun i => if i = 0 then 1 - w else w)
      (fun i => if i = 0 then a else b) m = mixHeadSum w a b m := by
    intro m
    rw [genHeadSum, mixHeadSum]
    exact Finset.sum_congr rfl (fun k _ => genKernel_two_component w a b k)
  have hmass : ∀ m : ℕ, genHeadMass ({0, 1} : Finset ℕ) (fun i => if i = 0 then 1 - w else w)
      (fun i => if i = 0 then a else b) n m = mixHeadMass w a b n m := by
    intro m
    rw [genHeadMass, mixHeadMass, hsum, hsum]
  refine gen_implied_exponent_strictAnti (s := ({0, 1} : Finset ℕ))
    (w := fun i => if i = 0 then 1 - w else w)
    (e := fun i => if i = 0 then a else b) ?_ (p := 0) (q := 1)
    (by simp) (by simp) ?_ hm₁ h₁₂ h₂n ?_ ?_
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by simpa using hi
    rcases hi' with h | h
    · subst h
      have hpos : (0:ℝ) < 1 - w := by linarith
      simpa using hpos
    · subst h
      simpa using hw0
  · simpa using ne_of_lt hab
  · rw [hmass]; exact h₁
  · rw [hmass]; exact h₂
