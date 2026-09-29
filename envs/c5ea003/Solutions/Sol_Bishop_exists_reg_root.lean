-- Prove2me | solution 1 for Bishop.exists_reg_root
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:39:42.914265+00:00
-- url     : https://prove2.me/submissions/07d8e111-f4fd-4cec-807c-157b41c5e4f4

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveIVT.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
import Theorems.Thm_Bishop_Reg_toReal_eq_of_approx_le
import Theorems.Thm_Bishop_abs_sub_root_le
import Theorems.Thm_Bishop_exists_grid_abs_le
import Theorems.Thm_Bishop_exists_root
import Theorems.Thm_Bishop_grid_mem_Icc
/-
# The constructive intermediate value theorem, with explicit modulus

In Bishop's constructive analysis the classical intermediate value theorem is not
available: from `f a ≤ 0 ≤ f b` one cannot compute a point where `f` vanishes
(see `Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean`).  What *is*
constructively valid, and what Bishop proves, are:

1. the **approximate intermediate value theorem**: for every `ε > 0` one can
   *compute* a point `x ∈ [a,b]` with `|f x| ≤ ε`, provided `f` comes with a
   modulus of uniform continuity `ω`;
2. the **exact intermediate value theorem** for functions that are, in an explicit
   quantitative sense, non-constant (here: with a positive lower slope bound `c`),
   together with an explicit modulus for the root.

Both are proved below.  The approximate root is produced by an entirely explicit
finite search on the grid `a + k(b-a)/N`, `0 ≤ k ≤ N`, where `N` is any integer with
`(b-a)/N ≤ ω ε`; the witness is the *largest* grid index at which `f` is `≤ 0`.

The final theorem `exists_reg_root` presents the root of such a function as a
Bishop real (a regular sequence of rationals) whose rational approximations are
explicitly grid points of the above finite search.
-/


open Bishop

open Set










/-! ## Exact roots under an explicit non-degeneracy assumption -/





/-- **Constructive intermediate value theorem with explicit modulus.**

For a function with modulus of uniform continuity `ω` and slope bound `c > 0` on
`[a,b]`, with `f a ≤ 0 ≤ f b`, there is a (unique) root `r`, and for every desired
accuracy `δ > 0` an explicitly computed grid point of mesh `≤ ω (c * δ)` lies within
`δ` of `r`.  The modulus of the root as a function of the desired accuracy is thus
`δ ↦ ω (c * δ)`. -/
theorem constructive_ivt {f : ℝ → ℝ} {a b c : ℝ} {ω : ℝ → ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hω : HasModulusOn f (Icc a b) ω) (hslope : HasSlopeBoundOn f (Icc a b) c)
    (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ r ∈ Icc a b, f r = 0 ∧
      ∀ δ > 0, ∀ N : ℕ, 0 < N → (b - a) / N ≤ ω (c * δ) →
        ∃ k ≤ N, |grid a b N k - r| ≤ δ := by
  obtain ⟨r, hr, hfr⟩ := exists_root hab hω hfa hfb
  refine ⟨r, hr, hfr, ?_⟩
  intro δ hδ N hN hstep
  obtain ⟨k, hk, hfk⟩ := exists_grid_abs_le hab hω (by positivity) hN hstep hfa hfb
  refine ⟨k, hk, ?_⟩
  have := abs_sub_root_le hc hslope hr hfr (grid_mem_Icc hab hN hk) hfk
  calc |grid a b N k - r| ≤ c * δ / c := this
    _ = δ := by field_simp

/-! ## The root as a Bishop real

Finally we present the root itself as a Bishop real: a regular sequence of
*rationals*, each term of which is one of the explicitly searched grid points. -/


lemma gridQ_cast (a b : ℚ) (N k : ℕ) :
    ((gridQ a b N k : ℚ) : ℝ) = grid (a : ℝ) (b : ℝ) N k := by
  simp only [gridQ, grid]
  push_cast
  ring



open Bishop in
theorem solution{f : ℝ → ℝ} {a b : ℚ} {c : ℝ} {ω : ℝ → ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hω : HasModulusOn f (Icc (a : ℝ) b) ω) (hslope : HasSlopeBoundOn f (Icc (a : ℝ) b) c)
    (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ x : Reg, f x.toReal = 0 ∧ x.toReal ∈ Icc (a : ℝ) b ∧
      ∀ n : ℕ, ∃ N k : ℕ, 0 < N ∧ k ≤ N ∧ x.approx n = gridQ a b N k := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  obtain ⟨r, hr, hfr, hgrid⟩ := constructive_ivt hab' hc hω hslope hfa hfb
  -- for each `n` choose a grid point within `1/(2(n+1))` of the root
  have hchoice : ∀ n : ℕ, ∃ p : ℕ × ℕ, 0 < p.1 ∧ p.2 ≤ p.1 ∧
      |((gridQ a b p.1 p.2 : ℚ) : ℝ) - r| ≤ 1 / (2 * (n + 1)) := by
    intro n
    set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    have hωpos : 0 < ω (c * δ) := (hω (c * δ) (by positivity)).1
    obtain ⟨N, hNgt⟩ := exists_nat_gt (((b : ℝ) - a) / ω (c * δ))
    have hNpos : 0 < N := by
      by_contra h
      push_neg at h
      interval_cases N
      · have : (0 : ℝ) ≤ ((b : ℝ) - a) / ω (c * δ) := div_nonneg (by linarith) hωpos.le
        simp at hNgt
        linarith
    have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hstep : ((b : ℝ) - a) / N ≤ ω (c * δ) := by
      rw [div_le_iff₀ hN']
      have := (div_lt_iff₀ hωpos).mp hNgt
      linarith
    obtain ⟨k, hk, hkr⟩ := hgrid δ hδ N hNpos hstep
    exact ⟨(N, k), hNpos, hk, by rw [gridQ_cast]; exact hkr⟩
  choose p hp using hchoice
  set q : ℕ → ℚ := fun n => gridQ a b (p n).1 (p n).2 with hq
  have hqr : ∀ n : ℕ, |((q n : ℚ) : ℝ) - r| ≤ 1 / (2 * (n + 1)) := fun n => (hp n).2.2
  have hreg : ∀ m n : ℕ, |q m - q n| ≤ 1 / (m + 1) + 1 / (n + 1) := by
    intro m n
    have hR : |((q m : ℚ) : ℝ) - ((q n : ℚ) : ℝ)| ≤ 1 / (m + 1) + 1 / (n + 1) := by
      have h1 : |((q m : ℚ) : ℝ) - ((q n : ℚ) : ℝ)|
          ≤ |((q m : ℚ) : ℝ) - r| + |r - ((q n : ℚ) : ℝ)| := abs_sub_le _ _ _
      have h2 := hqr m
      have h3 : |r - ((q n : ℚ) : ℝ)| ≤ 1 / (2 * (n + 1)) := by
        rw [abs_sub_comm]; exact hqr n
      have h4 : (1 : ℝ) / (2 * (m + 1)) ≤ 1 / (m + 1) := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have h5 : (1 : ℝ) / (2 * (n + 1)) ≤ 1 / (n + 1) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have h' : ((|q m - q n| : ℚ) : ℝ) ≤ (((1 : ℚ) / (m + 1) + 1 / (n + 1) : ℚ) : ℝ) := by
      push_cast
      simpa using hR
    exact_mod_cast h'
  have hx : (⟨q, hreg⟩ : Reg).toReal = r := by
    refine Reg.toReal_eq_of_approx_le _ r 1 (fun n => ?_)
    have h2 := hqr n
    have h3 : (1 : ℝ) / (2 * (n + 1)) ≤ 1 * (1 / ((n : ℝ) + 1)) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have : (1 : ℝ) / (2 * (n + 1)) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have happ : (⟨q, hreg⟩ : Reg).approx n = q n := rfl
    rw [happ]
    linarith
  refine ⟨⟨q, hreg⟩, ?_, ?_, ?_⟩
  · rw [hx]; exact hfr
  · rw [hx]; exact hr
  · intro n
    exact ⟨(p n).1, (p n).2, (hp n).1, (hp n).2.1, rfl⟩
