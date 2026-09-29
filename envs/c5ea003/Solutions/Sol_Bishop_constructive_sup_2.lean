-- Prove2me | solution 2 for Bishop.constructive_sup
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:02:06.572074+00:00
-- url     : https://prove2.me/submissions/162fd4e3-fcb4-4aaa-9a6a-9a0efc266dd2

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveSup

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Logic/ConstructiveAnalysis/BishopReals.lean ====
/-
# Bishop-style constructive real numbers

This file develops the elementary theory of Errett Bishop's *regular sequences of
rationals*, the standard presentation of the real numbers in constructive analysis
(Bishop–Bridges, *Constructive Analysis*, Chapter 2).

A Bishop real is a sequence `x : ℕ → ℚ` of rationals together with the **explicit
modulus** condition

  `|x m - x n| ≤ 1/(m+1) + 1/(n+1)`,

i.e. `x n` is an approximation of the number it denotes to within `1/(n+1)`.  No
appeal to a choice principle or to a modulus obtained non-effectively is needed:
the modulus of Cauchyness is built into the datum.

Main results:

* `Bishop.Reg.abs_toReal_sub_approx_le` : the classical real `toReal x` denoted by a
  regular sequence is approximated by `x.approx n` with the *explicit* error bound
  `1/(n+1)`.
* `Bishop.Reg.equiv_iff_toReal_eq` : Bishop's equality `∀ n, |x n - y n| ≤ 2/(n+1)`
  agrees with equality of the denoted classical reals; in particular it is an
  equivalence relation (a nontrivial fact constructively).
* `Bishop.Reg.exists_toReal_eq` : every classical real is denoted by a regular
  sequence (so nothing is lost by the constructive presentation).
* `Bishop.Reg.limit` : *constructive completeness*.  From a regular sequence of
  Bishop reals one builds, by an explicit diagonal formula, a Bishop real which is
  its limit, with the explicit error estimate `|lim - x k| ≤ 1/(k+1)`.
* `Bishop.equivReal` : the quotient of the Bishop reals by Bishop equality is in
  bijection with the classical reals — the comparison with classical mathematics.
-/

namespace Bishop

open Filter Topology

-- [dropped: platform already declares Reg]
namespace Reg

-- [dropped: platform already declares regular_real]
-- [dropped: platform already declares cauchySeq]
-- [dropped: platform already declares toReal]
-- [dropped: platform already declares tendsto_toReal]
-- [dropped: platform already declares abs_toReal_sub_approx_le]
/-- If the rational approximations of a Bishop real converge to `r` at the canonical
rate (up to a constant), then the Bishop real denotes `r`. -/
theorem toReal_eq_of_approx_le (x : Reg) (r C : ℝ)
    (h : ∀ n : ℕ, |(x.approx n : ℝ) - r| ≤ C * (1 / ((n : ℝ) + 1))) : x.toReal = r := by
  have key : ∀ n : ℕ, |x.toReal - r| ≤ (1 + C) * (1 / ((n : ℝ) + 1)) := by
    intro n
    have h1 := x.abs_toReal_sub_approx_le n
    have h2 := h n
    have h3 : |x.toReal - r| ≤ |x.toReal - (x.approx n : ℝ)| + |(x.approx n : ℝ) - r| :=
      abs_sub_le _ _ _
    have h4 : (1 : ℝ) / ((n : ℝ) + 1) = 1 * (1 / ((n : ℝ) + 1)) := by ring
    rw [h4] at h1
    nlinarith [h1, h2, h3]
  have hlim : Tendsto (fun n : ℕ => (1 + C) * ((1 : ℝ) / (n + 1))) atTop (𝓝 ((1 + C) * 0)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 + C)
  have h0 : |x.toReal - r| ≤ 0 := by
    have := le_of_tendsto_of_tendsto' (tendsto_const_nhds
      (x := |x.toReal - r|) (f := atTop (α := ℕ))) hlim key
    simpa using this
  have := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  linarith

-- [dropped: platform already declares Equiv]
/-- Bishop equality of regular sequences coincides with equality of the denoted
classical reals. -/
theorem equiv_iff_toReal_eq (x y : Reg) : Equiv x y ↔ x.toReal = y.toReal := by
  constructor
  · intro h
    have key : ∀ n : ℕ, |x.toReal - y.toReal| ≤ 4 / (n + 1) := by
      intro n
      have hxy : |(x.approx n : ℝ) - (y.approx n : ℝ)| ≤ 2 / (n + 1) := by
        have := h n
        have h' : ((|x.approx n - y.approx n| : ℚ) : ℝ) ≤ (((2 : ℚ) / (n + 1) : ℚ) : ℝ) := by
          exact_mod_cast this
        push_cast at h'
        exact h'
      have hx := x.abs_toReal_sub_approx_le n
      have hy := y.abs_toReal_sub_approx_le n
      calc |x.toReal - y.toReal|
          ≤ |x.toReal - (x.approx n : ℝ)| + |(x.approx n : ℝ) - y.toReal| :=
            abs_sub_le _ _ _
        _ ≤ |x.toReal - (x.approx n : ℝ)|
              + (|(x.approx n : ℝ) - (y.approx n : ℝ)| + |(y.approx n : ℝ) - y.toReal|) :=
            add_le_add le_rfl (abs_sub_le _ _ _)
        _ ≤ 1 / (n + 1) + (2 / (n + 1) + 1 / (n + 1)) :=
            add_le_add hx (add_le_add hxy (by rw [abs_sub_comm]; exact hy))
        _ = 4 / (n + 1) := by ring
    have hlim : Tendsto (fun n : ℕ => (4 : ℝ) / (n + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 : ℝ)
    have : |x.toReal - y.toReal| ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hlim key
    have : x.toReal - y.toReal = 0 := by
      have := abs_nonneg (x.toReal - y.toReal)
      have h0 : |x.toReal - y.toReal| = 0 := le_antisymm ‹|x.toReal - y.toReal| ≤ 0› this
      exact abs_eq_zero.mp h0
    linarith
  · intro h n
    have hx := x.abs_toReal_sub_approx_le n
    have hy := y.abs_toReal_sub_approx_le n
    have : |(x.approx n : ℝ) - (y.approx n : ℝ)| ≤ 2 / (n + 1) := by
      calc |(x.approx n : ℝ) - (y.approx n : ℝ)|
          ≤ |(x.approx n : ℝ) - x.toReal| + |x.toReal - (y.approx n : ℝ)| := abs_sub_le _ _ _
        _ ≤ 1 / (n + 1) + 1 / (n + 1) := by
            gcongr
            · rw [abs_sub_comm]; exact hx
            · rw [h]; exact hy
        _ = 2 / (n + 1) := by ring
    have : ((|x.approx n - y.approx n| : ℚ) : ℝ) ≤ (((2 : ℚ) / (n + 1) : ℚ) : ℝ) := by
      push_cast
      simpa using this
    exact_mod_cast this

lemma equiv_refl (x : Reg) : Equiv x x := (equiv_iff_toReal_eq x x).2 rfl

lemma equiv_symm {x y : Reg} (h : Equiv x y) : Equiv y x :=
  (equiv_iff_toReal_eq y x).2 ((equiv_iff_toReal_eq x y).1 h).symm

/-- Transitivity of Bishop equality (the constructive "3ε" argument). -/
lemma equiv_trans {x y z : Reg} (h₁ : Equiv x y) (h₂ : Equiv y z) : Equiv x z :=
  (equiv_iff_toReal_eq x z).2
    (((equiv_iff_toReal_eq x y).1 h₁).trans ((equiv_iff_toReal_eq y z).1 h₂))

/-- Every classical real number is denoted by a regular sequence: the constructive
presentation loses nothing. -/
theorem exists_toReal_eq (r : ℝ) : ∃ x : Reg, x.toReal = r := by
  have hchoice : ∀ n : ℕ, ∃ q : ℚ, |r - (q : ℝ)| < 1 / (2 * (n + 1)) := by
    intro n
    exact exists_rat_near r (by positivity)
  choose q hq using hchoice
  have hreg : ∀ m n : ℕ, |q m - q n| ≤ 1 / (m + 1) + 1 / (n + 1) := by
    intro m n
    have hm := hq m
    have hn := hq n
    have : |((q m : ℝ)) - (q n : ℝ)| ≤ 1 / (m + 1) + 1 / (n + 1) := by
      have h1 : |((q m : ℝ)) - (q n : ℝ)| ≤ |(q m : ℝ) - r| + |r - (q n : ℝ)| :=
        abs_sub_le _ _ _
      have h2 : |(q m : ℝ) - r| < 1 / (2 * (m + 1)) := by
        rw [abs_sub_comm]; exact hm
      have h3 : (1 : ℝ) / (2 * (m + 1)) ≤ 1 / (m + 1) := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have h4 : (1 : ℝ) / (2 * (n + 1)) ≤ 1 / (n + 1) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have h' : ((|q m - q n| : ℚ) : ℝ) ≤ (((1 : ℚ) / (m + 1) + 1 / (n + 1) : ℚ) : ℝ) := by
      push_cast
      simpa using this
    exact_mod_cast h'
  refine ⟨⟨q, hreg⟩, ?_⟩
  set x : Reg := ⟨q, hreg⟩ with hx
  have key : ∀ n : ℕ, |x.toReal - r| ≤ 2 / (n + 1) := by
    intro n
    have h1 := x.abs_toReal_sub_approx_le n
    have h2 := hq n
    have hxa : x.approx n = q n := rfl
    rw [hxa] at h1
    have h3 : |(q n : ℝ) - r| ≤ 1 / (n + 1) := by
      rw [abs_sub_comm]
      have h4 : (1 : ℝ) / (2 * (n + 1)) ≤ 1 / (n + 1) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [h2]
    calc |x.toReal - r| ≤ |x.toReal - (q n : ℝ)| + |(q n : ℝ) - r| := abs_sub_le _ _ _
      _ ≤ 1 / (n + 1) + 1 / (n + 1) := add_le_add h1 h3
      _ = 2 / (n + 1) := by ring
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
  have h0 : |x.toReal - r| ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim key
  have := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
  linarith [this]

/-! ## Constructive completeness

A *regular sequence of reals* is a sequence `x : ℕ → Reg` with
`|x k - x l| ≤ 1/(k+1) + 1/(l+1)`.  Bishop's completeness theorem builds its limit
by an explicit diagonal formula, together with an explicit rate of convergence. -/

-- [dropped: platform already declares IsRegularSeqOfReals]
-- [dropped: platform already declares diag_regular]
-- [dropped: platform already declares limit]
/-- **Explicit rate of convergence.**  The limit constructed above satisfies
`|lim - x k| ≤ 1/(k+1)`: the sequence converges with the canonical modulus. -/
theorem limit_spec {x : ℕ → Reg} (hx : IsRegularSeqOfReals x) (k : ℕ) :
    |(limit hx).toReal - (x k).toReal| ≤ 1 / (k + 1) := by
  have key : ∀ n : ℕ, |(limit hx).toReal - (x k).toReal|
      ≤ 2 * (1 / ((n : ℝ) + 1)) + 1 / (k + 1) := by
    intro n
    have h1 := (limit hx).abs_toReal_sub_approx_le n
    have happrox : (limit hx).approx n = (x (2 * n + 1)).approx (2 * n + 1) := rfl
    rw [happrox] at h1
    have h2 := (x (2 * n + 1)).abs_toReal_sub_approx_le (2 * n + 1)
    have e1 : ((2 * n + 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 2 := by push_cast; ring
    rw [e1] at h2
    have h3 := hx (2 * n + 1) k
    rw [e1] at h3
    have ea : (1 : ℝ) / (2 * (n : ℝ) + 2) = (1 / ((n : ℝ) + 1)) / 2 := by
      rw [div_div]; ring_nf
    rw [ea] at h2 h3
    have h4 : |(limit hx).toReal - (x k).toReal|
        ≤ |(limit hx).toReal - ((x (2 * n + 1)).approx (2 * n + 1) : ℝ)|
          + |((x (2 * n + 1)).approx (2 * n + 1) : ℝ) - (x k).toReal| := abs_sub_le _ _ _
    have h5 : |((x (2 * n + 1)).approx (2 * n + 1) : ℝ) - (x k).toReal|
        ≤ |((x (2 * n + 1)).approx (2 * n + 1) : ℝ) - (x (2 * n + 1)).toReal|
          + |(x (2 * n + 1)).toReal - (x k).toReal| := abs_sub_le _ _ _
    have h2' : |((x (2 * n + 1)).approx (2 * n + 1) : ℝ) - (x (2 * n + 1)).toReal|
        ≤ (1 / ((n : ℝ) + 1)) / 2 := by rw [abs_sub_comm]; exact h2
    linarith
  have hlim : Tendsto (fun n : ℕ => 2 * ((1 : ℝ) / (n + 1)) + 1 / (k + 1)) atTop
      (𝓝 (2 * 0 + 1 / (k + 1))) :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)).add
      tendsto_const_nhds
  have := le_of_tendsto_of_tendsto' (tendsto_const_nhds
    (x := |(limit hx).toReal - (x k).toReal|) (f := atTop (α := ℕ))) hlim key
  simpa using this

end Reg

/-- Bishop equality as a setoid on regular sequences. -/
def bishopSetoid : Setoid Reg where
  r := Reg.Equiv
  iseqv := ⟨Reg.equiv_refl, Reg.equiv_symm, Reg.equiv_trans⟩

/-- The type of Bishop reals: regular sequences modulo Bishop equality. -/
def BishopReal : Type := Quotient bishopSetoid

/-- The map sending a Bishop real to the classical real it denotes. -/
noncomputable def toRealQuot : BishopReal → ℝ :=
  Quotient.lift Reg.toReal (fun _ _ h => (Reg.equiv_iff_toReal_eq _ _).1 h)

/-- **Comparison with classical analysis.**  The Bishop reals, modulo Bishop
equality, are in canonical bijection with the classical real numbers. -/
noncomputable def equivReal : BishopReal ≃ ℝ := by
  refine Equiv.ofBijective toRealQuot ⟨?_, ?_⟩
  · refine Quotient.ind₂ (fun a b h => ?_)
    exact Quotient.sound ((Reg.equiv_iff_toReal_eq a b).2 h)
  · intro r
    obtain ⟨x, hx⟩ := Reg.exists_toReal_eq r
    exact ⟨Quotient.mk _ x, hx⟩

end Bishop
-- ==== upstream: Packages/Catalog/Logic/ConstructiveAnalysis/ConstructiveSup.lean ====
/-
# Bishop's constructive least upper bound principle

Classically every nonempty set of reals that is bounded above has a supremum.  That
proof is not constructive: it decides, for a rational `q`, whether `q` is an upper
bound of the set, which is in general undecidable.  Bishop's replacement assumes
that the set is **located**: it comes equipped with a *decision procedure* `L` such
that for rationals `p < q`, `L p q = true` guarantees that `q` is an upper bound,
and `L p q = false` produces a member of the set above `p`.  (Both alternatives may
hold; only their disjunction is asserted, which is what makes the datum obtainable
in practice.)

From such a datum the supremum is computed by an explicit **trisection search**
(`Bishop.bisect`), producing at every stage a pair of rationals `p n ≤ sup ≤ q n`
whose width is exactly `(2/3)^n (b₀ - a₀)`:

* `Bishop.bisect_width` : the exact geometric rate;
* `Bishop.bisect_invariant` : the enclosure invariant, proved by induction;
* `Bishop.constructive_sup` : the supremum exists, is the least upper bound, and is
  enclosed by the explicitly computed rationals with the stated rate;
* `Bishop.constructive_sup_reg` : the supremum, presented as a Bishop real, i.e. as a
  regular sequence of rationals with the canonical modulus `1/(n+1)`.

The located hypothesis is exactly what the classical proof hides: `Bishop.
locatedData_of_decidable` shows that assuming the classically valid but
constructively unavailable decision "is `q` an upper bound?" one recovers a located
datum, so the principle is classically equivalent to the ordinary completeness
axiom.
-/


namespace Bishop

open Set

-- [dropped: platform already declares bisectStep]
-- [dropped: platform already declares bisect]
@[simp] lemma bisect_zero (L : ℚ → ℚ → Bool) (a₀ b₀ : ℚ) : bisect L a₀ b₀ 0 = (a₀, b₀) := rfl

@[simp] lemma bisect_succ (L : ℚ → ℚ → Bool) (a₀ b₀ : ℚ) (n : ℕ) :
    bisect L a₀ b₀ (n + 1) = bisectStep L (bisect L a₀ b₀ n) := rfl

lemma bisectStep_width (L : ℚ → ℚ → Bool) (pq : ℚ × ℚ) :
    (bisectStep L pq).2 - (bisectStep L pq).1 = 2 / 3 * (pq.2 - pq.1) := by
  simp only [bisectStep]
  split <;> simp <;> ring

/-- **Exact geometric rate.**  The `n`-th enclosure has width `(2/3)^n (b₀ - a₀)`. -/
theorem bisect_width (L : ℚ → ℚ → Bool) (a₀ b₀ : ℚ) (n : ℕ) :
    (bisect L a₀ b₀ n).2 - (bisect L a₀ b₀ n).1 = (2 / 3) ^ n * (b₀ - a₀) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bisect_succ, bisectStep_width, ih]
      ring

lemma bisect_lt (L : ℚ → ℚ → Bool) {a₀ b₀ : ℚ} (hab : a₀ < b₀) (n : ℕ) :
    (bisect L a₀ b₀ n).1 < (bisect L a₀ b₀ n).2 := by
  have hw := bisect_width L a₀ b₀ n
  have hpos : (0 : ℚ) < (2 / 3) ^ n * (b₀ - a₀) := by
    have h1 : (0 : ℚ) < (2 / 3 : ℚ) ^ n := by positivity
    have h2 : (0 : ℚ) < b₀ - a₀ := by linarith
    positivity
  linarith

-- [dropped: platform already declares Enclosing]
-- [dropped: platform already declares LocatedData]
lemma enclosing_bisectStep {S : Set ℝ} (D : LocatedData S) {pq : ℚ × ℚ}
    (hlt : pq.1 < pq.2) (h : Enclosing S pq) : Enclosing S (bisectStep D.L pq) := by
  obtain ⟨hup, hlow⟩ := h
  have hm : pq.1 + (pq.2 - pq.1) / 3 < pq.1 + 2 * (pq.2 - pq.1) / 3 := by linarith
  by_cases hL : D.L (pq.1 + (pq.2 - pq.1) / 3) (pq.1 + 2 * (pq.2 - pq.1) / 3) = true
  · have hstep : bisectStep D.L pq = (pq.1, pq.1 + 2 * (pq.2 - pq.1) / 3) := by
      simp [bisectStep, hL]
    rw [hstep]
    exact ⟨D.upper _ _ hm hL, hlow⟩
  · have hLf : D.L (pq.1 + (pq.2 - pq.1) / 3) (pq.1 + 2 * (pq.2 - pq.1) / 3) = false := by
      simpa using hL
    have hstep : bisectStep D.L pq = (pq.1 + (pq.2 - pq.1) / 3, pq.2) := by
      simp [bisectStep, hLf]
    rw [hstep]
    exact ⟨hup, D.witness _ _ hm hLf⟩

/-- **The enclosure invariant.**  Every stage of the search encloses the supremum. -/
theorem bisect_invariant {S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
    (h₀ : Enclosing S (a₀, b₀)) (n : ℕ) : Enclosing S (bisect D.L a₀ b₀ n) := by
  induction n with
  | zero => simpa using h₀
  | succ n ih =>
      rw [bisect_succ]
      exact enclosing_bisectStep D (bisect_lt D.L hab n) ih

/-- **Bishop's constructive least upper bound principle.**

A set of reals that is nonempty, bounded above, and *located* (in the explicit sense
of `LocatedData`) has a least upper bound, and this supremum is enclosed by the
explicitly computed rationals of the trisection search, with the exact geometric
rate `(2/3)^n (b₀ - a₀)`. -/
theorem constructive_sup {S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
    (h₀ : Enclosing S (a₀, b₀)) :
    ∃ u : ℝ, IsLUB S u ∧ ∀ n : ℕ,
      ((bisect D.L a₀ b₀ n).1 : ℝ) ≤ u ∧ u ≤ ((bisect D.L a₀ b₀ n).2 : ℝ) ∧
        ((bisect D.L a₀ b₀ n).2 : ℝ) - ((bisect D.L a₀ b₀ n).1 : ℝ)
          = (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)) := by
  obtain ⟨hup₀, s₀, hs₀S, _⟩ := id h₀
  have hne : S.Nonempty := ⟨s₀, hs₀S⟩
  have hbdd : BddAbove S := ⟨(b₀ : ℝ), fun s hs => hup₀ s hs⟩
  refine ⟨sSup S, isLUB_csSup hne hbdd, fun n => ?_⟩
  obtain ⟨hup, s, hsS, hs⟩ := bisect_invariant D hab h₀ n
  refine ⟨?_, ?_, ?_⟩
  · exact le_of_lt (lt_of_lt_of_le hs (le_csSup hbdd hsS))
  · exact csSup_le hne hup
  · have := bisect_width D.L a₀ b₀ n
    have hR : (((bisect D.L a₀ b₀ n).2 - (bisect D.L a₀ b₀ n).1 : ℚ) : ℝ)
        = (((2 / 3) ^ n * (b₀ - a₀) : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at hR
    linarith

/-- An index at which the trisection width is below the canonical accuracy
`1/(k+1)`. -/
lemma exists_bisect_index (a₀ b₀ : ℚ) (hab : a₀ < b₀) (k : ℕ) :
    ∃ n : ℕ, (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)) ≤ 1 / (k + 1) := by
  have hW : (0 : ℝ) < (b₀ : ℝ) - (a₀ : ℝ) := by
    have : (a₀ : ℝ) < (b₀ : ℝ) := by exact_mod_cast hab
    linarith
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have h23 : |(2 / 3 : ℝ)| < 1 := by rw [abs_of_nonneg] <;> norm_num
  have htend : Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)))
      Filter.atTop (nhds (0 * ((b₀ : ℝ) - (a₀ : ℝ)))) :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h23).mul_const _
  rw [zero_mul] at htend
  have := (htend.eventually (eventually_le_nhds hk)).exists
  obtain ⟨n, hn⟩ := this
  exact ⟨n, hn⟩

/-- **The supremum of a located set is a Bishop real.**  Its `k`-th rational
approximation is the left endpoint of the first trisection stage whose width is
below `1/(k+1)`, so the whole construction stays inside the rationals. -/
theorem constructive_sup_reg {S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
    (h₀ : Enclosing S (a₀, b₀)) :
    ∃ x : Reg, IsLUB S x.toReal ∧
      ∀ k : ℕ, ∃ n : ℕ, x.approx k = (bisect D.L a₀ b₀ n).1 := by
  obtain ⟨u, hu, henc⟩ := constructive_sup D hab h₀
  have hchoice : ∀ k : ℕ, ∃ n : ℕ, |(((bisect D.L a₀ b₀ n).1 : ℚ) : ℝ) - u| ≤ 1 / (k + 1) := by
    intro k
    obtain ⟨n, hn⟩ := exists_bisect_index a₀ b₀ hab k
    obtain ⟨h1, h2, h3⟩ := henc n
    refine ⟨n, ?_⟩
    rw [abs_le]
    constructor <;> [linarith; linarith]
  choose N hN using hchoice
  set q : ℕ → ℚ := fun k => (bisect D.L a₀ b₀ (N k)).1 with hq
  have hreg : ∀ m n : ℕ, |q m - q n| ≤ 1 / (m + 1) + 1 / (n + 1) := by
    intro m n
    have hR : |((q m : ℚ) : ℝ) - ((q n : ℚ) : ℝ)| ≤ 1 / (m + 1) + 1 / (n + 1) := by
      have h1 : |((q m : ℚ) : ℝ) - ((q n : ℚ) : ℝ)|
          ≤ |((q m : ℚ) : ℝ) - u| + |u - ((q n : ℚ) : ℝ)| := abs_sub_le _ _ _
      have h2 := hN m
      have h3 : |u - ((q n : ℚ) : ℝ)| ≤ 1 / (n + 1) := by
        rw [abs_sub_comm]; exact hN n
      linarith
    have h' : ((|q m - q n| : ℚ) : ℝ) ≤ (((1 : ℚ) / (m + 1) + 1 / (n + 1) : ℚ) : ℝ) := by
      push_cast
      simpa using hR
    exact_mod_cast h'
  have hx : (⟨q, hreg⟩ : Reg).toReal = u := by
    refine Reg.toReal_eq_of_approx_le _ u 1 (fun k => ?_)
    have happ : (⟨q, hreg⟩ : Reg).approx k = q k := rfl
    rw [happ, one_mul]
    exact hN k
  refine ⟨⟨q, hreg⟩, ?_, ?_⟩
  · rw [hx]; exact hu
  · intro k; exact ⟨N k, rfl⟩


/-! ## A worked instance: the hypotheses are satisfiable

To see that `LocatedData` is not a vacuous requirement, here is a completely
explicit instance — a set whose locatedness oracle is a decidable comparison of
rationals — on which the trisection search really runs. -/

-- [dropped: platform already declares locatedIic]
/-- On this instance the trisection search really encloses the supremum `c` at every
stage, with the width `(2/3)^n (b₀ - a₀)` of `bisect_width`. -/
theorem bisect_Iic_encloses {c a₀ b₀ : ℚ} (h1 : a₀ < c) (h2 : c ≤ b₀) (hab : a₀ < b₀) (n : ℕ) :
    ((bisect (locatedIic c).L a₀ b₀ n).1 : ℝ) < (c : ℝ) ∧
      (c : ℝ) ≤ ((bisect (locatedIic c).L a₀ b₀ n).2 : ℝ) := by
  have h₀ : Enclosing (Set.Iic (c : ℝ)) (a₀, b₀) := by
    constructor
    · intro s hs
      have : (c : ℝ) ≤ (b₀ : ℝ) := by exact_mod_cast h2
      exact le_trans hs this
    · exact ⟨(c : ℝ), Set.mem_Iic.mpr (le_refl _), by exact_mod_cast h1⟩
  obtain ⟨hup, s, hsS, hs⟩ := bisect_invariant (locatedIic c) hab h₀ n
  exact ⟨lt_of_lt_of_le hs (Set.mem_Iic.mp hsS), hup (c : ℝ) (Set.mem_Iic.mpr (le_refl _))⟩

/-! The search is genuinely computable; the following facts about the trisection for
`c = 1/2` on `[0,1]` are checked at compile time. -/

-- the first four enclosures
#guard (List.range 4).map (fun n => bisect (locatedIic (1/2)).L 0 1 n)
    = [(0, 1), (0, 2 / 3), (2 / 9, 2 / 3), (2 / 9, 14 / 27)]

-- after ten steps the width is exactly `(2/3)^10`
#guard (bisect (locatedIic (1/2)).L 0 1 10).2 - (bisect (locatedIic (1/2)).L 0 1 10).1
    = (2 / 3 : ℚ) ^ 10

-- and the enclosure does contain `1/2`
#guard (bisect (locatedIic (1/2)).L 0 1 10).1 < (1 / 2 : ℚ) &&
    (1 / 2 : ℚ) ≤ (bisect (locatedIic (1/2)).L 0 1 10).2

/-- **Comparison with the classical principle.**  Classically the locatedness datum
is free: deciding "is `q` an upper bound of `S`?" (a decision no constructive
procedure can make in general) yields a `LocatedData`.  So the constructive
principle is classically equivalent to ordinary completeness, and the whole content
of the constructive theorem lies in the extra datum. -/
noncomputable def locatedData_of_decidable (S : Set ℝ) : LocatedData S := by
  classical
  refine ⟨fun _ q => decide (∀ s ∈ S, s ≤ (q : ℝ)), ?_, ?_⟩
  · intro p q _ h s hs
    have : ∀ s ∈ S, s ≤ (q : ℝ) := of_decide_eq_true h
    exact this s hs
  · intro p q hpq h
    have hnot : ¬ ∀ s ∈ S, s ≤ (q : ℝ) := of_decide_eq_false h
    push_neg at hnot
    obtain ⟨s, hsS, hs⟩ := hnot
    have hpq' : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
    exact ⟨s, hsS, lt_trans hpq' hs⟩

end Bishop
section
open Bishop
open Set

theorem solution {S : Set ℝ} (D : LocatedData S) {a₀ b₀ : ℚ} (hab : a₀ < b₀)
    (h₀ : Enclosing S (a₀, b₀)) :
    ∃ u : ℝ, IsLUB S u ∧ ∀ n : ℕ,
      ((bisect D.L a₀ b₀ n).1 : ℝ) ≤ u ∧ u ≤ ((bisect D.L a₀ b₀ n).2 : ℝ) ∧
        ((bisect D.L a₀ b₀ n).2 : ℝ) - ((bisect D.L a₀ b₀ n).1 : ℝ)
          = (2 / 3 : ℝ) ^ n * ((b₀ : ℝ) - (a₀ : ℝ)) :=
  @Bishop.constructive_sup S D a₀ b₀ hab h₀

end
