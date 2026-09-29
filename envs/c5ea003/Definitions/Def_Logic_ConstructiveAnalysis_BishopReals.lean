-- Prove2me | Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
-- name    : Logic_ConstructiveAnalysis_BishopReals
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:49:22.061822+00:00
-- url     : https://prove2.me/theorems/8dad9197-41e2-4710-a246-031032c914a5
-- title:
--   Aether Catalog definitions — Logic_ConstructiveAnalysis_BishopReals
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ConstructiveAnalysis.BishopReals`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ConstructiveAnalysis/BishopReals.lean by skeleton subtraction
import Mathlib
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

/-- A **regular sequence of rationals** (a Bishop real): a sequence of rationals
carrying its own modulus of Cauchyness, `|x m - x n| ≤ 1/(m+1) + 1/(n+1)`. -/
structure Reg where
  /-- the `n`-th rational approximation, accurate to within `1/(n+1)`. -/
  approx : ℕ → ℚ
  /-- the explicit regularity (Cauchy modulus) condition. -/
  regular : ∀ m n : ℕ, |approx m - approx n| ≤ 1 / (m + 1) + 1 / (n + 1)

namespace Reg

lemma regular_real (x : Reg) (m n : ℕ) :
    |(x.approx m : ℝ) - (x.approx n : ℝ)| ≤ 1 / (m + 1) + 1 / (n + 1) := by
  have h := x.regular m n
  have h' : ((|x.approx m - x.approx n| : ℚ) : ℝ)
      ≤ (((1 : ℚ) / (m + 1) + 1 / (n + 1) : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

lemma cauchySeq (x : Reg) : CauchySeq (fun n => ((x.approx n : ℝ))) := by
  refine cauchySeq_of_le_tendsto_0 (fun N => 2 / (N + 1)) ?_ ?_
  · intro n m N hn hm
    have hb := x.regular_real n m
    have h1 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : (1 : ℝ) / (m + 1) ≤ 1 / (N + 1) := by
      have : (N : ℝ) ≤ m := by exact_mod_cast hm
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have : dist ((x.approx n : ℝ)) ((x.approx m : ℝ)) = |(x.approx n : ℝ) - x.approx m| :=
      Real.dist_eq _ _
    rw [this]
    calc |(x.approx n : ℝ) - x.approx m| ≤ 1 / (n + 1) + 1 / (m + 1) := hb
      _ ≤ 1 / (N + 1) + 1 / (N + 1) := add_le_add h1 h2
      _ = 2 / (N + 1) := by ring
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)

/-- The classical real number denoted by a regular sequence. -/
noncomputable def toReal (x : Reg) : ℝ := limUnder atTop (fun n => ((x.approx n : ℝ)))

lemma tendsto_toReal (x : Reg) :
    Tendsto (fun n => ((x.approx n : ℝ))) atTop (𝓝 x.toReal) :=
  x.cauchySeq.tendsto_limUnder

/-- **Explicit modulus.**  The `n`-th rational approximation of a Bishop real is
within `1/(n+1)` of the real number it denotes. -/
theorem abs_toReal_sub_approx_le (x : Reg) (n : ℕ) :
    |x.toReal - (x.approx n : ℝ)| ≤ 1 / (n + 1) := by
  have h1 : Tendsto (fun j : ℕ => |(x.approx j : ℝ) - (x.approx n : ℝ)|) atTop
      (𝓝 |x.toReal - (x.approx n : ℝ)|) :=
    (x.tendsto_toReal.sub tendsto_const_nhds).abs
  have h2 : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1) + 1 / (n + 1)) atTop
      (𝓝 (0 + 1 / (n + 1))) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add tendsto_const_nhds
  have := le_of_tendsto_of_tendsto' h1 h2 (fun j => x.regular_real j n)
  simpa using this


/-- Bishop's equality of real numbers: `x = y` means `|x n - y n| ≤ 2/(n+1)` for all
`n`.  (Constructively this is a *definition*, not a derived notion.) -/
def Equiv (x y : Reg) : Prop := ∀ n : ℕ, |x.approx n - y.approx n| ≤ 2 / (n + 1)






/-! ## Constructive completeness

A *regular sequence of reals* is a sequence `x : ℕ → Reg` with
`|x k - x l| ≤ 1/(k+1) + 1/(l+1)`.  Bishop's completeness theorem builds its limit
by an explicit diagonal formula, together with an explicit rate of convergence. -/

/-- A sequence of Bishop reals which is Cauchy with the canonical explicit modulus. -/
def IsRegularSeqOfReals (x : ℕ → Reg) : Prop :=
  ∀ k l : ℕ, |(x k).toReal - (x l).toReal| ≤ 1 / (k + 1) + 1 / (l + 1)

lemma diag_regular {x : ℕ → Reg} (hx : IsRegularSeqOfReals x) (m n : ℕ) :
    |(x (2 * m + 1)).approx (2 * m + 1) - (x (2 * n + 1)).approx (2 * n + 1)|
      ≤ 1 / (m + 1) + 1 / (n + 1) := by
  have key : ∀ j : ℕ, |((x (2 * j + 1)).approx (2 * j + 1) : ℝ) - (x (2 * j + 1)).toReal|
      ≤ 1 / (2 * (j : ℝ) + 2) := by
    intro j
    have h := (x (2 * j + 1)).abs_toReal_sub_approx_le (2 * j + 1)
    rw [abs_sub_comm] at h
    have : ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 2 := by push_cast; ring
    rwa [this] at h
  have hm := key m
  have hn := key n
  have hmn := hx (2 * m + 1) (2 * n + 1)
  have e1 : ((2 * m + 1 : ℕ) : ℝ) + 1 = 2 * (m : ℝ) + 2 := by push_cast; ring
  have e2 : ((2 * n + 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 2 := by push_cast; ring
  rw [e1, e2] at hmn
  have hR : |((x (2 * m + 1)).approx (2 * m + 1) : ℝ)
        - ((x (2 * n + 1)).approx (2 * n + 1) : ℝ)| ≤ 1 / (m + 1) + 1 / (n + 1) := by
    have h1 : |((x (2 * m + 1)).approx (2 * m + 1) : ℝ)
          - ((x (2 * n + 1)).approx (2 * n + 1) : ℝ)|
        ≤ |((x (2 * m + 1)).approx (2 * m + 1) : ℝ) - (x (2 * m + 1)).toReal|
          + |(x (2 * m + 1)).toReal - ((x (2 * n + 1)).approx (2 * n + 1) : ℝ)| :=
      abs_sub_le _ _ _
    have h2 : |(x (2 * m + 1)).toReal - ((x (2 * n + 1)).approx (2 * n + 1) : ℝ)|
        ≤ |(x (2 * m + 1)).toReal - (x (2 * n + 1)).toReal|
          + |(x (2 * n + 1)).toReal - ((x (2 * n + 1)).approx (2 * n + 1) : ℝ)| :=
      abs_sub_le _ _ _
    have hn' : |(x (2 * n + 1)).toReal - ((x (2 * n + 1)).approx (2 * n + 1) : ℝ)|
        ≤ 1 / (2 * (n : ℝ) + 2) := by rw [abs_sub_comm]; exact hn
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ea : (1 : ℝ) / (2 * (m : ℝ) + 2) = (1 / ((m : ℝ) + 1)) / 2 := by
      rw [div_div]; ring_nf
    have eb : (1 : ℝ) / (2 * (n : ℝ) + 2) = (1 / ((n : ℝ) + 1)) / 2 := by
      rw [div_div]; ring_nf
    rw [ea] at hm hmn
    rw [eb] at hn' hmn
    linarith
  have h' : ((|(x (2 * m + 1)).approx (2 * m + 1) - (x (2 * n + 1)).approx (2 * n + 1)| : ℚ) : ℝ)
      ≤ (((1 : ℚ) / (m + 1) + 1 / (n + 1) : ℚ) : ℝ) := by
    push_cast
    simpa using hR
  exact_mod_cast h'

/-- **Constructive completeness (Bishop).**  The limit of a regular sequence of
Bishop reals, given by the explicit diagonal `n ↦ (x_{2n+1})_{2n+1}`. -/
def limit {x : ℕ → Reg} (hx : IsRegularSeqOfReals x) : Reg where
  approx n := (x (2 * n + 1)).approx (2 * n + 1)
  regular := diag_regular hx


end Reg





end Bishop


