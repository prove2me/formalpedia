-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.green_lower_from_block_heat
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:20:55.590096+00:00
-- url     : https://prove2.me/submissions/155d8213-6686-4cbf-bcb8-0ee6dff52784

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin: Tanaka telescoping ⟹ window occupation lower bound

Telescoping the single-step `|D|`-drift (brick 85) over the evolving distribution `distPow K μ₀ t`
(the law of the walk after `t` steps) yields, for a mean-preserving bounded-increment kernel,

  `E|D_T| − E|D_0| ≤ b · ∑_{t<T} (window-occupation at step t)`,

i.e. `window-occupation ≥ (E|D_T| − E|D_0|)/b`.  Combined with the Paley–Zygmund bound `E|D_T| ≥ c√T`
(brick 84) and the per-step second/fourth moments of the Erdős rank-difference walk, this gives the
occupation lower bound `≥ 1/δ` that closes the Hardy–Ramanujan convergence.  All deterministic finite-sum
algebra.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

lemma distPow_nonneg (K : ι → ι → ℝ) (μ0 : ι → ℝ) (hKnn : ∀ x z, 0 ≤ K x z)
    (hμ0 : ∀ x, 0 ≤ μ0 x) : ∀ t x, 0 ≤ distPow K μ0 t x := by
  intro t
  induction t with
  | zero => exact hμ0
  | succ t ih => exact fun z => Finset.sum_nonneg (fun x _ => mul_nonneg (ih x) (hKnn x z))

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Fact B via Doeblin: quadratic-variation telescoping (Doob decomposition for `D²`)

For a mean-preserving kernel, `D²` has Doob compensator equal to the cumulative local variance
`locVar x = ∑_z K x z (D z − D x)²`:

  `E[D_T²] − E[D_0²] = ∑_{t<T} ∑_x distPow t x · locVar x`.

With a uniform local-variance lower bound `v₀ ≤ locVar` this gives `E[D_T²] ≥ E[D_0²] + v₀·T`, the lower
quadratic-variation feeding the Paley–Zygmund bound `E|D_T| ≥ c√T`.  Deterministic finite-sum.
Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- The law `distPow` stays a probability distribution. -/
lemma distPow_sum (K : ι → ι → ℝ) (μ0 : ι → ℝ) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0 : ∑ x, μ0 x = 1) : ∀ t, ∑ x, distPow K μ0 t x = 1 := by
  intro t
  induction t with
  | zero => exact hμ0
  | succ t ih =>
    simp only [distPow]
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (fun x _ => by rw [← Finset.mul_sum, hKsum x, mul_one])]
    exact ih

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Green lower bridge from block heat + second-moment tightness (renewal route B, Layer 1)

This is the *deterministic finite-sum* bridge of the two-layer split (ChatGPT R8):
given a per-block heat lower bound `hblock` (`c0/√(m+1) ≤` window mass from a tight start) and a
second-moment tightness bound `hM2` (`∑ distPow·D² ≤ V(m+1)`), the cumulative window occupation over
a horizon `T` is `≥ (c0/8)·√T`.  No probability/measure theory — pure `Finset` algebra:

* `good_mass_ge_half` — Chebyshev/Markov: ≥ ½ of the law sits in `{|D| ≤ Λ√(m+1)}`.
* `distPow_expect_comp` — Chapman–Kolmogorov in expectation form (induction on the recursive `distPow`).
* `even_time_windowMass_lower` — one even-time block: feed `hblock` from each good start.
* `sum_Icc_one_div_sqrt_succ_ge` + `sqrt_T_quarter_le_sqrt_half_minus_one` — the `∑ 1/√(m+1) ≥ √T/4`
  telescope (no integrals).
* `green_lower_from_block_heat` — the assembled bridge, constant `c ≤ c0/8`, needs `16 ≤ T`.

The remaining wall is the *Layer 2* input `hblock` itself (`erdos_rankdiff_block_heat_lower`); this file
discharges everything around it.  (Bridge authored via ChatGPT ac2 R8, verified against the repo
`distPow` API and rebuilt clean-3.)
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Point mass at `x`, as a row vector. -/
private def pointMass (x : α) : α → ℝ :=
  fun z => if z = x then 1 else 0

private lemma pointMass_nonneg (x z : α) :
    0 ≤ pointMass x z := by
  unfold pointMass
  split <;> norm_num

private lemma pointMass_sum_mul (x : α) (φ : α → ℝ) :
    ∑ z, pointMass x z * φ z = φ x := by
  classical
  simp [pointMass]

/-- Window occupation mass at time `t`. -/
private def windowMass
    (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ) (W : ℝ) (t : ℕ) : ℝ :=
  ∑ x, distPow K μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0)

private lemma windowMass_nonneg
    (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ) (W : ℝ) (t : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hμ0nn : ∀ x, 0 ≤ μ0 x) :
    0 ≤ windowMass K D μ0 W t := by
  unfold windowMass
  refine Finset.sum_nonneg ?_
  intro x _
  exact mul_nonneg
    (distPow_nonneg K μ0 hKnn hμ0nn t x)
    (by split <;> norm_num)

/-- One-step expectation form of the recursive definition of `distPow`. -/
private lemma distPow_succ_expect
    (K : α → α → ℝ) (μ0 : α → ℝ) (t : ℕ) (φ : α → ℝ) :
    (∑ z, distPow K μ0 (t + 1) z * φ z)
      =
    ∑ x, distPow K μ0 t x * (∑ z, K x z * φ z) := by
  simp only [distPow]
  calc
    (∑ z, (∑ x, distPow K μ0 t x * K x z) * φ z)
        =
      ∑ z, ∑ x, distPow K μ0 t x * K x z * φ z := by
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [Finset.sum_mul]
    _ =
      ∑ x, ∑ z, distPow K μ0 t x * K x z * φ z := by
        rw [Finset.sum_comm]
    _ =
      ∑ x, distPow K μ0 t x * (∑ z, K x z * φ z) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro z _
        ring

/-- Chapman–Kolmogorov in expectation form:
`E_{μ K^(m+n)} φ = E_{x∼μK^m} E_{δ_x K^n} φ`. -/
private lemma distPow_expect_comp
    (K : α → α → ℝ) (μ0 : α → ℝ) (m n : ℕ) (φ : α → ℝ) :
    (∑ z, distPow K μ0 (m + n) z * φ z)
      =
    ∑ x, distPow K μ0 m x *
      (∑ z, distPow K (pointMass x) n z * φ z) := by
  induction n generalizing φ with
  | zero =>
      calc
        (∑ z, distPow K μ0 (m + 0) z * φ z)
            =
          ∑ z, distPow K μ0 m z * φ z := by
            rw [Nat.add_zero]
        _ =
          ∑ x, distPow K μ0 m x *
            (∑ z, pointMass x z * φ z) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [pointMass_sum_mul]
        _ =
          ∑ x, distPow K μ0 m x *
            (∑ z, distPow K (pointMass x) 0 z * φ z) := by
            simp [distPow]
  | succ n ih =>
      calc
        (∑ z, distPow K μ0 (m + (n + 1)) z * φ z)
            =
          ∑ z, distPow K μ0 ((m + n) + 1) z * φ z := by
            rw [Nat.add_succ]
        _ =
          ∑ u, distPow K μ0 (m + n) u * (∑ z, K u z * φ z) := by
            rw [distPow_succ_expect]
        _ =
          ∑ x, distPow K μ0 m x *
            (∑ u, distPow K (pointMass x) n u *
              (∑ z, K u z * φ z)) := by
            exact ih (fun u => ∑ z, K u z * φ z)
        _ =
          ∑ x, distPow K μ0 m x *
            (∑ z, distPow K (pointMass x) (n + 1) z * φ z) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [distPow_succ_expect]

/-- The good-start indicator at block size `m`. -/
private def goodInd (D : α → ℝ) (Λ : ℝ) (m : ℕ) (x : α) : ℝ :=
  if |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1) then 1 else 0

/-- The complementary bad-start indicator. -/
private def badInd (D : α → ℝ) (Λ : ℝ) (m : ℕ) (x : α) : ℝ :=
  if |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1) then 0 else 1

private lemma badInd_nonneg (D : α → ℝ) (Λ : ℝ) (m : ℕ) (x : α) :
    0 ≤ badInd D Λ m x := by
  unfold badInd
  split <;> norm_num

private lemma good_add_bad (D : α → ℝ) (Λ : ℝ) (m : ℕ) (x : α) :
    goodInd D Λ m x + badInd D Λ m x = 1 := by
  unfold goodInd badInd
  split <;> norm_num

/-- Finite-sum Chebyshev/Markov tightness: if `E[D²] ≤ V(m+1)` and `2V ≤ Λ²`, then at least half of
the law is in `{|D| ≤ Λ√(m+1)}`. -/
private lemma good_mass_ge_half
    (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ)
    (Λ V : ℝ) (T m : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hM2 : ∀ m, m ≤ T / 2 →
      ∑ x, distPow K μ0 m x * (D x) ^ 2 ≤ V * ((m : ℝ) + 1))
    (hΛpos : 0 < Λ) (hΛ : 2 * V ≤ Λ ^ 2)
    (hmT : m ≤ T / 2) :
    (1 / 2 : ℝ)
      ≤ ∑ x, distPow K μ0 m x * goodInd D Λ m x := by
  classical
  set R : ℝ := Λ * Real.sqrt ((m : ℝ) + 1) with hRdef
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  have hspos : 0 < Real.sqrt ((m : ℝ) + 1) :=
    Real.sqrt_pos.mpr hmpos
  have hRpos : 0 < R := by
    rw [hRdef]
    exact mul_pos hΛpos hspos
  have hR2 : R ^ 2 = Λ ^ 2 * ((m : ℝ) + 1) := by
    rw [hRdef, mul_pow, Real.sq_sqrt hmpos.le]
  have hΛ2pos : 0 < Λ ^ 2 := sq_pos_of_pos hΛpos

  let ν : α → ℝ := fun x => distPow K μ0 m x
  have hνnn : ∀ x, 0 ≤ ν x := by
    intro x
    exact distPow_nonneg K μ0 hKnn hμ0nn m x

  set G : ℝ := ∑ x, ν x * goodInd D Λ m x with hGdef
  set B : ℝ := ∑ x, ν x * badInd D Λ m x with hBdef

  have hBnn : 0 ≤ B := by
    rw [hBdef]
    refine Finset.sum_nonneg ?_
    intro x _
    exact mul_nonneg (hνnn x) (badInd_nonneg D Λ m x)

  have hbad_sq : ∀ x, badInd D Λ m x * R ^ 2 ≤ (D x) ^ 2 := by
    intro x
    unfold badInd
    by_cases hx : |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1)
    · simp [hx]
      exact sq_nonneg (D x)
    · simp [hx]
      have hlt : R < |D x| := by
        rw [hRdef]
        exact lt_of_not_ge hx
      have hs : R ^ 2 ≤ |D x| ^ 2 :=
        pow_le_pow_left₀ hRpos.le hlt.le 2
      simpa [sq_abs] using hs

  have hbadM2 :
      B * R ^ 2 ≤ ∑ x, distPow K μ0 m x * (D x) ^ 2 := by
    rw [hBdef]
    change (∑ x, ν x * badInd D Λ m x) * R ^ 2
        ≤ ∑ x, distPow K μ0 m x * (D x) ^ 2
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro x _
    calc
      ν x * badInd D Λ m x * R ^ 2
          = ν x * (badInd D Λ m x * R ^ 2) := by ring
      _ ≤ ν x * (D x) ^ 2 :=
          mul_le_mul_of_nonneg_left (hbad_sq x) (hνnn x)
      _ = distPow K μ0 m x * (D x) ^ 2 := rfl

  have hbadBound :
      B * R ^ 2 ≤ V * ((m : ℝ) + 1) :=
    le_trans hbadM2 (hM2 m hmT)

  have hbadΛ : B * Λ ^ 2 ≤ V := by
    rw [hR2] at hbadBound
    have h' : (B * Λ ^ 2) * ((m : ℝ) + 1)
        ≤ V * ((m : ℝ) + 1) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hbadBound
    exact le_of_mul_le_mul_right h' hmpos

  have hBhalf : B ≤ 1 / 2 := by
    have htmp : 2 * B * Λ ^ 2 ≤ 1 * Λ ^ 2 := by
      nlinarith [hbadΛ, hΛ]
    have h2B : 2 * B ≤ 1 := le_of_mul_le_mul_right htmp hΛ2pos
    linarith

  have hGB : G + B = 1 := by
    rw [hGdef, hBdef]
    calc
      (∑ x, ν x * goodInd D Λ m x) +
          (∑ x, ν x * badInd D Λ m x)
          =
        ∑ x, ν x * (goodInd D Λ m x + badInd D Λ m x) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
      _ = ∑ x, ν x := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [good_add_bad]
          ring
      _ = 1 := by
          dsimp [ν]
          exact distPow_sum K μ0 hKsum hμ0sum m

  show (1 / 2 : ℝ) ≤ G
  linarith

/-- One even-time block lower bound: at time `2m`, expose the law at time `m`; at least half the mass
is on good starts, each contributing the block heat lower bound. -/
private lemma even_time_windowMass_lower
    (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ)
    (W Λ c0 V : ℝ) (T m : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hM2 : ∀ m, m ≤ T / 2 →
      ∑ x, distPow K μ0 m x * (D x) ^ 2 ≤ V * ((m : ℝ) + 1))
    (hΛpos : 0 < Λ) (hΛ : 2 * V ≤ Λ ^ 2) (hc0 : 0 ≤ c0)
    (hblock : ∀ m, m ≤ T / 2 → 1 ≤ m → ∀ x,
      |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1) →
        c0 / Real.sqrt ((m : ℝ) + 1)
          ≤ ∑ y, distPow K (fun z => if z = x then 1 else 0) m y *
              (if |D y| ≤ W then (1 : ℝ) else 0))
    (hmT : m ≤ T / 2) (hm1 : 1 ≤ m) :
    c0 / (2 * Real.sqrt ((m : ℝ) + 1))
      ≤ windowMass K D μ0 W (2 * m) := by
  classical
  set s : ℝ := Real.sqrt ((m : ℝ) + 1) with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.mpr (by positivity)
  have hcs_nonneg : 0 ≤ c0 / s := by
    exact div_nonneg hc0 hspos.le

  let φ : α → ℝ := fun y => if |D y| ≤ W then (1 : ℝ) else 0

  have hgood :=
    good_mass_ge_half K D μ0 Λ V T m hKnn hKsum hμ0nn hμ0sum
      hM2 hΛpos hΛ hmT

  have hinner_nonneg :
      ∀ x, 0 ≤ ∑ y, distPow K (pointMass x) m y * φ y := by
    intro x
    refine Finset.sum_nonneg ?_
    intro y _
    exact mul_nonneg
      (distPow_nonneg K (pointMass x) hKnn (pointMass_nonneg x) m y)
      (by dsimp [φ]; split <;> norm_num)

  have hinner_good :
      ∀ x,
        goodInd D Λ m x * (c0 / s)
          ≤ ∑ y, distPow K (pointMass x) m y * φ y := by
    intro x
    unfold goodInd
    by_cases hx : |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1)
    · simp [hx]
      have hb := hblock m hmT hm1 x hx
      simpa [pointMass, φ, hsdef] using hb
    · simp [hx]
      exact hinner_nonneg x

  have hweighted :
      (c0 / s) * (∑ x, distPow K μ0 m x * goodInd D Λ m x)
        ≤
      ∑ x, distPow K μ0 m x *
        (∑ y, distPow K (pointMass x) m y * φ y) := by
    calc
      (c0 / s) * (∑ x, distPow K μ0 m x * goodInd D Λ m x)
          =
        ∑ x, distPow K μ0 m x * (goodInd D Λ m x * (c0 / s)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
      _ ≤
        ∑ x, distPow K μ0 m x *
          (∑ y, distPow K (pointMass x) m y * φ y) := by
          refine Finset.sum_le_sum ?_
          intro x _
          exact mul_le_mul_of_nonneg_left
            (hinner_good x)
            (distPow_nonneg K μ0 hKnn hμ0nn m x)

  have hhalf :
      c0 / (2 * s)
        ≤ (c0 / s) * (∑ x, distPow K μ0 m x * goodInd D Λ m x) := by
    calc
      c0 / (2 * s) = (c0 / s) * (1 / 2) := by field_simp [hspos.ne']
      _ ≤ (c0 / s) * (∑ x, distPow K μ0 m x * goodInd D Λ m x) :=
          mul_le_mul_of_nonneg_left hgood hcs_nonneg

  have hCK :
      windowMass K D μ0 W (m + m)
        =
      ∑ x, distPow K μ0 m x *
        (∑ y, distPow K (pointMass x) m y * φ y) := by
    unfold windowMass
    dsimp [φ]
    exact distPow_expect_comp K μ0 m m φ

  have htwo : m + m = 2 * m := by omega

  calc
    c0 / (2 * Real.sqrt ((m : ℝ) + 1))
        = c0 / (2 * s) := by rw [hsdef]
    _ ≤ (c0 / s) * (∑ x, distPow K μ0 m x * goodInd D Λ m x) := hhalf
    _ ≤ ∑ x, distPow K μ0 m x *
        (∑ y, distPow K (pointMass x) m y * φ y) := hweighted
    _ = windowMass K D μ0 W (2 * m) := by
        rw [← hCK, htwo]

/-- The elementary telescope term used in the final summation. -/
private lemma sqrt_succ_sub_sqrt_le_inv_sqrt_succ (m : ℕ) :
    Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)
      ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hm1pos : 0 < (m : ℝ) + 1 := by positivity
  have hs1pos : 0 < Real.sqrt ((m : ℝ) + 1) :=
    Real.sqrt_pos.mpr hm1pos
  have hdenpos :
      0 < Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ) := by
    positivity
  have hdiff :
      Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)
        =
      1 / (Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ)) := by
    rw [eq_div_iff hdenpos.ne']
    have h1 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 :=
      Real.sq_sqrt hm1pos.le
    have h0 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
      Real.sq_sqrt hm0
    nlinarith
  rw [hdiff]
  exact one_div_le_one_div_of_le hs1pos
    (by nlinarith [Real.sqrt_nonneg (m : ℝ)])

/-- `∑_{m=1}^N 1/√(m+1) ≥ √(N+1) - 1`. -/
private lemma sum_Icc_one_div_sqrt_succ_ge (N : ℕ) :
    Real.sqrt ((N : ℝ) + 1) - 1
      ≤ ∑ m ∈ Finset.Icc 1 N, 1 / Real.sqrt ((m : ℝ) + 1) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hstep :=
        sqrt_succ_sub_sqrt_le_inv_sqrt_succ (N + 1)
      have htop : 1 ≤ N + 1 := by omega
      rw [Finset.sum_Icc_succ_top htop]
      calc
        Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) - 1
            =
          (Real.sqrt ((N : ℝ) + 1) - 1)
            + (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1)
                - Real.sqrt ((N : ℝ) + 1)) := by
            push_cast
            ring
        _ ≤
          (∑ m ∈ Finset.Icc 1 N, 1 / Real.sqrt ((m : ℝ) + 1))
            + 1 / Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) := by
            have hrewrite :
                Real.sqrt (((N + 1 : ℕ) : ℝ) + 1)
                  - Real.sqrt ((N : ℝ) + 1)
                =
                Real.sqrt (((N + 1 : ℕ) : ℝ) + 1)
                  - Real.sqrt ((N + 1 : ℕ) : ℝ) := by norm_num
            rw [hrewrite]
            exact add_le_add ih hstep

/-- Summing the even-time block lower bounds inside the full Green sum (using `N = (T-1)/2`,
so `2m < T` for all `m ∈ Icc 1 N`). -/
private lemma green_sum_lower_by_even_blocks
    (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ)
    (W Λ c0 V : ℝ) (T : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hM2 : ∀ m, m ≤ T / 2 →
      ∑ x, distPow K μ0 m x * (D x) ^ 2 ≤ V * ((m : ℝ) + 1))
    (hΛpos : 0 < Λ) (hΛ : 2 * V ≤ Λ ^ 2) (hc0 : 0 ≤ c0)
    (hblock : ∀ m, m ≤ T / 2 → 1 ≤ m → ∀ x,
      |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1) →
        c0 / Real.sqrt ((m : ℝ) + 1)
          ≤ ∑ y, distPow K (fun z => if z = x then 1 else 0) m y *
              (if |D y| ≤ W then (1 : ℝ) else 0)) :
    (∑ m ∈ Finset.Icc 1 ((T - 1) / 2),
        c0 / (2 * Real.sqrt ((m : ℝ) + 1)))
      ≤
    ∑ t ∈ Finset.range T, windowMass K D μ0 W t := by
  classical
  set N : ℕ := (T - 1) / 2 with hNdef
  let F : ℕ → ℝ := fun t => windowMass K D μ0 W t

  have hNle : N ≤ T / 2 := by
    rw [hNdef]
    omega

  have hsub :
      (Finset.Icc 1 N).image (fun m => 2 * m) ⊆ Finset.range T := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨m, hm, rfl⟩
    simp only [Finset.mem_range]
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmle : m ≤ N := (Finset.mem_Icc.mp hm).2
    rw [hNdef] at hmle
    omega

  have hnonneg_out :
      ∀ t ∈ Finset.range T,
        t ∉ (Finset.Icc 1 N).image (fun m => 2 * m) →
          0 ≤ F t := by
    intro t _ _
    exact windowMass_nonneg K D μ0 W t hKnn hμ0nn

  have hrestrict :
      (∑ t ∈ (Finset.Icc 1 N).image (fun m => 2 * m), F t)
        ≤ ∑ t ∈ Finset.range T, F t :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg_out

  have himage :
      (∑ t ∈ (Finset.Icc 1 N).image (fun m => 2 * m), F t)
        =
      ∑ m ∈ Finset.Icc 1 N, F (2 * m) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    simp only [] at hab
    omega

  have hpoint :
      ∀ m ∈ Finset.Icc 1 N,
        c0 / (2 * Real.sqrt ((m : ℝ) + 1)) ≤ F (2 * m) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
    have hmT : m ≤ T / 2 := le_trans hmN hNle
    exact even_time_windowMass_lower K D μ0 W Λ c0 V T m
      hKnn hKsum hμ0nn hμ0sum hM2 hΛpos hΛ hc0 hblock hmT hm1

  calc
    (∑ m ∈ Finset.Icc 1 ((T - 1) / 2),
        c0 / (2 * Real.sqrt ((m : ℝ) + 1)))
        =
      ∑ m ∈ Finset.Icc 1 N,
        c0 / (2 * Real.sqrt ((m : ℝ) + 1)) := by
        rw [hNdef]
    _ ≤ ∑ m ∈ Finset.Icc 1 N, F (2 * m) :=
        Finset.sum_le_sum hpoint
    _ =
      ∑ t ∈ (Finset.Icc 1 N).image (fun m => 2 * m), F t := by
        rw [himage]
    _ ≤ ∑ t ∈ Finset.range T, F t := hrestrict

/-- A coarse arithmetic conversion: for `16 ≤ T`, with `N = (T-1)/2`, `√T / 4 ≤ √(N+1) - 1`. -/
private lemma sqrt_T_quarter_le_sqrt_half_minus_one
    (T : ℕ) (hT : 16 ≤ T) :
    Real.sqrt (T : ℝ) / 4
      ≤ Real.sqrt ((((T - 1) / 2 : ℕ) : ℝ) + 1) - 1 := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 16) hT)
  have hsqrtT4 : 4 ≤ Real.sqrt (T : ℝ) := by
    have h16 : (16 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hs := Real.sqrt_le_sqrt h16
    norm_num at hs
    exact hs

  have hnat : T ≤ 4 * (((T - 1) / 2) + 1) := by
    omega
  have hreal : (T : ℝ) / 4
      ≤ ((((T - 1) / 2 : ℕ) : ℝ) + 1) := by
    have hcast : (T : ℝ) ≤ 4 * ((((T - 1) / 2 : ℕ) : ℝ) + 1) := by
      exact_mod_cast hnat
    nlinarith

  have hsqrt_half :
      Real.sqrt (T : ℝ) / 2
        ≤ Real.sqrt ((((T - 1) / 2 : ℕ) : ℝ) + 1) := by
    have hsq :
        (Real.sqrt (T : ℝ) / 2) ^ 2
          ≤ (Real.sqrt ((((T - 1) / 2 : ℕ) : ℝ) + 1)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hTpos.le,
        Real.sq_sqrt (by positivity : 0 ≤ ((((T - 1) / 2 : ℕ) : ℝ) + 1))]
      nlinarith [hreal]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

  calc
    Real.sqrt (T : ℝ) / 4
        ≤ Real.sqrt (T : ℝ) / 2 - 1 := by
          nlinarith
    _ ≤ Real.sqrt ((((T - 1) / 2 : ℕ) : ℝ) + 1) - 1 := by
          linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem solution
    (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ)
    (W Λ c0 V c : ℝ) (T : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hM2 : ∀ m, m ≤ T / 2 →
      ∑ x, distPow K μ0 m x * (D x) ^ 2 ≤ V * ((m : ℝ) + 1))
    (hΛpos : 0 < Λ) (hΛ : 2 * V ≤ Λ ^ 2)
    (hc0 : 0 ≤ c0) (hT : 16 ≤ T) (hc : c ≤ c0 / 8)
    (hblock : ∀ m, m ≤ T / 2 → 1 ≤ m → ∀ x,
      |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1) →
        c0 / Real.sqrt ((m : ℝ) + 1)
          ≤ ∑ y, distPow K (fun z => if z = x then 1 else 0) m y *
              (if |D y| ≤ W then (1 : ℝ) else 0)) :
    c * Real.sqrt (T : ℝ)
      ≤ ∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x *
            (if |D x| ≤ W then (1 : ℝ) else 0) := by
  classical
  set N : ℕ := (T - 1) / 2 with hNdef

  have hsqrt_nonneg : 0 ≤ Real.sqrt (T : ℝ) := Real.sqrt_nonneg _

  have htel :
      (c0 / 2) * (Real.sqrt ((N : ℝ) + 1) - 1)
        ≤
      ∑ m ∈ Finset.Icc 1 N,
        c0 / (2 * Real.sqrt ((m : ℝ) + 1)) := by
    have hbase := sum_Icc_one_div_sqrt_succ_ge N
    have hcoef : 0 ≤ c0 / 2 := by positivity
    calc
      (c0 / 2) * (Real.sqrt ((N : ℝ) + 1) - 1)
          ≤
        (c0 / 2) *
          (∑ m ∈ Finset.Icc 1 N, 1 / Real.sqrt ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hbase hcoef
      _ =
        ∑ m ∈ Finset.Icc 1 N,
          c0 / (2 * Real.sqrt ((m : ℝ) + 1)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro m _
          rw [mul_one_div, div_div]

  have hblocks :
      (∑ m ∈ Finset.Icc 1 N,
        c0 / (2 * Real.sqrt ((m : ℝ) + 1)))
        ≤
      ∑ t ∈ Finset.range T, windowMass K D μ0 W t := by
    rw [hNdef]
    exact green_sum_lower_by_even_blocks K D μ0 W Λ c0 V T
      hKnn hKsum hμ0nn hμ0sum hM2 hΛpos hΛ hc0 hblock

  have hquarter :
      Real.sqrt (T : ℝ) / 4
        ≤ Real.sqrt ((N : ℝ) + 1) - 1 := by
    rw [hNdef]
    exact sqrt_T_quarter_le_sqrt_half_minus_one T hT

  have hconst :
      (c0 / 8) * Real.sqrt (T : ℝ)
        ≤ (c0 / 2) * (Real.sqrt ((N : ℝ) + 1) - 1) := by
    have hcoef : 0 ≤ c0 / 2 := by positivity
    calc
      (c0 / 8) * Real.sqrt (T : ℝ)
          =
        (c0 / 2) * (Real.sqrt (T : ℝ) / 4) := by ring
      _ ≤ (c0 / 2) * (Real.sqrt ((N : ℝ) + 1) - 1) :=
        mul_le_mul_of_nonneg_left hquarter hcoef

  calc
    c * Real.sqrt (T : ℝ)
        ≤ (c0 / 8) * Real.sqrt (T : ℝ) :=
          mul_le_mul_of_nonneg_right hc hsqrt_nonneg
    _ ≤ (c0 / 2) * (Real.sqrt ((N : ℝ) + 1) - 1) := hconst
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
          c0 / (2 * Real.sqrt ((m : ℝ) + 1)) := htel
    _ ≤ ∑ t ∈ Finset.range T, windowMass K D μ0 W t := hblocks
    _ =
      ∑ t ∈ Finset.range T,
        ∑ x, distPow K μ0 t x *
          (if |D x| ≤ W then (1 : ℝ) else 0) := by
        rfl
