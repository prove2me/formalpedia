-- Prove2me | solution 1 for conditional_khintchine_scale_moment_from_row_column_energy_moment_2pN
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-25T09:34:06.466216+00:00
-- url     : https://prove2.me/submissions/f49f8fb9-8b33-4df9-8c4c-5b25522bc475

import Definitions.Def_matrix_completion_rademacher
import Mathlib

open MatrixCompletion
open scoped Classical BigOperators

/-!
# `conditional_khintchine_scale_moment_from_row_column_energy_moment`

Convert the Bernoulli moment of the conditional Khintchine scale
`(Ckh·√q·p⁻¹·√maxEnergy)^q` into the displayed `(Crad·√(qN/p)·‖X‖_∞)^q` bound,
using the row/column energy moment estimate `bExp[maxEnergy^q] ≤ (Cenergy·p·N·‖X‖_∞²)^q`
from Lemma 6.2.

Key step (power mean / Jensen on the probability average `bernoulliExpectation`):
with `Y = maxEnergy ≥ 0`,
  `bExp[(√Y)^q] = bExp[(Y^q)^{1/2}] ≤ (bExp[Y^q])^{1/2}`
since `t ↦ t^{1/2}` is concave on `[0,∞)` and the Bernoulli weights are nonneg
summing to one.  The remaining algebra gives `Crad = Ckh·√Cenergy`; both the
non-degenerate `p > 0` case and the degenerate `p = 0` case (where both sides are
`0`) are subsumed by the real identities `√p·p⁻¹ = √(p⁻¹)` and `0 ^ q = 0`.
-/

namespace CondKhintchineScale

/-! ## Bernoulli weight facts (nonneg, sum to one) -/

lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)

lemma bernoulliWeight_sum
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega) = 1 := by
  classical
  unfold bernoulliObservationWeight
  set N := Fintype.card (Fin n₁ × Fin n₂) with hN
  have huniv :
      (Finset.univ : Finset (Finset (Fin n₁ × Fin n₂)))
        = (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset := by
    ext S; simp
  rw [huniv, Finset.sum_powerset]
  have hcard : (Finset.univ : Finset (Fin n₁ × Fin n₂)).card = N := by
    rw [Finset.card_univ]
  rw [hcard]
  have hbin := add_pow p (1 - p) N
  have hkey :
      ∀ k ∈ Finset.range (N + 1),
        (∑ t ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n₁ × Fin n₂)),
            p ^ t.card * (1 - p) ^ (N - t.card))
          = (N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    intro k _
    rw [Finset.sum_congr rfl (by
      intro t ht
      rw [(Finset.mem_powersetCard.mp ht).2])]
    rw [Finset.sum_const, Finset.card_powersetCard, hcard, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hkey]
  have hsum :
      (∑ k ∈ Finset.range (N + 1),
        (N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k)))
        = (p + (1 - p)) ^ N := by
    rw [hbin]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [hsum]; ring_nf

/-! ## Jensen power mean for `bernoulliExpectation` (square-root version) -/

lemma bExp_sqrt_le_sqrt_bExp
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (g : Finset (Fin n₁ × Fin n₂) → ℝ) (hg : ∀ Omega, 0 ≤ g Omega) :
    bernoulliExpectation p (fun Omega => Real.rpow (g Omega) (1 / 2))
      ≤ Real.rpow (bernoulliExpectation p g) (1 / 2) := by
  have ht0 : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  have ht1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    Real.concaveOn_rpow ht0 ht1
  unfold bernoulliExpectation
  have hjensen := hconc.le_map_sum
    (t := (Finset.univ : Finset (Finset (Fin n₁ × Fin n₂))))
    (w := bernoulliObservationWeight p)
    (p := g)
    (fun i _ => bernoulliObservationWeight_nonneg hp hp1 i)
    (by simpa using (bernoulliWeight_sum (n₁ := n₁) (n₂ := n₂) (p := p)))
    (fun i _ => hg i)
  simp only [smul_eq_mul] at hjensen
  exact hjensen

/-! ## monotonicity of `bernoulliExpectation` -/

lemma bExp_mono
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : Finset (Fin n₁ × Fin n₂) → ℝ}
    (h : ∀ Omega, F Omega ≤ G Omega) :
    bernoulliExpectation p F ≤ bernoulliExpectation p G := by
  unfold bernoulliExpectation
  apply Finset.sum_le_sum
  intro Omega _
  exact mul_le_mul_of_nonneg_left (h Omega)
    (bernoulliObservationWeight_nonneg hp hp1 Omega)

/-! ## constant pulls out of `bernoulliExpectation` -/

lemma bExp_const_mul
    {n₁ n₂ : ℕ} (p c : ℝ) (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    bernoulliExpectation p (fun Omega => c * F Omega)
      = c * bernoulliExpectation p F := by
  unfold bernoulliExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Omega _; ring

/-! ## sqrt algebra helper: `√p · p⁻¹ = √(p⁻¹)` for `p ≥ 0` -/

lemma sqrt_mul_inv_eq_sqrt_inv {p : ℝ} (hp : 0 ≤ p) :
    Real.sqrt p * p⁻¹ = Real.sqrt p⁻¹ := by
  rcases eq_or_lt_of_le hp with hp0 | hppos
  · simp [← hp0]
  · have hlhs_nonneg : 0 ≤ Real.sqrt p * p⁻¹ :=
      mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hp)
    have hrhs_nonneg : 0 ≤ Real.sqrt p⁻¹ := Real.sqrt_nonneg _
    have hsq : (Real.sqrt p * p⁻¹) ^ 2 = (Real.sqrt p⁻¹) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hppos), Real.sq_sqrt (inv_nonneg.mpr hp)]
      field_simp
    nlinarith [hsq, hlhs_nonneg, hrhs_nonneg,
      sq_nonneg (Real.sqrt p * p⁻¹ - Real.sqrt p⁻¹)]

end CondKhintchineScale

open CondKhintchineScale


theorem solution
    (Cenergy Ckh : ℝ) :
    0 < Cenergy →
    0 < Ckh →
    ∃ Crad : ℝ, 0 < Crad ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (max (sampledRowEnergyMax Omega X)
                (sampledColumnEnergyMax Omega X)) ^ q) ≤
          (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              (Ckh * Real.sqrt (q : ℝ) *
                (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                Real.sqrt
                  (max (sampledRowEnergyMax Omega X)
                    (sampledColumnEnergyMax Omega X))) ^ q) ≤
          (Crad * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCenergy hCkh
  refine ⟨Ckh * Real.sqrt Cenergy, by positivity, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ hm _hmLower hqOne _hqLower _hqUpper _hqsample hEnergy
  -- abbreviations
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hNdef
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  set Y : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega => max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)
    with hY
  have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp_nonneg : 0 ≤ p := by rw [hp_def]; positivity
  have hp_le_one : p ≤ 1 := by
    rw [hp_def, div_le_one hden_pos]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
    simpa using this
  have hN_nonneg : 0 ≤ N := by rw [hNdef]; positivity
  have hentry_nonneg : 0 ≤ entrySupNorm X := by
    rw [show entrySupNorm X = ⨆ i : Fin n₁, ⨆ j : Fin n₂, |X i j| from rfl]
    refine le_trans (abs_nonneg (X ⟨0, hn₁⟩ ⟨0, hn₂⟩)) ?_
    refine le_trans
      (le_ciSup (Finite.bddAbove_range (fun j : Fin n₂ => |X ⟨0, hn₁⟩ j|)) ⟨0, hn₂⟩) ?_
    exact le_ciSup (Finite.bddAbove_range (fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)) ⟨0, hn₁⟩
  -- Y is nonneg
  have hY_nonneg : ∀ Omega, 0 ≤ Y Omega := by
    intro Omega
    rw [hY]
    refine le_trans ?_ (le_max_left _ _)
    unfold sampledRowEnergyMax
    refine le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, hn₁⟩ ?_
    apply Finset.sum_nonneg; intro j _; split <;> positivity
  -- constant factor pulls out of the LHS expectation
  set c : ℝ := Ckh * Real.sqrt (q : ℝ) * p⁻¹ with hc
  have hc_nonneg : 0 ≤ c := by
    rw [hc]; have : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_nonneg; positivity
  have hpull :
      bernoulliExpectation p (fun Omega => (c * Real.sqrt (Y Omega)) ^ q)
        = c ^ q * bernoulliExpectation p (fun Omega => (Real.sqrt (Y Omega)) ^ q) := by
    rw [← bExp_const_mul p (c ^ q) (fun Omega => (Real.sqrt (Y Omega)) ^ q)]
    apply Finset.sum_congr rfl
    intro Omega _
    show bernoulliObservationWeight p Omega * (c * Real.sqrt (Y Omega)) ^ q
        = bernoulliObservationWeight p Omega * (c ^ q * (Real.sqrt (Y Omega)) ^ q)
    rw [mul_pow]
  -- bound bExp[(√Y)^q] ≤ (bExp[Y^q])^{1/2}
  have hsqrtpow : ∀ Omega,
      (Real.sqrt (Y Omega)) ^ q = Real.rpow ((Y Omega) ^ q) (1 / 2) := by
    intro Omega
    have h1 : (Real.sqrt (Y Omega)) ^ q = Real.rpow (Y Omega) ((q : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_natCast (Y Omega ^ (1/2 : ℝ)) q]
      rw [← Real.rpow_mul (hY_nonneg Omega)]
      norm_num; ring_nf
    have h2 : Real.rpow ((Y Omega) ^ q) (1 / 2) = Real.rpow (Y Omega) ((q : ℝ) / 2) := by
      have he : ((Y Omega) ^ q : ℝ) = Real.rpow (Y Omega) (q : ℝ) :=
        (Real.rpow_natCast (Y Omega) q).symm
      rw [he]
      rw [show ((q : ℝ) / 2) = (q : ℝ) * (1 / 2) by ring]
      exact (Real.rpow_mul (hY_nonneg Omega) (q : ℝ) (1 / 2)).symm
    rw [h1, h2]
  have hjensen :
      bernoulliExpectation p (fun Omega => (Real.sqrt (Y Omega)) ^ q)
        ≤ Real.rpow (bernoulliExpectation p (fun Omega => (Y Omega) ^ q)) (1 / 2) := by
    have hrw : bernoulliExpectation p (fun Omega => (Real.sqrt (Y Omega)) ^ q)
        = bernoulliExpectation p (fun Omega => Real.rpow ((Y Omega) ^ q) (1 / 2)) := by
      unfold bernoulliExpectation
      apply Finset.sum_congr rfl; intro Omega _
      simp only []
      rw [hsqrtpow Omega]
    rw [hrw]
    exact bExp_sqrt_le_sqrt_bExp hp_nonneg hp_le_one
      (fun Omega => (Y Omega) ^ q) (fun Omega => pow_nonneg (hY_nonneg Omega) q)
  -- energy hypothesis (rewritten with abbreviations)
  have hEnergy' :
      bernoulliExpectation p (fun Omega => (Y Omega) ^ q)
        ≤ (Cenergy * p * N * entrySupNorm X ^ 2) ^ q := hEnergy
  have hbExpY_nonneg : 0 ≤ bernoulliExpectation p (fun Omega => (Y Omega) ^ q) := by
    unfold bernoulliExpectation
    apply Finset.sum_nonneg; intro Omega _
    exact mul_nonneg (bernoulliObservationWeight_nonneg hp_nonneg hp_le_one Omega)
      (pow_nonneg (hY_nonneg Omega) q)
  have henergyRHS_nonneg : 0 ≤ (Cenergy * p * N * entrySupNorm X ^ 2) ^ q := by
    apply pow_nonneg; positivity
  -- chain: bExp[(√Y)^q] ≤ ((Cenergy·p·N·E²)^q)^{1/2}
  have hsqrt_energy :
      bernoulliExpectation p (fun Omega => (Real.sqrt (Y Omega)) ^ q)
        ≤ Real.rpow ((Cenergy * p * N * entrySupNorm X ^ 2) ^ q) (1 / 2) := by
    refine le_trans hjensen ?_
    exact Real.rpow_le_rpow hbExpY_nonneg hEnergy' (by norm_num)
  -- LHS ≤ c^q · ((Cenergy·p·N·E²)^q)^{1/2}
  have hLHS :
      bernoulliExpectation p
          (fun Omega => (Ckh * Real.sqrt (q : ℝ) * p⁻¹ * Real.sqrt (Y Omega)) ^ q)
        ≤ c ^ q * Real.rpow ((Cenergy * p * N * entrySupNorm X ^ 2) ^ q) (1 / 2) := by
    rw [show (fun Omega => (Ckh * Real.sqrt (q : ℝ) * p⁻¹ * Real.sqrt (Y Omega)) ^ q)
          = (fun Omega => (c * Real.sqrt (Y Omega)) ^ q) from rfl, hpull]
    exact mul_le_mul_of_nonneg_left hsqrt_energy (pow_nonneg hc_nonneg q)
  -- now the scalar identity: c^q · ((Cenergy·p·N·E²)^q)^{1/2} = (Crad·√(qN/p)·E)^q
  -- rewrite ((A)^q)^{1/2} = (A^{1/2})^q
  have hA_nonneg : 0 ≤ Cenergy * p * N * entrySupNorm X ^ 2 := by positivity
  have hswap :
      Real.rpow ((Cenergy * p * N * entrySupNorm X ^ 2) ^ q) (1 / 2)
        = (Real.rpow (Cenergy * p * N * entrySupNorm X ^ 2) (1 / 2)) ^ q := by
    set A := Cenergy * p * N * entrySupNorm X ^ 2 with hAeq
    have hL : Real.rpow (A ^ q) (1 / 2) = Real.rpow A ((q : ℝ) / 2) := by
      have he : (A ^ q : ℝ) = Real.rpow A (q : ℝ) := (Real.rpow_natCast A q).symm
      rw [he, show ((q : ℝ) / 2) = (q : ℝ) * (1 / 2) by ring]
      exact (Real.rpow_mul hA_nonneg (q : ℝ) (1 / 2)).symm
    have hR : (Real.rpow A (1 / 2)) ^ q = Real.rpow A ((q : ℝ) / 2) := by
      rw [← Real.rpow_natCast (Real.rpow A (1 / 2)) q,
        show ((q : ℝ) / 2) = (1 / 2) * (q : ℝ) by ring]
      exact (Real.rpow_mul hA_nonneg (1 / 2) (q : ℝ)).symm
    rw [hL, hR]
  -- base of A^{1/2} = √(Cenergy·p·N)·E  (since E ≥ 0, √(E²)=E)
  have hAhalf :
      Real.rpow (Cenergy * p * N * entrySupNorm X ^ 2) (1 / 2)
        = Real.sqrt Cenergy * Real.sqrt p * Real.sqrt N * entrySupNorm X := by
    rw [show Real.rpow (Cenergy * p * N * entrySupNorm X ^ 2) (1 / 2)
          = Real.sqrt (Cenergy * p * N * entrySupNorm X ^ 2) from
        (Real.sqrt_eq_rpow _).symm]
    rw [show Cenergy * p * N * entrySupNorm X ^ 2
          = (Cenergy * p * N) * entrySupNorm X ^ 2 by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hentry_nonneg]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (le_of_lt hCenergy)]
  -- now combine c^q · (base)^q = (c · base)^q and simplify the base
  have hfinal_base :
      c * (Real.sqrt Cenergy * Real.sqrt p * Real.sqrt N * entrySupNorm X)
        = (Ckh * Real.sqrt Cenergy) * Real.sqrt ((q : ℝ) * N / p) * entrySupNorm X := by
    rw [hc]
    have hqN : Real.sqrt ((q : ℝ) * N / p)
        = Real.sqrt (q : ℝ) * Real.sqrt N * Real.sqrt p⁻¹ := by
      rw [div_eq_mul_inv, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [hqN]
    have hsqrtp : Real.sqrt p * p⁻¹ = Real.sqrt p⁻¹ :=
      sqrt_mul_inv_eq_sqrt_inv hp_nonneg
    -- LHS = Ckh·√q·p⁻¹·√Ce·√p·√N·E ;  RHS = Ckh·√Ce·√q·√N·√(p⁻¹)·E
    -- use √p·p⁻¹ = √(p⁻¹)
    rw [show Ckh * Real.sqrt (q : ℝ) * p⁻¹ *
              (Real.sqrt Cenergy * Real.sqrt p * Real.sqrt N * entrySupNorm X)
            = (Ckh * Real.sqrt Cenergy) *
                (Real.sqrt (q : ℝ) * Real.sqrt N * (Real.sqrt p * p⁻¹)) * entrySupNorm X by ring]
    rw [hsqrtp]
  calc
    bernoulliExpectation p
        (fun Omega => (Ckh * Real.sqrt (q : ℝ) * p⁻¹ * Real.sqrt (Y Omega)) ^ q)
        ≤ c ^ q * Real.rpow ((Cenergy * p * N * entrySupNorm X ^ 2) ^ q) (1 / 2) := hLHS
    _ = c ^ q * (Real.sqrt Cenergy * Real.sqrt p * Real.sqrt N * entrySupNorm X) ^ q := by
          rw [hswap, hAhalf]
    _ = (c * (Real.sqrt Cenergy * Real.sqrt p * Real.sqrt N * entrySupNorm X)) ^ q := by
          rw [← mul_pow]
    _ = ((Ckh * Real.sqrt Cenergy) * Real.sqrt ((q : ℝ) * N / p) * entrySupNorm X) ^ q := by
          rw [hfinal_base]
#print axioms solution
