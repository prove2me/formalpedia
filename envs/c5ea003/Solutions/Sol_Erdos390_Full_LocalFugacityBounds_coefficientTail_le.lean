-- Prove2me | solution 1 for Erdos390.Full.LocalFugacityBounds.coefficientTail_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T14:45:09.283182+00:00
-- url     : https://prove2.me/submissions/974a2457-ee7c-4b03-ae57-f7a8bbd84ce5

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

/- Source module: Erdos390.Full.LocalFugacity -/
section


/-!
# Exact restoration of one local fugacity

This proves the finite telescoping identity used when an omitted prime is
restored in the tilted measure.  The coefficients are the actual
`λ^a-λ^(a-1)` coefficients and the indicators are actual divisibility
indicators.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacity

open ArithmeticModel





theorem coefficient_pos (lam : ℝ) {a : ℕ} (ha : 0 < a) :
    coefficient lam a = lam ^ a - lam ^ (a - 1) := by
  simp [coefficient, ha.ne']

/-- A literal coefficient bound for a compact logarithmic fugacity.  It is
stated first in terms of `x`; substituting `x=η/L` gives the paper's
`O(L⁻¹ exp(Ba/L))` estimate. -/
theorem abs_coefficient_exp_le {x : ℝ} {a : ℕ} (ha : 0 < a)
    (hx : |x| ≤ 1) :
    |coefficient (Real.exp x) a| ≤
      2 * |x| * Real.exp (|x| * (a : ℝ)) := by
  rw [coefficient_pos (Real.exp x) ha]
  have ha1 : 1 ≤ a := ha
  have hsplit : (a : ℝ) = ((a - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel ha1).symm
  have hcoeff :
      Real.exp x ^ a - Real.exp x ^ (a - 1) =
        Real.exp (((a - 1 : ℕ) : ℝ) * x) * (Real.exp x - 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    rw [hsplit, add_mul, one_mul, Real.exp_add]
    ring
  rw [hcoeff, abs_mul, Real.abs_exp]
  calc
    Real.exp (((a - 1 : ℕ) : ℝ) * x) * |Real.exp x - 1| ≤
        Real.exp (((a - 1 : ℕ) : ℝ) * x) * (2 * |x|) :=
      mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le hx)
        (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (|x| * (a : ℝ)) * (2 * |x|) := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.exp_le_exp.mpr
        have hxle : x ≤ |x| := le_abs_self x
        have hcast : (((a - 1 : ℕ) : ℝ)) ≤ (a : ℝ) := by
          exact_mod_cast Nat.sub_le a 1
        have hnonneg : 0 ≤ (((a - 1 : ℕ) : ℝ)) := by positivity
        have habs : 0 ≤ |x| := abs_nonneg x
        nlinarith
      · positivity
    _ = 2 * |x| * Real.exp (|x| * (a : ℝ)) := by ring

theorem abs_coefficient_exp_div_le {B η L : ℝ} {a : ℕ}
    (ha : 0 < a) (hL : 0 < L) (hBL : B ≤ L)
    (hη : |η| ≤ B) :
    |coefficient (Real.exp (η / L)) a| ≤
      (2 * B / L) * Real.exp (B * (a : ℝ) / L) := by
  have hx : |η / L| ≤ 1 := by
    rw [abs_div, abs_of_pos hL]
    apply (div_le_one hL).mpr
    exact hη.trans hBL
  refine (abs_coefficient_exp_le ha hx).trans ?_
  have hdiv : |η / L| ≤ B / L := by
    rw [abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hη hL.le
  have hexp :
      Real.exp (|η / L| * (a : ℝ)) ≤
        Real.exp (B * (a : ℝ) / L) := by
    apply Real.exp_le_exp.mpr
    have ha0 : 0 ≤ (a : ℝ) := by positivity
    calc
      |η / L| * (a : ℝ) ≤ (B / L) * (a : ℝ) :=
        mul_le_mul_of_nonneg_right hdiv ha0
      _ = B * (a : ℝ) / L := by ring
  have hleft : 0 ≤ 2 * |η / L| := by positivity
  have hright : 0 ≤ Real.exp (B * (a : ℝ) / L) :=
    (Real.exp_pos _).le
  calc
    2 * |η / L| * Real.exp (|η / L| * (a : ℝ)) ≤
        2 * |η / L| * Real.exp (B * (a : ℝ) / L) :=
      mul_le_mul_of_nonneg_left hexp hleft
    _ ≤ (2 * B / L) * Real.exp (B * (a : ℝ) / L) := by
      apply mul_le_mul_of_nonneg_right _ hright
      calc
        2 * |η / L| ≤ 2 * (B / L) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = 2 * B / L := by ring







end Erdos390.Full.LocalFugacity

end

/- Source module: Erdos390.Full.LocalFugacityBounds -/
section


/-!
# Uniform bounds for restored local fugacity coefficients

The local restoration in Lemma 7.5 must retain both the factor `1 / L`
and the geometric factor `p^{-r}`.  Cardinality bounds on the exponent set
are too crude for that purpose.  This module proves the required shifted
geometric estimates directly for the actual coefficients
`exp (eta/L)^a - exp (eta/L)^(a-1)`.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityBounds

open LocalFugacity

noncomputable section

private theorem sub_injective_on_Icc (k A : ℕ) :
    Set.InjOn (fun a : ℕ ↦ a - k) (↑(Finset.Icc k A) : Set ℕ) := by
  intro a ha b hb hab
  have hka : k ≤ a := (Finset.mem_Icc.mp ha).1
  have hkb : k ≤ b := (Finset.mem_Icc.mp hb).1
  change a - k = b - k at hab
  calc
    a = (a - k) + k := (Nat.sub_add_cancel hka).symm
    _ = (b - k) + k := congrArg (fun z : ℕ ↦ z + k) hab
    _ = b := Nat.sub_add_cancel hkb

/-- Every finite shifted half-geometric tail is bounded by the complete
geometric series. -/
theorem sum_shifted_half_le_two (k A : ℕ) :
    (∑ a ∈ Finset.Icc k A,
        (1 / (2 : ℝ)) ^ (a - k)) ≤ 2 := by
  let s := Finset.Icc k A
  let g : ℕ → ℕ := fun a ↦ a - k
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc k A
  have heq :
      (∑ a ∈ s, (1 / (2 : ℝ)) ^ (a - k)) =
        ∑ i ∈ s.image g, (1 / (2 : ℝ)) ^ i := by
    symm
    rw [Finset.sum_image]
    exact hinj
  rw [heq]
  exact (summable_geometric_two.sum_le_tsum (s.image g)
    (fun i hi ↦ by positivity)).trans_eq tsum_geometric_two









/-- A finite reciprocal-power tail beginning at exponent `r+1` has the
same bound as the corresponding infinite geometric tail. -/
theorem sum_inv_pow_tail_le {p r A : ℕ} (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      2 / (p : ℝ) ^ (r + 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < (p : ℝ) := by positivity
  calc
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      ∑ a ∈ Finset.Icc (r + 1) A,
        (1 / (p : ℝ) ^ (r + 1)) *
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hra : r + 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hpPow : (2 : ℝ) ^ (a - (r + 1)) ≤
          (p : ℝ) ^ (a - (r + 1)) := by gcongr
      have haSplit : a = (r + 1) + (a - (r + 1)) := by omega
      have hpowSplit : (p : ℝ) ^ a =
          (p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1)) := by
        conv_lhs => rw [haSplit]
        rw [pow_add]
      norm_num only [Nat.cast_pow]
      rw [hpowSplit]
      calc
        1 / ((p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1))) ≤
            1 / ((p : ℝ) ^ (r + 1) *
              (2 : ℝ) ^ (a - (r + 1))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ (r + 1)) *
            (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ (r + 1)) *
        ∑ a ∈ Finset.Icc (r + 1) A,
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ (r + 1)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_shifted_half_le_two (r + 1) A)
        (by positivity)
    _ = 2 / (p : ℝ) ^ (r + 1) := by ring



















/-- Pointwise coefficient majorant at the common exponent cutoff. -/
theorem abs_coefficient_exp_div_le_at_cutoff
    {B eta L : ℝ} {a A : ℕ}
    (ha : 0 < a) (haA : a ≤ A) (hB : 0 ≤ B)
    (hL : 0 < L) (hBL : B ≤ L) (heta : |eta| ≤ B) :
    |coefficient (Real.exp (eta / L)) a| ≤
      (2 * B / L) * Real.exp (B * (A : ℝ) / L) := by
  have hraw := abs_coefficient_exp_div_le
    (B := B) (η := eta) (L := L) ha hL hBL heta
  have hcoef : 0 ≤ 2 * B / L := by positivity
  have hexp : Real.exp (B * (a : ℝ) / L) ≤
      Real.exp (B * (A : ℝ) / L) := by
    apply Real.exp_le_exp.mpr
    have haAR : (a : ℝ) ≤ (A : ℝ) := by exact_mod_cast haA
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left haAR hB) hL.le
  exact hraw.trans (mul_le_mul_of_nonneg_left hexp hcoef)

/-- Exact scale of the one-prime restoration tail.  Unlike a cardinality
bound, this retains `1/L` uniformly in the exponent cutoff. -/
theorem coefficientTail_le
    {p A r : ℕ} {B eta L : ℝ}
    (hp : 2 ≤ p) (hB : 0 ≤ B) (hL : 0 < L)
    (hBL : B ≤ L) (heta : |eta| ≤ B) :
    coefficientTail p A r eta L ≤
      ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) *
        (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
  classical
  let s := Finset.Icc 1 A
  let K : ℝ := (2 * B / L) * Real.exp (B * (A : ℝ) / L)
  let low := s.filter (fun a ↦ a ≤ r)
  let high := s.filter (fun a ↦ ¬a ≤ r)
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hcoeff : ∀ a ∈ s,
      |coefficient (Real.exp (eta / L)) a| ≤ K := by
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    simpa only [K] using abs_coefficient_exp_div_le_at_cutoff
      ha'.1 ha'.2 hB hL hBL heta
  have hsplit :
      (∑ a ∈ s,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) =
        (∑ a ∈ low,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) +
        (∑ a ∈ high,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) := by
    dsimp only [low, high]
    exact (Finset.sum_filter_add_sum_filter_not s (fun a ↦ a ≤ r)
      (fun a ↦ |coefficient (Real.exp (eta / L)) a| /
        ((p ^ max r a : ℕ) : ℝ))).symm
  have hlowSubset : low ⊆ Finset.Icc 1 r := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha'.1).1, ha'.2⟩
  have hlowCard : low.card ≤ r := by
    calc
      low.card ≤ (Finset.Icc 1 r).card := Finset.card_le_card hlowSubset
      _ = r := by simp
  have hlow :
      (∑ a ∈ low,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) ≤
        (r : ℝ) * (K / (p : ℝ) ^ r) := by
    calc
      _ ≤ ∑ a ∈ low, K / (p : ℝ) ^ r := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' := Finset.mem_filter.mp ha
        have har : a ≤ r := ha'.2
        norm_num only [Nat.cast_pow]
        rw [max_eq_left har]
        exact div_le_div_of_nonneg_right (hcoeff a ha'.1) (by positivity)
      _ = (low.card : ℝ) * (K / (p : ℝ) ^ r) := by simp
      _ ≤ (r : ℝ) * (K / (p : ℝ) ^ r) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlowCard)
          (div_nonneg hK (by positivity))
  have hhighSet : high = Finset.Icc (r + 1) A := by
    ext a
    simp only [high, s, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hhigh :
      (∑ a ∈ high,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) ≤
        K * (2 / (p : ℝ) ^ (r + 1)) := by
    rw [hhighSet]
    calc
      _ ≤ ∑ a ∈ Finset.Icc (r + 1) A,
          K * (1 / (p : ℝ) ^ a) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' := Finset.mem_Icc.mp ha
        have hra : r ≤ a := by omega
        norm_num only [Nat.cast_pow]
        rw [max_eq_right hra]
        calc
          |coefficient (Real.exp (eta / L)) a| / (p : ℝ) ^ a ≤
              K / (p : ℝ) ^ a :=
            div_le_div_of_nonneg_right
              (hcoeff a (by simp only [s, Finset.mem_Icc]; omega))
              (by positivity)
          _ = K * (1 / (p : ℝ) ^ a) := by ring
      _ = K * (∑ a ∈ Finset.Icc (r + 1) A,
          1 / (p : ℝ) ^ a) := by
        rw [Finset.mul_sum]
      _ ≤ K * (2 / (p : ℝ) ^ (r + 1)) := by
        have htail := sum_inv_pow_tail_le (A := A) (r := r) hp
        norm_num only [Nat.cast_pow] at htail
        exact mul_le_mul_of_nonneg_left htail hK
  have htailScale :
      2 / (p : ℝ) ^ (r + 1) ≤ 1 / (p : ℝ) ^ r := by
    rw [pow_succ]
    have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hpow : (0 : ℝ) < (p : ℝ) ^ r := by positivity
    apply (div_le_iff₀ (mul_pos hpow hpR)).2
    field_simp [hpow.ne', hpR.ne']
    nlinarith
  unfold coefficientTail
  change (∑ a ∈ s,
      |coefficient (Real.exp (eta / L)) a| /
        ((p ^ max r a : ℕ) : ℝ)) ≤ _
  rw [hsplit]
  calc
    _ ≤ (r : ℝ) * (K / (p : ℝ) ^ r) +
        K * (2 / (p : ℝ) ^ (r + 1)) := add_le_add hlow hhigh
    _ ≤ (r : ℝ) * (K / (p : ℝ) ^ r) +
        K * (1 / (p : ℝ) ^ r) := by gcongr
    _ = K * (((r : ℝ) + 1) / (p : ℝ) ^ r) := by ring
    _ = ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) *
        (((r : ℝ) + 1) / (p : ℝ) ^ r) := by rfl







end

end Erdos390.Full.LocalFugacityBounds

end

theorem solution :
∀ {p A r : Nat} {B eta L : Real},
  LE.le.{0} (2 : Nat) p →
    LE.le.{0} (0 : Real) B →
      LT.lt.{0} (0 : Real) L →
        LE.le.{0} B L →
          LE.le.{0} (abs.{0} eta) B →
            LE.le.{0} (Erdos390.Full.LocalFugacityBounds.coefficientTail p A r eta L)
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) B) L)
                  (Real.exp (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} B ↑A) L)))
                (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑r (1 : Real)) (HPow.hPow.{0, 0, 0} (↑p) r))) := by
  exact @Erdos390.Full.LocalFugacityBounds.coefficientTail_le
