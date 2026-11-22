-- Prove2me | solution 1 for Erdos390.Full.PrimePowerTaylorLedger.sum_positiveExponents_pair_inv_lcm_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:32:30.425408+00:00
-- url     : https://prove2.me/submissions/b2103e61-0e5b-4099-a904-f2e7f9654044

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_005
import Theorems.Thm_Erdos390_Full_PrimePowerLcmGeometry_sum_highExponents_pair_inv_lcm_eq_diagonalWeight

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





private theorem summable_quadraticHalfTerm : Summable quadraticHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hsq : Summable
      (fun i : ℕ ↦ (i : ℝ) ^ 2 * (1 / (2 : ℝ)) ^ i) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hx
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable (fun i : ℕ ↦ (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two
  convert ((hsq.mul_left 2).add (hlin.mul_left 7)).add
    (hconst.mul_left 3) using 1
  funext i
  unfold quadraticHalfTerm
  push_cast
  ring



theorem quadraticHalfMass_nonneg : 0 ≤ quadraticHalfMass := by
  unfold quadraticHalfMass
  exact tsum_nonneg fun i ↦ by
    unfold quadraticHalfTerm
    positivity

theorem sum_shifted_quadratic_half_le_mass (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
          (1 / (2 : ℝ)) ^ (r - 2)) ≤ quadraticHalfMass := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, quadraticHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hweight : 2 * r - 3 = 2 * (r - 2) + 1 := by omega
      have hshift : r + 1 = (r - 2) + 3 := by omega
      unfold quadraticHalfTerm g
      rw [hweight]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [show (r : ℝ) + 1 = ((r - 2 : ℕ) : ℝ) + 3 by
        exact_mod_cast hshift]
    · exact hinj
  rw [heq, quadraticHalfMass]
  exact summable_quadraticHalfTerm.sum_le_tsum (s.image g)
    (fun i hi ↦ by unfold quadraticHalfTerm; positivity)

/-- The exact diagonal weight `(2r-3)` still aggregates on the
`p^{-2}` scale. -/
theorem sum_diagonalWeight_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpPow : (2 : ℝ) ^ (r - 2) ≤ (p : ℝ) ^ (r - 2) := by
        gcongr
      have hrSplit : r = 2 + (r - 2) := by omega
      have hpowSplit : (p : ℝ) ^ r =
          (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
        conv_lhs => rw [hrSplit]
        rw [pow_add]
      rw [hpowSplit]
      have hweight0 : (0 : ℝ) ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
      have hnum0 : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2))) ≤
            ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
              (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * quadraticHalfMass :=
      mul_le_mul_of_nonneg_left (sum_shifted_quadratic_half_le_mass R)
        (by positivity)
    _ = quadraticHalfMass / (p : ℝ) ^ 2 := by ring















end

end Erdos390.Full.LocalFugacityBounds

end

/- Source module: Erdos390.Full.PrimePowerLcmGeometry -/
section


/-!
# Diagonal prime-power lcm geometry

For the physical-tilt transfer, the diagonal `JJ` orientation contains the
joint divisibility scale `lcm(p^k,p^l)`.  The number of ordered exponent
pairs whose maximum is `r` is exactly `2r-3`.  The identities below keep
that shell multiplicity literal and then invoke the already proved
arithmetic--geometric diagonal mass.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerLcmGeometry

open ArithmeticModel LocalFugacityBounds

noncomputable section

theorem lcm_pow_pow_eq_pow_max (p k l : ℕ) :
    Nat.lcm (p ^ k) (p ^ l) = p ^ max k l := by
  rcases le_total k l with hkl | hlk
  · rw [max_eq_right hkl, Nat.lcm_eq_right_iff_dvd]
    exact pow_dvd_pow p hkl
  · rw [max_eq_left hlk, Nat.lcm_eq_left_iff_dvd]
    exact pow_dvd_pow p hlk



/-- The diagonal reciprocal-lcm ledger has a fixed `p^{-2}` bound. -/
theorem sum_highExponents_pair_inv_lcm_le
    {p A : ℕ} (hp : p.Prime) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  rw [sum_highExponents_pair_inv_lcm_eq_diagonalWeight]
  calc
    (∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
      ∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hden : 0 ≤ (p : ℝ) ^ r := by positivity
        have hw : 0 ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
        have hr0 : 0 ≤ (r : ℝ) := by positivity
        calc
          ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r =
              ((2 * r - 3 : ℕ) : ℝ) *
                (1 / (p : ℝ) ^ r) := by ring
          _ ≤ ((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
            apply mul_le_mul_of_nonneg_left _ hw
            exact div_le_div_of_nonneg_right (by linarith) hden
    _ ≤ quadraticHalfMass / (p : ℝ) ^ 2 :=
      sum_diagonalWeight_raddone_inv_pow_le hp.two_le



end

end Erdos390.Full.PrimePowerLcmGeometry

end

/- Source module: Erdos390.Full.PaperMediumNuisanceInputReduction -/
section


/-!
# Exact reductions for the two medium-law nuisance inputs

The nuisance Schur row in paper Lemma 8.6 uses two arithmetic facts about
the literal medium-prime component laws:

* a Stieltjes bound for `Cov(v_p, log (m / n))` inside one cell; and
* agreement, to reciprocal-logarithmic precision, of `E v_p` in two cells.

This file proves all finite probability, Abel summation, prime-power
summation, and physical-log identifications surrounding those two facts.
It intentionally does **not** replace the remaining arithmetic estimates by
a bundled certificate.  The hypotheses in the two terminal reductions are
the literal moving-prefix estimate and the literal prime-power/tail
estimates which still have to be obtained from the marked-cell theorem.
-/

open scoped BigOperators Interval

namespace Erdos390.Full

noncomputable section

open ArithmeticModel FiniteProbability ValuationScoreDomination
open DivisibilityMomentBounds

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

























































end FiniteProbability

namespace PrimePowerTaylorLedger

open LocalFugacityBounds PrimePowerLcmGeometry



theorem positivePrimePowerLcmConstant_pos :
    0 < positivePrimePowerLcmConstant := by
  unfold positivePrimePowerLcmConstant
  have hq : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  positivity

/-- The entire same-prime prime-power second-moment ledger costs only a
fixed multiple of `1/p`, uniformly in the moving exponent cutoff. -/
theorem sum_positiveExponents_pair_inv_lcm_le
    {p M : ℕ} (hp : p.Prime) :
    (∑ k ∈ positiveExponents M, ∑ l ∈ positiveExponents M,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) ≤
      positivePrimePowerLcmConstant / (p : ℝ) := by
  by_cases hM0 : M = 0
  · subst M
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    simp [positiveExponents,
      div_nonneg positivePrimePowerLcmConstant_pos.le hpR.le]
  have hM1 : 1 ≤ M := by omega
  have hsplit : positiveExponents M = insert 1 (highExponents M) := by
    ext k
    simp only [mem_positiveExponents, Finset.mem_insert, mem_highExponents]
    omega
  have h1not : 1 ∉ highExponents M := by simp
  let H : ℝ := ∑ k ∈ highExponents M, 1 / ((p ^ k : ℕ) : ℝ)
  let Q : ℝ := ∑ k ∈ highExponents M, ∑ l ∈ highExponents M,
    1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)
  have hfirst :
      (∑ l ∈ highExponents M,
          1 / (Nat.lcm (p ^ 1) (p ^ l) : ℝ)) = H := by
    dsimp only [H]
    apply Finset.sum_congr rfl
    intro l hl
    have hl1 : 1 ≤ l := by
      have := (mem_highExponents.mp hl).1
      omega
    rw [lcm_pow_pow_eq_pow_max, max_eq_right hl1]
  have hsecond :
      (∑ k ∈ highExponents M,
          1 / (Nat.lcm (p ^ k) (p ^ 1) : ℝ)) = H := by
    dsimp only [H]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (mem_highExponents.mp hk).1
      omega
    rw [lcm_pow_pow_eq_pow_max, max_eq_left hk1]
  have hinner :
      (∑ k ∈ highExponents M,
          ∑ l ∈ insert 1 (highExponents M),
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
        (∑ k ∈ highExponents M,
            1 / (Nat.lcm (p ^ k) (p ^ 1) : ℝ)) +
          ∑ k ∈ highExponents M,
            ∑ l ∈ highExponents M,
              1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ) := by
    calc
      (∑ k ∈ highExponents M,
          ∑ l ∈ insert 1 (highExponents M),
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
        ∑ k ∈ highExponents M,
          (1 / (Nat.lcm (p ^ k) (p ^ 1) : ℝ) +
            ∑ l ∈ highExponents M,
              1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_insert h1not]
      _ = _ := Finset.sum_add_distrib
  have hinnerHQ :
      (∑ k ∈ highExponents M,
          ∑ l ∈ insert 1 (highExponents M),
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) = H + Q := by
    rw [hinner, hsecond]
  have hdecomp :
      (∑ k ∈ positiveExponents M, ∑ l ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
        1 / (p : ℝ) + 2 * H + Q := by
    rw [hsplit, Finset.sum_insert h1not]
    rw [show (∑ l ∈ insert 1 (highExponents M),
        1 / (Nat.lcm (p ^ 1) (p ^ l) : ℝ)) =
          1 / (p : ℝ) + H by
      rw [Finset.sum_insert h1not, hfirst]
      norm_num]
    rw [hinnerHQ]
    ring
  have hH : H ≤ 2 / (p : ℝ) ^ 2 := by
    dsimp only [H]
    simpa only [highExponents] using
      (sum_inv_pow_tail_le (p := p) (r := 1) (A := M) hp.two_le)
  have hQ : Q ≤ quadraticHalfMass / (p : ℝ) ^ 2 := by
    dsimp only [Q]
    exact sum_highExponents_pair_inv_lcm_le hp
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  rw [hdecomp]
  calc
    1 / (p : ℝ) + 2 * H + Q ≤
        1 / (p : ℝ) + 2 * (2 / (p : ℝ) ^ 2) +
          quadraticHalfMass / (p : ℝ) ^ 2 := by
      gcongr
    _ = 1 / (p : ℝ) +
        (4 + quadraticHalfMass) / (p : ℝ) ^ 2 := by ring
    _ ≤ 1 / (p : ℝ) +
        ((4 + quadraticHalfMass) / 2) / (p : ℝ) := by
      have hq0 : 0 ≤ 4 + quadraticHalfMass := by
        exact add_nonneg (by norm_num) quadraticHalfMass_nonneg
      have hden : (2 : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ 2 := by
        nlinarith
      have htail :
        (4 + quadraticHalfMass) / (p : ℝ) ^ 2 ≤
            ((4 + quadraticHalfMass) / 2) / (p : ℝ) := by
        calc
          (4 + quadraticHalfMass) / (p : ℝ) ^ 2 ≤
              (4 + quadraticHalfMass) / (2 * (p : ℝ)) :=
            div_le_div_of_nonneg_left hq0 (by positivity) hden
          _ = ((4 + quadraticHalfMass) / 2) / (p : ℝ) := by ring
      exact add_le_add le_rfl htail
    _ = positivePrimePowerLcmConstant / (p : ℝ) := by
      unfold positivePrimePowerLcmConstant
      field_simp [hpPos.ne']









end PrimePowerTaylorLedger

namespace FiniteProbability

open PrimePowerTaylorLedger

variable {Omega : Type*} [Fintype Omega]



















end FiniteProbability

namespace FiniteLogStieltjes

open Finset Set

variable {Omega : Type*} [Fintype Omega]





end FiniteLogStieltjes

namespace GuardedUniformCell

open FiniteLogStieltjes

variable {Alpha : Type*} [DecidableEq Alpha]





end GuardedUniformCell

namespace PrimePowerTail

open Finset

variable {Omega : Type*} [Fintype Omega]



end PrimePowerTail

namespace PaperBridgeFit

open ArithmeticBandGeometry FiniteLogStieltjes

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













end BridgeData

end PaperBridgeFit

end

end Erdos390.Full

end

theorem solution :
∀ {p M : Nat},
  Nat.Prime p →
    LE.le.{0}
      (∑ k ∈ Erdos390.Full.ArithmeticModel.positiveExponents M,
        ∑ l ∈ Erdos390.Full.ArithmeticModel.positiveExponents M,
          HDiv.hDiv.{0, 0, 0} (1 : Real) ↑(Nat.lcm (HPow.hPow.{0, 0, 0} p k) (HPow.hPow.{0, 0, 0} p l)))
      (HDiv.hDiv.{0, 0, 0} Erdos390.Full.PrimePowerTaylorLedger.positivePrimePowerLcmConstant ↑p) := by
  exact @Erdos390.Full.PrimePowerTaylorLedger.sum_positiveExponents_pair_inv_lcm_le
