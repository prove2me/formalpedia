-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceWithFixedNumericalData_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.621007+00:00
-- url     : https://prove2.me/submissions/564e30e6-82d0-4665-82df-89ebdcc03b67

import Definitions.Def_erdos390_remaining_analytic_propositions_006
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_Full_PaperScaleMarkedCell_exists_uniform_markedCell_paper_main_bound
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget_compact
import Theorems.Thm_Erdos390_WholePaper_bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
import Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact
import Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds



section
theorem Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower : Erdos390.RemainingAnalyticGoal008_004 := @Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact
end
section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget : Erdos390.RemainingAnalyticGoal004_014.{u_1} := @Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget_compact
end
/- Source module: Erdos390.Full.RegularRelativeMesh -/
section


/-!
# Existence of a finite regular relative mesh

Section 8.4 partitions the positive logarithmic interval `[delta,1]` into
geometric cells.  This file constructs such a mesh rather than leaving its
existence as a certificate.  Given `0 < delta < 1` and a requested upper
relative width `eta > 0`, the number of cells is the ceiling of the relevant
logarithmic ratio and the common relative width is adjusted so that the last
endpoint is exactly `1`.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)













theorem endpoint_succ (k : ℕ) :
    M.endpoint (k + 1) = M.endpoint k * (1 + M.ratio) := by
  unfold endpoint
  rw [pow_succ]
  ring



theorem endpoint_pos (hdelta : 0 < delta) (k : ℕ) :
    0 < M.endpoint k := by
  unfold endpoint
  exact mul_pos hdelta (pow_pos (by linarith [M.ratio_pos]) k)

theorem lower_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.lower k := M.endpoint_pos hdelta k.1

theorem width_eq_ratio_mul_lower (k : Fin M.cellCount) :
    M.width k = M.ratio * M.lower k := by
  unfold width upper lower
  rw [M.endpoint_succ]
  ring

theorem width_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.width k := by
  rw [M.width_eq_ratio_mul_lower]
  exact mul_pos M.ratio_pos (M.lower_pos hdelta k)











end Mesh



end

end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)









theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.Scale -/
section


/-!
# Exact scale identities

This file records the elementary identities behind the fixed choice
`y = n^(2/9)` used throughout the marked and smooth bridge.  Keeping them as
equalities avoids repeatedly treating `U = 9/2` and the four-mark cofactor
margin as informal arithmetic simplifications.
-/

open Filter Topology

namespace Erdos390.Full.Scale

open ArithmeticModel

























theorem endpointRatio_eq {n : ℕ} (hn : 0 < n) :
    endpointRatio n = L n ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      (n : ℝ) ^ (4 / 9 : ℝ) * (n : ℝ) ^ (5 / 9 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  rw [endpointRatio, y_pow_two]
  field_simp [(Real.rpow_pos_of_pos hnR (5 / 9 : ℝ)).ne', hnR.ne']
  nlinarith

/-- In particular, all `y^2 L^2 / n` endpoint errors vanish. -/
theorem tendsto_endpointRatio_zero :
    Tendsto endpointRatio atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (5 / 9 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 5 / 9)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ))
      atTop (𝓝 0) := by
    simpa [Real.rpow_natCast] using hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [L] using (endpointRatio_eq hn).symm

end Erdos390.Full.Scale

end

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/



















































/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/






















































/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower






end Erdos390.Full.FriableAsymptotic

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/











theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)



/-! ## The common paper-scale main term -/





theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos

































/-! ## Normalization algebra -/







/-- The unmarked structured cell has a fixed positive linear density.  This
is the normalization lower bound used by all subsequent compact tilts. -/
theorem exists_structuredCell_density_lower_bound
    (P : Pattern) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ N₀ : ℕ, ∀ {n : ℕ}, N₀ ≤ n →
      paperCellDensity P A B * (n : ℝ) / 2 ≤
        ((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) := by
  obtain ⟨K, hK, Ncount, hcount⟩ :=
    exists_uniform_markedCell_paper_main_bound P hA hAB
  let c : ℝ := paperCellDensity P A B
  have hc : 0 < c := paperCellDensity_pos P hAB
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ (2 : ℝ) ≤ y n ∧ 2 * K / c ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
      hLTop.eventually (Filter.eventually_ge_atTop (2 * K / c))] with
      n hn hy hden
    exact ⟨hn, hy, hden⟩
  obtain ⟨Nlarge, hNlarge⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max Ncount Nlarge, ?_⟩
  intro n hN
  have hNc : Ncount ≤ n := by omega
  have hNl : Nlarge ≤ n := by omega
  obtain ⟨hn, hy, hden⟩ := hNlarge n hNl
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hL : 0 < L n := L_pos hn
  have hyNat2 : 2 ≤ yNat n := Nat.le_floor hy
  have h1d4 : 1 ≤ yNat n ^ 4 := by
    exact pow_pos (by omega : 0 < yNat n) 4
  have hbase₀ := hcount (n := n) (d := 1) hNc (by omega) h1d4
    (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hbase :
      |((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) - c * (n : ℝ)| ≤
        K * (n : ℝ) / L n := by
    simpa [c, markedCell] using hbase₀
  have hscale : 2 * K ≤ c * L n := by
    have := (div_le_iff₀ hc).1 hden
    simpa [mul_comm] using this
  have hKdiv : K / L n ≤ c / 2 := by
    apply (div_le_iff₀ hL).2
    nlinarith [hscale]
  have herr : K * (n : ℝ) / L n ≤ c * (n : ℝ) / 2 := by
    calc
      K * (n : ℝ) / L n = (K / L n) * (n : ℝ) := by ring
      _ ≤ (c / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hKdiv hnR.le
      _ = c * (n : ℝ) / 2 := by ring
  have hlower := (abs_le.mp (hbase.trans herr)).1
  dsimp only [c] at hlower ⊢
  linarith



end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.Full.PaperGuardCensus -/
section


/-!
# The concrete numerical-guard census used by the smooth bridge

The rough construction has only two kinds of numerical occurrences which can
meet one of the active smooth cells:

* promoted smooth anchors, in `O(y)` slots;
* endpoints (and the possible donor occurrence) of an `O(y)` family of bank
  paths, with at most one component at each geometric scale.

This file represents those occurrences by a literal finite slot type and
defines the numerical guard set as the image of its value map.  Consequently
the guard-cardinality estimate is a theorem about `Finset.image`; it is not a
field of a contract and it is not assumed about an arbitrary finset.

The number of geometric slots is fixed here to `ceil(log n)+1`.  This is a
harmless enlargement of the paper's geometric-scale list and makes the
`O(y log n)` census completely explicit.  Multiple slots are allowed to map to
the same integer; this only makes the proved image-cardinality bound stronger.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability GuardedUniformCell ValuationTiltCell

noncomputable section













/-- The global bridge-relevant guard census, derived from the image
construction rather than postulated. -/
theorem Ledger.card_guards_le {n Cprom Cbank : ℕ}
    (G : Ledger n Cprom Cbank) :
    G.guards.card ≤
      Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 := by
  calc
    G.guards.card ≤ (Finset.univ : Finset (GuardSlot n Cprom Cbank)).card :=
      Finset.card_image_le
    _ = Fintype.card (GuardSlot n Cprom Cbank) := Finset.card_univ
    _ = _ := card_guardSlot n Cprom Cbank

/-- The concrete ceiling has the advertised logarithmic size. -/
theorem cast_scaleSlots_lt {n : ℕ} (hn : 1 ≤ n) :
    (scaleSlots n : ℝ) < L n + 2 := by
  have hL : 0 ≤ L n := by
    unfold L
    exact Real.log_nonneg (by exact_mod_cast hn)
  unfold scaleSlots
  push_cast
  have hceil := Nat.ceil_lt_add_one hL
  linarith

/-- A weak inequality convenient in multiplicative census estimates. -/
theorem cast_scaleSlots_le {n : ℕ} (hn : 1 ≤ n) :
    (scaleSlots n : ℝ) ≤ L n + 2 :=
  (cast_scaleSlots_lt hn).le

/-- Real-cast form of the image census. -/
theorem Ledger.cast_card_guards_le {n Cprom Cbank : ℕ}
    (G : Ledger n Cprom Cbank) (hn : 1 ≤ n) :
    (G.guards.card : ℝ) ≤
      (Cprom + 3 * Cbank * (L n + 2)) * (yNat n : ℝ) := by
  have hcard : (G.guards.card : ℝ) ≤
      (Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) := by
    exact_mod_cast G.card_guards_le
  have hy0 : (0 : ℝ) ≤ (yNat n : ℝ) := by positivity
  have hscale := cast_scaleSlots_le hn
  calc
    (G.guards.card : ℝ) ≤
        (Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) := hcard
    _ = ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (scaleSlots n : ℝ)) *
          (yNat n : ℝ) := by
      push_cast
      ring
    _ ≤ ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
          (yNat n : ℝ) := by
      gcongr
    _ = (Cprom + 3 * Cbank * (L n + 2)) * (yNat n : ℝ) := by ring



private theorem tendsto_L_pow_zero_div_nat_rpow_zero (a : ℝ)
    (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (0 : ℝ) / x ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (0 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, Real.rpow_zero]

private theorem tendsto_L_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n / (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (1 : ℝ) / x ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, L, Real.rpow_one]

private theorem y_div_nat_eq_inv_rpow {n : ℕ} (hn : 0 < n) :
    y n / (n : ℝ) = 1 / (n : ℝ) ^ (7 / 9 : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      (n : ℝ) ^ (2 / 9 : ℝ) * (n : ℝ) ^ (7 / 9 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num [Real.rpow_one]
  unfold y
  field_simp [(Real.rpow_pos_of_pos hnR (7 / 9 : ℝ)).ne', hnR.ne']
  nlinarith

/-- The concrete `O(y log n)` census is `o(n)`. -/
theorem tendsto_censusRatioMajorant_zero (Cprom Cbank : ℕ) :
    Tendsto (censusRatioMajorant Cprom Cbank) atTop (𝓝 0) := by
  let a : ℝ := (7 / 9 : ℝ)
  have ha : 0 < a := by norm_num [a]
  have hzero := tendsto_L_pow_zero_div_nat_rpow_zero a ha
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hsum : Tendsto
      (fun n : ℕ ↦
        (Cprom : ℝ) * (1 / (n : ℝ) ^ a) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ a + 2 * (1 / (n : ℝ) ^ a)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (hzero.const_mul (Cprom : ℝ)).add
        ((hlog.add (hzero.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [censusRatioMajorant]
  rw [show
    ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n / (n : ℝ) =
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
        (y n / (n : ℝ)) by ring]
  rw [y_div_nat_eq_inv_rpow hn]
  dsimp only [a]
  ring

/-- The literal guard set has vanishing relative cardinality, with no
cardinality premise on the ledger. -/
theorem Ledger.tendsto_card_div_nat_zero {Cprom Cbank : ℕ}
    (G : ∀ n, Ledger n Cprom Cbank) :
    Tendsto (fun n : ℕ ↦ ((G n).guards.card : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hcard := (G n).cast_card_guards_le hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hyfloor : (yNat n : ℝ) ≤ y n :=
      Nat.floor_le (Scale.y_pos (by omega : 0 < n)).le
    calc
      ((G n).guards.card : ℝ) / (n : ℝ) ≤
          ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
            (yNat n : ℝ) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hcard hn0
      _ ≤ ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
            y n / (n : ℝ) := by
        have hcoef : 0 ≤ (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by
          have hL : 0 ≤ L n := by
            exact Real.log_nonneg (by exact_mod_cast hn)
          positivity
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hyfloor hcoef) hn0
      _ = censusRatioMajorant Cprom Cbank n := rfl
  · exact tendsto_censusRatioMajorant_zero Cprom Cbank

end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperBridgeFit -/
section


/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit







namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]





























/-- Every integer in the guarded sample is smooth at the paper's integral
cutoff.  Guard deletion changes neither smoothness nor the head pattern. -/
theorem value_mem_smoothNumbers (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∈ Nat.smoothNumbers (yNat D.n + 1) := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.2

theorem value_not_guard (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∉ D.guards :=
  (Finset.mem_sdiff.mp (D.value_mem_cell m)).2



end StructuredSampleData



namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}



















end BaselineAllocation









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

















































































/-! ### Exact main/nuisance coordinate splitting -/

































































































































/-! ## Exact target and moment correspondence -/















































































/-! ## Actual baseline mixture and coarse cells -/





























































































/-! ## Explicit finite diameter -/





















/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/















/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

end


end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperGuardedStructuredSample -/
section


/-!
# Canonical guarded structured sample

This module attaches the concrete guard ledger to the literal physical
structured cells used by the bridge.  Both physical endpoints are definitionally
`floor(A*n)`, and nonemptiness after guard deletion is derived from the proved
Dickman cell-density theorem and the concrete `O(y log n)` image census.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open PaperScaleMarkedCell
open PaperBridgeFit

noncomputable section



variable {Head : Type*} [Fintype Head]





/-- Every raw cell has its proved positive Dickman density eventually. -/
theorem eventually_rawCell_density
    (P : Head → Pattern) (I : PhysicalIntervals) :
    ∀ᶠ n : ℕ in atTop, ∀ c : Cell Head,
      paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) *
          (n : ℝ) / 2 ≤ (rawCell P I n c).card := by
  rw [Filter.eventually_all]
  intro c
  obtain ⟨N₀, hN₀⟩ := exists_structuredCell_density_lower_bound
    (P c.1) (I.lower_pos c.2) (I.lower_lt_upper c.2)
  filter_upwards [eventually_ge_atTop N₀] with n hn
  simpa only [rawCell] using hN₀ hn

/-- Strict separation of the two floored physical pools follows from the
fixed strict separation of their real endpoints. -/
theorem eventually_physicalBound_separated (I : PhysicalIntervals) :
    ∀ᶠ n : ℕ in atTop,
      physicalBound (I.upper .minus) n <
        physicalBound (I.lower .plus) n := by
  let gap : ℝ := I.lower .plus - I.upper .minus
  have hgap : 0 < gap := sub_pos.mpr I.separated
  have htop : Tendsto (fun n : ℕ ↦ gap * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hgap)
  have hevent := htop.eventually (eventually_gt_atTop (1 : ℝ))
  filter_upwards [hevent, eventually_gt_atTop 0] with n hlarge hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hminus :
      (physicalBound (I.upper .minus) n : ℝ) ≤
        I.upper .minus * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg (le_of_lt
      ((I.lower_pos .minus).trans (I.lower_lt_upper .minus))) hn0)
  have hplus :
      I.lower .plus * (n : ℝ) <
        (physicalBound (I.lower .plus) n : ℝ) + 1 := by
    unfold physicalBound
    exact Nat.lt_floor_add_one _
  have hcast :
      (physicalBound (I.upper .minus) n : ℝ) <
        (physicalBound (I.lower .plus) n : ℝ) := by
    dsimp only [gap] at hlarge
    nlinarith
  exact_mod_cast hcast

/-- After the concrete image census, every physical/head cell remains
nonempty.  No cardinality estimate is supplied as a hypothesis. -/
theorem eventually_guarded_rawCell_nonempty
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    {Cprom Cbank : ℕ} (G : ∀ n, Ledger n Cprom Cbank) :
    ∀ᶠ n : ℕ in atTop, ∀ c : Cell Head,
      (rawCell P I n c \ (G n).guards).Nonempty := by
  have hdensity := eventually_rawCell_density P I
  have hratio := Ledger.tendsto_card_div_nat_zero G
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ c : Cell Head,
      ((G n).guards.card : ℝ) / (n : ℝ) <
        paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) / 2 := by
    rw [Filter.eventually_all]
    intro c
    have hc : 0 <
        paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) / 2 :=
      half_pos (paperCellDensity_pos (P c.1) (I.lower_lt_upper c.2))
    exact hratio.eventually (eventually_lt_nhds hc)
  filter_upwards [hdensity, hsmall, eventually_gt_atTop 0] with
      n hdens hguard hn c
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hguardScaled :
      ((G n).guards.card : ℝ) <
        paperCellDensity (P c.1) (I.lower c.2) (I.upper c.2) *
          (n : ℝ) / 2 := by
    have hmul := (div_lt_iff₀ hnR).mp (hguard c)
    nlinarith
  have hcardR : ((G n).guards.card : ℝ) < (rawCell P I n c).card :=
    hguardScaled.trans_le (hdens c)
  have hcard : (G n).guards.card < (rawCell P I n c).card := by
    exact_mod_cast hcardR
  rw [Finset.sdiff_nonempty]
  intro hsubset
  exact (Nat.not_lt_of_ge (Finset.card_le_card hsubset)) hcard



















end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperHeadSimplex -/
section


/-!
# The literal finite head-pattern simplex used in Section 8

For a fixed finite head-prime set `P` and a positive exponent `E`, the paper
uses the vertices `0` and `E e_p`.  This module constructs those exact
valuation patterns and proves that two different vertices cannot contain the
same positive integer.  The result discharges the cell-disjointness premise
used when tagged structured cells are returned to literal integer
coordinates.
-/

namespace Erdos390.Full.PaperHeadSimplex

noncomputable section













/-- Distinct simplex vertices disagree at a common head prime. -/
theorem patternsSeparated (P : Finset Nat)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E) :
    forall h k : Tag P, h ≠ k -> exists p,
      p ∈ (pattern P hprime E h).primes ∧
      p ∈ (pattern P hprime E k).primes ∧
      (pattern P hprime E h).exponent p ≠
        (pattern P hprime E k).exponent p := by
  intro h k hne
  cases h with
  | none =>
      cases k with
      | none => exact (hne rfl).elim
      | some q =>
          refine ⟨q.1, q.2, q.2, ?_⟩
          simp only [pattern, exponent_none, exponent_some_self]
          exact Nat.ne_of_lt hE
  | some p =>
      cases k with
      | none =>
          refine ⟨p.1, p.2, p.2, ?_⟩
          simp only [pattern, exponent_some_self, exponent_none]
          exact Nat.ne_of_gt hE
      | some q =>
          have hpq : p.1 ≠ q.1 := by
            intro hpq
            have hpqSubtype : p = q := Subtype.ext hpq
            exact hne (congrArg some hpqSubtype)
          refine ⟨p.1, p.2, p.2, ?_⟩
          simp only [pattern, exponent_some_self]
          rw [exponent_some_ne P E q p.1 hpq]
          exact Nat.ne_of_gt hE

end

end Erdos390.Full.PaperHeadSimplex

end

/- Source module: Erdos390.Full.PaperBridgeFitFeasibility -/
section


/-!
# Feasibility and frozen-ledger consequences of the actual bridge tilt

The nonlinear bridge changes only the active structured-cell coordinates.
This file records, for the literal finite exponential family used in
`PaperBridgeFit`, the conclusions which are independent of the analytic
covariance estimates: positivity, preservation of the active mass, an
explicit coordinate ceiling on a preselected parameter ball, and literal
preservation of every frozen top/protected coordinate and integer quota.

The coordinate ceiling is not postulated as a property of the output.  It is
deduced from the exact finite density-ratio estimate and an explicit baseline
slack inequality.  In the final Proposition 8.7 specialization that baseline
slack is discharged by the structured-cell count and the paper's `O(1/L)`
baseline-coordinate bound.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteExponentialFamily

namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]





/-- The literal `0, E e_p` head simplex used in the paper automatically
satisfies `HeadPatternsSeparated`; this is not an extra final hypothesis. -/
theorem headPatternsSeparated_of_paperHeadSimplex
    (P : Finset Nat) (hprime : ∀ p ∈ P, p.Prime)
    (E : Nat) (hE : 0 < E)
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E) :
    D.HeadPatternsSeparated := by
  rw [HeadPatternsSeparated, hpattern]
  exact PaperHeadSimplex.patternsSeparated P hprime E hE

end StructuredSampleData

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)











/-! The paper uses a compact *effective-score* box, not the crude sum of
all score norms.  The next estimates therefore take the correct pointwise
score bound and have constants independent of the number of active cells. -/













/-! ## Actual natural-number coordinates -/

















/-! ## Frozen top/protected coordinates and the integer ledger -/

















end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.RegularMeshPrimeCutoffsEventually -/
section


/-!
# Eventual population of every explicit regular-mesh prime cell

For a fixed regular mesh, each positive logarithmic cell has fixed positive
width.  Its multiplicative size on the original prime scale therefore tends
to infinity.  This file proves the scale-separation hypotheses used by the
Bertrand construction automatically for all sufficiently large `n`, and
hence produces the arithmetic partition and interval certificate without a
mesh or prime-existence assumption.
-/

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel RegularRelativeMesh PositiveCellTransfer

theorem tendsto_y_atTop :
    Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
  unfold y
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
    tendsto_natCast_atTop_atTop

/-- Every fixed positive logarithmic coordinate tends to infinity on the
original prime scale. -/
theorem tendsto_scalePoint_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ scalePoint n t) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ ↦ (y n) ^ t) atTop atTop :=
    (tendsto_rpow_atTop ht).comp tendsto_y_atTop
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  unfold scalePoint
  rw [Real.rpow_def_of_pos (Scale.y_pos hn)]
  congr 1
  ring

theorem scalePoint_add (n : ℕ) (a b : ℝ) :
    scalePoint n (a + b) = scalePoint n a * scalePoint n b := by
  unfold scalePoint
  rw [add_mul, Real.exp_add]

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The multiplicative ratio of a positive cell tends beyond two. -/
theorem eventually_two_mul_scalePoint_lower_le_upper
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    ∀ᶠ n : ℕ in atTop,
      2 * scalePoint n (M.lower k) ≤ scalePoint n (M.upper k) := by
  have hwidth := tendsto_scalePoint_atTop (M.width_pos hdelta k)
  have hevent := hwidth.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hevent] with n hn
  have hsum : M.upper k = M.lower k + M.width k := by
    unfold RegularRelativeMesh.Mesh.width
    ring
  rw [hsum, scalePoint_add]
  have hlower : 0 ≤ scalePoint n (M.lower k) := by
    unfold scalePoint
    exact (Real.exp_pos _).le
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hn hlower

/-- The lower endpoint of every fixed positive cell eventually exceeds
one. -/
theorem eventually_one_le_scalePoint_lower
    (hdelta : 0 < delta) (k : Fin M.cellCount) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ scalePoint n (M.lower k) :=
  (tendsto_scalePoint_atTop (M.lower_pos hdelta k)).eventually
    (eventually_ge_atTop (1 : ℝ))

/-- All explicit separation inequalities hold simultaneously because the
mesh has finitely many cells. -/
theorem eventually_scaleSeparation
    (hdelta : 0 < delta) (W : ℕ) :
    ∀ᶠ n : ℕ in atTop, ScaleSeparation M n W := by
  have hlow := (tendsto_scalePoint_atTop hdelta).eventually
    (eventually_ge_atTop (2 * W : ℝ))
  have hpositive : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        1 ≤ scalePoint n (M.lower k) ∧
          2 * scalePoint n (M.lower k) ≤ scalePoint n (M.upper k) := by
    rw [Filter.eventually_all]
    intro k
    exact (eventually_one_le_scalePoint_lower M hdelta k).and
      (eventually_two_mul_scalePoint_lower_le_upper M hdelta k)
  filter_upwards [hlow, hpositive] with n hnLow hnPositive
  exact ⟨hnLow, hnPositive⟩



end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.PaperCanonicalHeadPhysicalTarget -/
section


/-!
# The paper's explicit head simplex and physical interpolation

The head barycenter is not supplied as an arbitrary probability vector in
the paper.  Its nonzero-vertex coefficients are exactly `A_p / (E*q)` and
the zero-vertex coefficient is the remaining mass.  This file constructs
that literal vector from the finite reserve ledger and combines it with the
two fixed physical intervals around `mu`.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit PaperHeadSimplex ArithmeticModel

noncomputable section

namespace PaperGuardCensus



namespace HeadSimplexReserve

variable {P : Finset ℕ} (R : HeadSimplexReserve P)



















end HeadSimplexReserve



namespace PhysicalInterpolationTarget

variable {I : PhysicalIntervals}











end PhysicalInterpolationTarget

end PaperGuardCensus

namespace PaperBridgeFit.BridgeData

variable {P : Finset ℕ} {Band : Type*}
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData (PaperHeadSimplex.Tag P) Band)













/-- The common normalized cell-mass margin is the product of the explicit
head-reserve margin and the fixed physical interpolation margin. -/
theorem barycentricTargetOfPaperData_cellMassMargin
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (R : HeadSimplexReserve P)
    (K : PhysicalInterpolationTarget I) :
    (B.barycentricTargetOfPaperData I hlo hhi R K).cellMassMargin =
      R.margin * K.tau := rfl



end PaperBridgeFit.BridgeData

end

end Erdos390.Full

end

/- Source module: Erdos390.WholePaper.SafePrimeCounting -/
section


/-!
# A prime-counting asymptotic with an audited dependency closure

The pinned auxiliary package contains stronger convenience theorems whose
transitive imports include unfinished declarations.  This file instead
derives `π(x) ~ x / log x` from the already audited `MediumPNT` route used by
`FriableAsymptotic.theta_error_isBigO_log_power` and Mathlib's elementary
comparison between `π` and `θ`.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

private theorem div_log_isLittleO_id :
    (fun x : ℝ => x / Real.log x) =o[atTop] (fun x : ℝ => x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr
  apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  exact inv_mul_cancel₀ hlog

private theorem div_log_sq_isLittleO_div_log :
    (fun x : ℝ => x / Real.log x ^ 2) =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by
    apply div_eq_zero_iff.mpr
    rcases (div_eq_zero_iff.mp hx) with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by simp [hx]))).mpr
  apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  exact inv_mul_cancel₀ hlog

theorem theta_sub_id_isLittleO :
    (Chebyshev.theta - id) =o[atTop] (id : ℝ → ℝ) := by
  have htheta :
      (Chebyshev.theta - id) =O[atTop]
        (fun x : ℝ => x / Real.log x) := by
    simpa using
      Erdos390.Full.FriableAsymptotic.theta_error_isBigO_log_power 1
  exact htheta.trans_isLittleO div_log_isLittleO_id

theorem theta_div_log_sub_main_isLittleO :
    (fun x : ℝ =>
      Chebyshev.theta x / Real.log x - x / Real.log x) =o[atTop]
        (fun x : ℝ => x / Real.log x) := by
  have hmul := theta_sub_id_isLittleO.mul_isBigO
    (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)
  apply hmul.congr'
  · exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, id_eq]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
  · exact Eventually.of_forall fun x => by
      simp only [id_eq]
      rw [div_eq_mul_inv]

theorem primeCounting_sub_main_isLittleO :
    (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =o[atTop]
        (fun x : ℝ => x / Real.log x) := by
  have hpi :
      (fun x : ℝ =>
        (Nat.primeCounting ⌊x⌋₊ : ℝ) -
          Chebyshev.theta x / Real.log x) =o[atTop]
          (fun x : ℝ => x / Real.log x) :=
    Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO
      div_log_sq_isLittleO_div_log
  have hadd := hpi.add theta_div_log_sub_main_isLittleO
  apply hadd.congr' (Eventually.of_forall fun x => by ring) (Eventually.of_forall fun _ => rfl)

/-- Safe real-variable prime number theorem. -/
theorem primeCounting_real_isEquivalent :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ => x / Real.log x) :=
  primeCounting_sub_main_isLittleO

/-- Safe natural-variable form used to count the thirteen layers. -/
theorem primeCounting_nat_isEquivalent :
    (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have h := primeCounting_real_isEquivalent.comp_tendsto
    tendsto_natCast_atTop_atTop
  refine (h.congr_left ?_).congr_right ?_
  · exact Eventually.of_forall fun n => by
      simp [Function.comp_apply, Nat.floor_natCast]
  · exact Eventually.of_forall fun n => by
      rfl

end Erdos390.WholePaper.SafePrimeCounting

end

/- Source module: Erdos390.WholePaper.StationaryLayers -/
section


/-!
# Stationary prime layers

For a fixed row `r`, Section 3 uses the prime interval
`n / (r + 1) < p ≤ 2n / (2r + 1)`.  The definition below records the
endpoints by cross-multiplied natural-number inequalities, so there is no
rounding ambiguity.  Its cardinality is then identified with the exact
prime-counting difference to which the fixed-interval PNT applies.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section



@[simp]
theorem mem_stationaryPrimeLayer {n r p : ℕ} :
    p ∈ stationaryPrimeLayer n r ↔
      p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n := by
  simp only [stationaryPrimeLayer, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun hp ↦ hp.2
  · intro hp
    have hpLe : p ≤ 2 * n :=
      (Nat.le_mul_of_pos_right p (by omega : 0 < 2 * r + 1)).trans hp.2.2
    exact ⟨by omega, hp⟩

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPromotion -/
section


/-! # Promotion of residual central prime powers

This file formalizes the elementary promotion step from Section 10 of the
paper.  A positive block `B ≤ 2n` is multiplied by the least power of two
which puts it above `n`; the resulting block still lies at most `2n`.
-/

namespace Erdos390.WholePaper

noncomputable section





theorem promotionExponent_spec {n B : ℕ} (hB : 0 < B) :
    n < 2 ^ promotionExponent n B * B := by
  have htarget : n / B + 1 ≤ 2 ^ promotionExponent n B := by
    simpa only [promotionExponent] using
      Nat.le_pow_clog Nat.one_lt_two (n / B + 1)
  apply (Nat.div_lt_iff_lt_mul hB).mp
  omega

theorem promotionExponent_minimal {n B k : ℕ}
    (hk : k < promotionExponent n B) :
    2 ^ k * B ≤ n := by
  have hpow : 2 ^ k < n / B + 1 := by
    exact (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp hk
  have hpow' : 2 ^ k ≤ n / B := by omega
  exact (Nat.mul_le_mul_right B hpow').trans (Nat.div_mul_le_self n B)

theorem promotedBlock_gt {n B : ℕ} (hB : 0 < B) :
    n < promotedBlock n B := by
  exact promotionExponent_spec hB

theorem promotedBlock_le_two_mul {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ≤ 2 * n := by
  by_cases hBn : B ≤ n
  · have hdivPos : 0 < n / B := Nat.div_pos hBn hB
    have htarget : 1 < n / B + 1 := by omega
    have hkPos : 0 < promotionExponent n B := by
      simpa only [promotionExponent] using
        Nat.clog_pos Nat.one_lt_two htarget
    have hkPred : promotionExponent n B - 1 < promotionExponent n B := by
      omega
    have hprevious : 2 ^ (promotionExponent n B - 1) * B ≤ n :=
      promotionExponent_minimal hkPred
    have hkSplit : promotionExponent n B - 1 + 1 = promotionExponent n B := by
      omega
    rw [promotedBlock, ← hkSplit, pow_succ]
    calc
      (2 ^ (promotionExponent n B - 1) * 2) * B =
          2 * (2 ^ (promotionExponent n B - 1) * B) := by ac_rfl
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hprevious
  · have hnB : n < B := Nat.lt_of_not_ge hBn
    have hdiv : n / B = 0 := Nat.div_eq_of_lt hnB
    simp [promotedBlock, promotionExponent, hdiv, hBupper]

theorem promotedBlock_mem_centralInterval {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ∈ Finset.Ioc n (2 * n) := by
  exact Finset.mem_Ioc.mpr
    ⟨promotedBlock_gt hB, promotedBlock_le_two_mul hB hBupper⟩





theorem centralPrimeBlock_pos (n p : ℕ) : 0 < centralPrimeBlock n p := by
  cases p with
  | zero => simp [centralPrimeBlock]
  | succ p =>
      simpa only [centralPrimeBlock] using
        (pow_pos (Nat.succ_pos p)
          ((Nat.choose (2 * n) n).factorization (p + 1)))

theorem centralPrimeBlock_le_two_mul {n p : ℕ} (hn : 0 < n) :
    centralPrimeBlock n p ≤ 2 * n := by
  simpa only [centralPrimeBlock] using
    (Nat.pow_factorization_choose_le
      (p := p) (n := 2 * n) (k := n) (by omega))







theorem promotedCentralFactor_mem_centralInterval {n p : ℕ} (hn : 0 < n) :
    promotedCentralFactor n p ∈ Finset.Ioc n (2 * n) := by
  exact promotedBlock_mem_centralInterval
    (centralPrimeBlock_pos n p) (centralPrimeBlock_le_two_mul hn)

theorem promotedCentralFactor_gt {n p : ℕ} (hn : 0 < n) :
    n < promotedCentralFactor n p :=
  (Finset.mem_Ioc.mp (promotedCentralFactor_mem_centralInterval hn)).1











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ResidualCentralFactors -/
section


/-! # The finite family of promoted residual central factors -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section











theorem residualCentralPrimes_exponent_pos {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) :
    0 < (Nat.choose (2 * n) n).factorization p := by
  have hpMem : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hp).1
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  exact (Nat.prime_of_mem_primeFactors hpMem).factorization_pos_of_dvd
    hchoosePos.ne' (Nat.dvd_of_mem_primeFactors hpMem)









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPrimeBlockDecomposition -/
section


/-!
# Exact low/high decomposition of the central binomial coefficient

The central binomial coefficient is the product of its complete prime-power
blocks.  Splitting those blocks at the anchor cutoff and promoting every low
block therefore introduces exactly one aggregate power of two and no other
valuation error.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem largeCentralPrimes_prime {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem largeCentralPrimes_gt {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : X < p :=
  (Finset.mem_filter.mp hp).2











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralCarryAnchors -/
section


/-! # Exact arithmetic of the fixed-prefix central carry anchors -/

namespace Erdos390.WholePaper

noncomputable section





/-- Every allowed allocation cofactor places its carry prime anchor in the
central interval. -/
theorem stationaryPrimeLayer_mul_cofactor_mem_centralInterval
    {n r p q : ℕ} (hp : p ∈ stationaryPrimeLayer n r)
    (hqLower : r + 1 ≤ q) (hqUpper : q ≤ 2 * r + 1) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  have hmem := mem_stationaryPrimeLayer.mp hp
  apply Finset.mem_Ioc.mpr
  constructor
  · exact hmem.2.1.trans_le (Nat.mul_le_mul_left p hqLower)
  · exact (Nat.mul_le_mul_left p hqUpper).trans hmem.2.2



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorProduct -/
section


/-!
# Exact product of all three central-anchor families

This file isolates the finite algebra behind the full central-anchor lemma.
For every large central prime, a cofactor choice is required to follow either
its row-zero route or its stationary carry row.  The resulting marker factors
are combined with every promoted low prime-power block.  Their product is
proved to be the central binomial coefficient times the literal cofactor and
promotion divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem routedCentralCofactor_mem_centralInterval
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, hpRow, hqLower, hqUpper⟩
  · simpa only [hzero.2.2, mul_one] using
      (show p ∈ Finset.Ioc n (2 * n) from
        Finset.mem_Ioc.mpr ⟨hzero.1, hzero.2.1⟩)
  · exact stationaryPrimeLayer_mul_cofactor_mem_centralInterval
      hpRow hqLower hqUpper









theorem largeCentralAnchor_mem_centralInterval
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    largeCentralAnchor q p ∈ Finset.Ioc n (2 * n) := by
  exact routedCentralCofactor_mem_centralInterval (hq p hp)























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperScale -/
section


/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section





/-- The elementary logarithmic comparison `log n / n → 0`, made public
for later upper-bound estimates. -/
theorem log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

/-- The second-order scale `n / log n` diverges to infinity. -/
theorem secondOrderScale_tendsto_atTop :
    Tendsto secondOrderScale atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop,
        0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright :
      Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨log_natCast_div_natCast_tendsto_zero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
      secondOrderScale n
    rw [secondOrderScale, inv_div]

/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

/-- Eventually the second-order scale is strictly positive. -/
theorem eventually_secondOrderScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact secondOrderScale_pos hn

/-- The second-order scale is sublinear. -/
theorem secondOrderScale_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ secondOrderScale n / (n : ℝ))
      atTop (nhds 0) := by
  have hinvLog :
      Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ))
        atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  apply hinvLog.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [secondOrderScale]
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  have hlogNe : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp





/-- Ceiling changes `c n/log n` only by a negligible relative error. -/
theorem upperTailLength_normalized_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailLength c n : ℝ) / secondOrderScale n)
      atTop (nhds c) := by
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
      secondOrderScale_tendsto_atTop

/-- The chosen upper tail is `o(n)`. -/
theorem upperTailLength_ratio_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    (upperTailLength_normalized_tendsto hc).mul
      secondOrderScale_ratio_tendsto_zero
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hscaleNe : secondOrderScale n ≠ 0 := hscale.ne'
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  field_simp





















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/











/-- Under the paper's interval-size condition, the two raw blocks exhaust
the whole lower interval `(n,2n]`. -/
theorem roughRawCandidateSet_eq_Ioc
    {n h K : ℕ} (hKh : K * h ≤ n) :
    roughRawCandidateSet n h K = Finset.Ioc n (2 * n) := by
  ext a
  simp only [roughRawCandidateSet, roughHighLowerBlock,
    roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc]
  omega

/-- The upper tail is disjoint from every raw lower candidate. -/
theorem roughUpperBlock_disjoint_rawCandidateSet
    (n h K : ℕ) :
    Disjoint (roughUpperBlock n h) (roughRawCandidateSet n h K) := by
  rw [Finset.disjoint_left]
  intro a haUpper haLower
  simp only [roughUpperBlock, roughRawCandidateSet,
    roughHighLowerBlock, roughBroadLowerBlock, Finset.mem_Ioc,
    Finset.mem_union] at haUpper haLower
  rcases haLower with haHigh | haBroad <;> omega







/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod



































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CompleteRoughDecomposition -/
section


/-!
# Complete rough/smooth decomposition

The complete rough label retains exactly the prime-power coordinates above
`y`.  This file defines the complementary literal quotient and proves that
the two pieces recover the original natural number, with exact complementary
factorizations and no auxiliary decomposition hypothesis.
-/

namespace Erdos390.WholePaper

noncomputable section



/-! ## Positivity, divisibility, and product recovery -/

/-- A complete rough label is always positive, including for `a = 0`, when
the empty factorization gives label `1`. -/
theorem completeRoughLabel_pos (y a : ℕ) :
    0 < completeRoughLabel y a := by
  rw [completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

theorem completeRoughLabel_ne_zero (y a : ℕ) :
    completeRoughLabel y a ≠ 0 :=
  (completeRoughLabel_pos y a).ne'

/-- Literal Finsupp form of the high-prime factorization. -/
theorem completeRoughLabel_factorization_eq_filter_gt (y a : ℕ) :
    (completeRoughLabel y a).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughSignature] using
    completeRoughLabel_factorization y a

/-- Coordinate form of the exact high-prime factorization. -/
theorem completeRoughLabel_factorization_apply (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeRoughLabel_factorization_eq_filter_gt y a)
  simpa only [Finsupp.filter_apply] using h

/-- The retained high-prime product is a literal divisor of the original
number. -/
theorem completeRoughLabel_dvd (y a : ℕ) :
    completeRoughLabel y a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd
      (completeRoughLabel_ne_zero y a) ha,
      completeRoughLabel_factorization_eq_filter_gt]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs <;> simp

/-- The requested multiplication direction: the original number is the
rough label times its literal complementary quotient. -/
theorem completeRough_decomposition (y a : ℕ) :
    a = completeRoughLabel y a * completeSmoothPart y a := by
  calc
    a = a / completeRoughLabel y a * completeRoughLabel y a :=
      (Nat.div_mul_cancel (completeRoughLabel_dvd y a)).symm
    _ = completeRoughLabel y a * (a / completeRoughLabel y a) :=
      Nat.mul_comm _ _
    _ = completeRoughLabel y a * completeSmoothPart y a := rfl



/-! ## The complementary low-prime factorization -/

/-- The quotient retains exactly the complementary coordinates `p ≤ y`. -/
theorem completeSmoothPart_factorization_eq_filter_le (y a : ℕ) :
    (completeSmoothPart y a).factorization =
      a.factorization.filter (fun p ↦ p ≤ y) := by
  rw [completeSmoothPart,
    Nat.factorization_div (completeRoughLabel_dvd y a),
    completeRoughLabel_factorization_eq_filter_gt]
  ext p
  simp only [Finsupp.filter_apply]
  by_cases hpLow : p ≤ y
  · have hpNotHigh : ¬y < p := Nat.not_lt_of_ge hpLow
    simp [hpLow, hpNotHigh]
  · have hpHigh : y < p := Nat.lt_of_not_ge hpLow
    simp [hpLow, hpHigh]

/-- Coordinate form of the exact low-prime factorization. -/
theorem completeSmoothPart_factorization_apply (y a p : ℕ) :
    (completeSmoothPart y a).factorization p =
      if p ≤ y then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeSmoothPart_factorization_eq_filter_le y a)
  simpa only [Finsupp.filter_apply] using h

/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp

/-- Nonzero smooth-part coordinates lie weakly below the cutoff. -/
theorem completeSmoothPart_factorization_support
    {y a p : ℕ}
    (hp : (completeSmoothPart y a).factorization p ≠ 0) :
    p ≤ y := by
  rw [completeSmoothPart_factorization_apply] at hp
  by_contra hpLow
  simp [hpLow] at hp

/-- Every prime divisor of the complete rough label is above `y`. -/
theorem prime_dvd_completeRoughLabel_gt
    {y a p : ℕ} (hp : p.Prime)
    (hpDvd : p ∣ completeRoughLabel y a) :
    y < p := by
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeRoughLabel_ne_zero y a) hpDvd
  exact completeRoughLabel_factorization_support hfactorPos.ne'

/-- For a positive original number, the complementary quotient is positive. -/
theorem completeSmoothPart_pos {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a := by
  rw [completeSmoothPart]
  apply Nat.div_pos
  · exact Nat.le_of_dvd ha (completeRoughLabel_dvd y a)
  · exact completeRoughLabel_pos y a

/-- For a positive original number, the complementary quotient is literally
`(y+1)`-smooth in Mathlib's positive-number convention. -/
theorem completeSmoothPart_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeSmoothPart y a ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpDvd
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeSmoothPart_pos ha).ne' hpDvd
  have hpLow : p ≤ y :=
    completeSmoothPart_factorization_support hfactorPos.ne'
  omega

/-! ## Uniqueness and the smooth-label criterion -/



/-- For positive `a`, the rough label is `1` exactly when `a` is
`(y+1)`-smooth. -/
theorem completeRoughLabel_eq_one_iff_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeRoughLabel y a = 1 ↔
      a ∈ Nat.smoothNumbers (y + 1) := by
  constructor
  · intro hlabel
    have haPart : a = completeSmoothPart y a := by
      simpa only [hlabel, one_mul] using
        completeRough_decomposition y a
    rw [haPart]
    exact completeSmoothPart_mem_smoothNumbers ha
  · intro haSmooth
    by_contra hlabel
    obtain ⟨p, hp, hpDvdLabel⟩ :=
      Nat.exists_prime_and_dvd hlabel
    have hpHigh : y < p :=
      prime_dvd_completeRoughLabel_gt hp hpDvdLabel
    have hpDvdA : p ∣ a :=
      hpDvdLabel.trans (completeRoughLabel_dvd y a)
    have hpLow :=
      (Nat.mem_smoothNumbers').mp haSmooth p hp hpDvdA
    omega



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomMarkerPools -/
section


/-!
# Literal marker pools for the four bottom bank moves

The four rows below are the natural-number half-open intervals appearing in
the paper.  Each is split at its integer midpoint into two fixed one-half
orientation subintervals.  This file proves only exact finite interval and
factor arithmetic; prime supply is deliberately kept separate.
-/

namespace Erdos390.WholePaper

noncomputable section











































/-- A marker in its row makes both endpoint states and the donor lie in
the factor interval `(n,M]`. -/
theorem bankBottom_states_donor_mem_factorInterval
    {n M marker : ℕ} {move : BankBottomMove}
    (hmarker : marker ∈ bankBottomMarkerInterval n M move) :
    bankBottomLowerState move marker ∈ factorInterval n M ∧
      bankBottomUpperState move marker ∈ factorInterval n M ∧
      bankBottomDonor move marker ∈ factorInterval n M := by
  cases move <;>
    simp only [bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, bankBottomLowerState,
      bankBottomUpperState, bankBottomDonor,
      bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
      bankBottomDonorMultiplier, factorInterval] at hmarker ⊢ <;>
    omega



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomConcreteDemand -/
section


/-!
# Concrete request demand for the eight bottom bank pools

The formal floating-rounding theorem produces the sharper floor-log error box
`4 * log_2(M) * log_p(M)`.  We reserve the paper's ceiling-log,
endpoint-free box at `3n`.  A request is an actual signed bank
slot together with one of the four bottom moves; its sign selects the fixed
orientation pool.  Thus every one of the eight pool fibers has exactly
`sum_{p <= floor(n^(2/9))} beta_p` requests.

The analytic count is also proved here.  Primes below `(3n)^(1/5)` are
bounded trivially; their contribution is `o(n^(2/9))`.  Above that cutoff,
`clog_p(3n) <= 5`, while the safe PNT gives `pi(y) = O(y / log y)`.  Since
`log y` is a fixed positive fraction of `log n`, the total demand is
`O(y)`, hence negligible compared with `n / (log n)^2`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section





































private theorem bankRoundingBeta_le_head
    {n p : ℕ} (hp : p.Prime) :
    bankRoundingBeta n p ≤
      4 * bankRoundingDepth n * bankRoundingDepth n := by
  have hclog : Nat.clog p (3 * n) ≤ Nat.clog 2 (3 * n) :=
    Nat.clog_anti_left Nat.one_lt_two hp.two_le
  rw [bankRoundingBeta, bankRoundingDepth]
  exact Nat.mul_le_mul_left (4 * Nat.clog 2 (3 * n)) hclog

private theorem bankRoundingBeta_le_tail
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hcut : bankRoundingHeadCutoff n < p) :
    bankRoundingBeta n p ≤ 20 * bankRoundingDepth n := by
  let root : ℝ := (3 * (n : ℝ)) ^ (1 / 5 : ℝ)
  have hrootPos : 0 < root := by
    dsimp [root]
    positivity
  have hrootLt : root < (p : ℝ) := by
    have hfloor : root < (bankRoundingHeadCutoff n : ℝ) + 1 := by
      simpa only [root, bankRoundingHeadCutoff] using
        (Nat.lt_floor_add_one root)
    have hsucc : bankRoundingHeadCutoff n + 1 ≤ p := by omega
    have hsuccR : (bankRoundingHeadCutoff n : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast hsucc
    exact hfloor.trans_le hsuccR
  have hrootPow : root ^ (5 : ℕ) = 3 * (n : ℝ) := by
    dsimp [root]
    calc
      ((3 * (n : ℝ)) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) =
          (3 * (n : ℝ)) ^ ((1 / 5 : ℝ) * (5 : ℕ)) :=
        (Real.rpow_mul_natCast (by positivity) _ _).symm
      _ = 3 * (n : ℝ) := by norm_num [Real.rpow_one]
  have hpowR : 3 * (n : ℝ) < (p : ℝ) ^ (5 : ℕ) := by
    rw [← hrootPow]
    exact pow_lt_pow_left₀ hrootLt hrootPos.le (by omega)
  have hpow : 3 * n < p ^ 5 := by exact_mod_cast hpowR
  have hclog : Nat.clog p (3 * n) ≤ 5 :=
    (Nat.clog_le_iff_le_pow hp.one_lt).2 hpow.le
  calc
    bankRoundingBeta n p =
        4 * bankRoundingDepth n * Nat.clog p (3 * n) := rfl
    _ ≤ 4 * bankRoundingDepth n * 5 :=
      Nat.mul_le_mul_left _ hclog
    _ = 20 * bankRoundingDepth n := by ring

/-- Exact finite beta-sum estimate underlying the asymptotic demand bound. -/
theorem bankBottomPaperDemand_le_majorant (n : ℕ) :
    bankBottomPaperDemand n ≤ bankBottomPaperDemandMajorant n := by
  classical
  let P := bankRoundingPrimeSupport n
  let head := P.filter (fun p ↦ p ≤ bankRoundingHeadCutoff n)
  let tail := P.filter (fun p ↦ ¬p ≤ bankRoundingHeadCutoff n)
  have hsplit :
      (∑ p ∈ P, bankRoundingBeta n p) =
        (∑ p ∈ head, bankRoundingBeta n p) +
          ∑ p ∈ tail, bankRoundingBeta n p := by
    simpa only [head, tail] using
      (P.sum_filter_add_sum_filter_not
        (fun p ↦ p ≤ bankRoundingHeadCutoff n)
        (fun p ↦ bankRoundingBeta n p)).symm
  have hheadPoint : ∀ p ∈ head,
      bankRoundingBeta n p ≤
        4 * bankRoundingDepth n * bankRoundingDepth n := by
    intro p hp
    exact bankRoundingBeta_le_head
      (bankRoundingPrimeSupport_prime (Finset.mem_filter.mp hp).1)
  have hheadCard : head.card ≤ bankRoundingHeadCutoff n + 1 := by
    have hsubset : head ⊆ Finset.range (bankRoundingHeadCutoff n + 1) := by
      intro p hp
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    simpa using Finset.card_le_card hsubset
  have hhead :
      (∑ p ∈ head, bankRoundingBeta n p) ≤
        (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) := by
    calc
      (∑ p ∈ head, bankRoundingBeta n p) ≤
          head.card *
            (4 * bankRoundingDepth n * bankRoundingDepth n) := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul head (fun p ↦ bankRoundingBeta n p)
            (4 * bankRoundingDepth n * bankRoundingDepth n) hheadPoint
      _ ≤ (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) :=
        Nat.mul_le_mul_right _ hheadCard
  have htailPoint : ∀ p ∈ tail,
      bankRoundingBeta n p ≤ 20 * bankRoundingDepth n := by
    intro p hp
    by_cases hn : n = 0
    · subst n
      simp [bankRoundingBeta, bankRoundingDepth]
    · apply bankRoundingBeta_le_tail (Nat.pos_of_ne_zero hn)
        (bankRoundingPrimeSupport_prime (Finset.mem_filter.mp hp).1)
      exact Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
  have hPcard : P.card = Nat.primeCounting (yNat n) := by
    simpa only [P, bankRoundingPrimeSupport, Nat.primeCounting] using
      Nat.primesBelow_card_eq_primeCounting' (yNat n + 1)
  have htailCard : tail.card ≤ Nat.primeCounting (yNat n) := by
    rw [← hPcard]
    exact Finset.card_filter_le _ _
  have htail :
      (∑ p ∈ tail, bankRoundingBeta n p) ≤
        Nat.primeCounting (yNat n) * (20 * bankRoundingDepth n) := by
    calc
      (∑ p ∈ tail, bankRoundingBeta n p) ≤
          tail.card * (20 * bankRoundingDepth n) := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul tail (fun p ↦ bankRoundingBeta n p)
            (20 * bankRoundingDepth n) htailPoint
      _ ≤ Nat.primeCounting (yNat n) *
          (20 * bankRoundingDepth n) :=
        Nat.mul_le_mul_right _ htailCard
  rw [bankBottomPaperDemand, bankBottomPaperDemandMajorant]
  change (∑ p ∈ P, bankRoundingBeta n p) ≤ _
  rw [hsplit]
  calc
    (∑ p ∈ head, bankRoundingBeta n p) +
        ∑ p ∈ tail, bankRoundingBeta n p ≤
      (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) +
        Nat.primeCounting (yNat n) *
          (20 * bankRoundingDepth n) := Nat.add_le_add hhead htail
    _ = 4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) +
        20 * bankRoundingDepth n * Nat.primeCounting (yNat n) := by ring

private theorem yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

private theorem eventually_y_half_le_yNat :
    ∀ᶠ n : ℕ in atTop, y n / 2 ≤ (yNat n : ℝ) := by
  have hyTop : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hyTop.eventually (eventually_ge_atTop (2 : ℝ))] with n hyn
  have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
  linarith

private theorem bankRoundingDepth_le_two_mul_log2
    {n : ℕ} (hn : 0 < n) :
    bankRoundingDepth n ≤ 2 * Nat.log2 (3 * n) := by
  have hX : 3 * n ≠ 0 := by omega
  have hone : 1 ≤ Nat.log 2 (3 * n) :=
    (Nat.le_log_iff_pow_le Nat.one_lt_two hX).2 (by
      simpa only [pow_one] using (show 2 ≤ 3 * n by omega))
  have hceil : Nat.clog 2 (3 * n) ≤ (Nat.log 2 (3 * n)).succ :=
    Nat.clog_le_of_le_pow
      (Nat.lt_pow_succ_log_self Nat.one_lt_two (3 * n)).le
  rw [bankRoundingDepth, Nat.log2_eq_log_two]
  omega

private theorem bankRoundingDepth_cast_le_two_logb
    {n : ℕ} (hn : 0 < n) :
    (bankRoundingDepth n : ℝ) ≤
      2 * (Real.log (3 * (n : ℝ)) / Real.log 2) := by
  have hnat := bankRoundingDepth_le_two_mul_log2 hn
  have hcast : (bankRoundingDepth n : ℝ) ≤
      2 * (Nat.log2 (3 * n) : ℝ) := by exact_mod_cast hnat
  have hfloor : (Nat.log2 (3 * n) : ℝ) ≤
      Real.logb 2 ((3 * n : ℕ) : ℝ) := Real.log2_le_logb (3 * n)
  calc
    (bankRoundingDepth n : ℝ) ≤ 2 * (Nat.log2 (3 * n) : ℝ) := hcast
    _ ≤ 2 * Real.logb 2 ((3 * n : ℕ) : ℝ) := by gcongr
    _ = 2 * (Real.log (3 * (n : ℝ)) / Real.log 2) := by
      norm_num [Real.logb]



private theorem bankRoundingDepth_isBigO_log_yNat :
    (fun n : ℕ ↦ (bankRoundingDepth n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (yNat n : ℝ)) := by
  apply IsBigO.of_bound (20 / Real.log 2)
  filter_upwards [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
      with n hn hyLog
  have hnPos : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogY : 0 < Real.log (yNat n : ℝ) := by
    have : 0 < (1 / 5 : ℝ) * L n := mul_pos (by norm_num) (by simpa [L])
    exact this.trans_le hyLog
  have hlogThree : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogMul : Real.log (3 * (n : ℝ)) =
      Real.log 3 + Real.log (n : ℝ) :=
    Real.log_mul (by norm_num) hnPos.ne'
  have hdepth := bankRoundingDepth_cast_le_two_logb
    (show 0 < n by omega)
  rw [hlogMul] at hdepth
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLn : L n ≤ 5 * Real.log (yNat n : ℝ) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ bankRoundingDepth n),
    Real.norm_eq_abs, abs_of_nonneg hlogY.le]
  have hsum : Real.log 3 + Real.log (n : ℝ) ≤
      2 * Real.log (n : ℝ) := by linarith
  have hbase : (bankRoundingDepth n : ℝ) ≤
      (4 / Real.log 2) * L n := by
    calc
      (bankRoundingDepth n : ℝ) ≤
          2 * ((Real.log 3 + Real.log (n : ℝ)) / Real.log 2) := hdepth
      _ ≤ 2 * ((2 * Real.log (n : ℝ)) / Real.log 2) := by
        exact mul_le_mul_of_nonneg_left
          ((div_le_div_iff_of_pos_right hlogTwo).2 hsum) (by norm_num)
      _ = (4 / Real.log 2) * L n := by
        rw [L]
        ring
  calc
    (bankRoundingDepth n : ℝ) ≤
        (4 / Real.log 2) * L n := hbase
    _ ≤ (4 / Real.log 2) * (5 * Real.log (yNat n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLn (by positivity)
    _ = (20 / Real.log 2) * Real.log (yNat n : ℝ) := by ring

private theorem bankRoundingHeadMajorant_isLittleO_yNat :
    (fun n : ℕ ↦
      ((4 * bankRoundingDepth n * bankRoundingDepth n *
        (bankRoundingHeadCutoff n + 1) : ℕ) : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ)) := by
  let headModel : ℕ → ℝ := fun n ↦
    (3 * (n : ℝ)) ^ (1 / 5 : ℝ) * Real.log (3 * (n : ℝ)) ^ 2
  have hheadO :
      (fun n : ℕ ↦
        ((4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) : ℕ) : ℝ)) =O[atTop]
        headModel := by
    apply IsBigO.of_bound (32 / Real.log 2 ^ 2)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hroot : 1 ≤ (3 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.one_le_rpow
        (by exact_mod_cast (show 1 ≤ 3 * n by omega)) (by norm_num)
    have hcutCast : (bankRoundingHeadCutoff n : ℝ) ≤
        (3 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have hcut : (bankRoundingHeadCutoff n : ℝ) + 1 ≤
        2 * (3 * (n : ℝ)) ^ (1 / 5 : ℝ) := by linarith
    have hdepth := bankRoundingDepth_cast_le_two_logb hn
    have hlogNonneg : 0 ≤ Real.log (3 * (n : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * n by omega))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) : ℕ)),
      Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))]
    push_cast
    calc
      (4 : ℝ) * bankRoundingDepth n * bankRoundingDepth n *
          ((bankRoundingHeadCutoff n : ℝ) + 1) ≤
        4 * (2 * (Real.log (3 * (n : ℝ)) / Real.log 2)) *
          (2 * (Real.log (3 * (n : ℝ)) / Real.log 2)) *
            (2 * (3 * (n : ℝ)) ^ (1 / 5 : ℝ)) := by gcongr
      _ = (32 / Real.log 2 ^ 2) * headModel n := by
        dsimp [headModel]
        ring
  have hreal0 :
      (fun x : ℝ ↦ Real.log x ^ (2 : ℕ) * x ^ (1 / 5 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ (1 / 45 : ℝ) * x ^ (1 / 5 : ℝ)) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : ℝ) < 1 / 45)).mul_isBigO
          (isBigO_refl (fun x : ℝ ↦ x ^ (1 / 5 : ℝ)) atTop)
  have hreal :
      (fun x : ℝ ↦ x ^ (1 / 5 : ℝ) * Real.log x ^ 2) =o[atTop]
        (fun x : ℝ ↦ x ^ (2 / 9 : ℝ)) := by
    apply hreal0.congr'
    · exact Eventually.of_forall fun x ↦ by
        change Real.log x ^ (2 : ℕ) * x ^ (1 / 5 : ℝ) =
          x ^ (1 / 5 : ℝ) * Real.log x ^ (2 : ℕ)
        exact mul_comm (Real.log x ^ (2 : ℕ)) (x ^ (1 / 5 : ℝ))
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_add hx]
      norm_num
  have hthreeTop : Tendsto (fun n : ℕ ↦ 3 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hmodel : headModel =o[atTop]
      (fun n : ℕ ↦ (3 * (n : ℝ)) ^ (2 / 9 : ℝ)) := by
    simpa only [headModel] using hreal.comp_tendsto hthreeTop
  have hscaledY :
      (fun n : ℕ ↦ (3 * (n : ℝ)) ^ (2 / 9 : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    apply IsBigO.of_bound (2 * 3 ^ (2 / 9 : ℝ))
    filter_upwards [eventually_y_half_le_yNat,
        eventually_gt_atTop 0] with n hyFloor hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hthree :
        (3 * (n : ℝ)) ^ (2 / 9 : ℝ) =
          3 ^ (2 / 9 : ℝ) * y n := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hnR.le]
      rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ yNat n),
      hthree]
    have hyScaled : y n ≤ 2 * (yNat n : ℝ) := by linarith
    calc
      3 ^ (2 / 9 : ℝ) * y n ≤
          3 ^ (2 / 9 : ℝ) * (2 * (yNat n : ℝ)) :=
        mul_le_mul_of_nonneg_left hyScaled
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      _ = (2 * 3 ^ (2 / 9 : ℝ)) * (yNat n : ℝ) := by ring
  exact (hheadO.trans_isLittleO hmodel).trans_isBigO hscaledY

private theorem bankRoundingTailMajorant_isBigO_yNat :
    (fun n : ℕ ↦
      ((20 * bankRoundingDepth n * Nat.primeCounting (yNat n) : ℕ) : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ)) := by
  have hpnt0 :=
    SafePrimeCounting.primeCounting_nat_isEquivalent.comp_tendsto
      yNat_tendsto_atTop
  have hpnt :
      (fun n : ℕ ↦ (Nat.primeCounting (yNat n) : ℝ)) =O[atTop]
        (fun n : ℕ ↦
          (yNat n : ℝ) / Real.log (yNat n : ℝ)) := by
    simpa only [Function.comp_apply] using hpnt0.isBigO
  have hmul := bankRoundingDepth_isBigO_log_yNat.mul hpnt
  have hcore :
      (fun n : ℕ ↦
        (bankRoundingDepth n : ℝ) * Nat.primeCounting (yNat n)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    apply hmul.congr' (Eventually.of_forall fun _n ↦ rfl)
    filter_upwards [yNat_tendsto_atTop.eventually (eventually_gt_atTop 1)]
        with n hY
    have hlog : Real.log (yNat n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hY)).ne'
    field_simp
  have h20 := hcore.const_mul_left (20 : ℝ)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h20

/-- The exact common request demand is `O(floor(n^(2/9)))`. -/
theorem bankBottomPaperDemand_isBigO_yNat :
    (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ)) := by
  have hmajorantPoint :
      (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (bankBottomPaperDemandMajorant n : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankBottomPaperDemand n),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankBottomPaperDemandMajorant n), one_mul]
    exact_mod_cast bankBottomPaperDemand_le_majorant n
  have hmajorant :
      (fun n : ℕ ↦ (bankBottomPaperDemandMajorant n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    have hadd := (bankRoundingHeadMajorant_isLittleO_yNat.isBigO).add
      bankRoundingTailMajorant_isBigO_yNat
    apply hadd.congr'
    · exact Eventually.of_forall fun n ↦ by
        unfold bankBottomPaperDemandMajorant
        push_cast
        ring
    · exact Eventually.of_forall fun _n ↦ rfl
  exact hmajorantPoint.trans hmajorant











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPaperComponents -/
section


/-!
# Actual bottom-bank components from the concrete marker matching

The capacity argument deliberately matches the rectangular upper-bound family
consisting of every signed slot and all four bottom rows.  The path belonging
to a small source prime does not use every one of those rows: source `3` uses
only `3→2→1`, and source `2` uses only `2→1`.  This file therefore separates
the full matched family from the literal relevant subfamily before forming any
set of used occurrences.

For every matched request we retain its actual prime marker, the two state
factors in the corresponding row, and its donor occurrence.  A finite set of
occurrence values is used, so in the last two rows the donor and the upper
state are literally one occurrence, rather than two tagged copies.  The only
global input is the already constructed injective marker matching.  All other
claims below are explicit interval, factorization, and large-prime arithmetic.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal relevant subfamily -/





















































/-! ## The deterministic truncated bottom path -/

























/-! ## A realization obtained from the actual matching -/





namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)





















/-- Both row endpoints and the donor are actual factors in `(n,M]`. -/
theorem states_donor_mem_factorInterval (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    realization.lowerStateFactor request ∈ factorInterval n M ∧
      realization.upperStateFactor request ∈ factorInterval n M ∧
      realization.donorFactor request ∈ factorInterval n M := by
  simpa only [lowerStateFactor, upperStateFactor, donorFactor] using
    bankBottom_states_donor_mem_factorInterval
      (realization.marker_mem_row hTwoN request)







/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/









namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)























































end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/



























end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/







/-! ## Eventual local geometry and the terminal realized family -/

private theorem bankBottom_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

theorem eventually_bankBottom_six_le_yNat :
    ∀ᶠ n : ℕ in atTop, 6 ≤ yNat n :=
  bankBottom_yNat_tendsto_atTop.eventually (eventually_ge_atTop 6)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryConcreteDemand -/
section


/-!
# Concrete ordinary-component requests and their demand

For every signed rounding slot, this file materializes one request for every
nonterminal source of its actual core path.  A request is routed by its exact
geometric-grid index and by the sign of the slot.  The request fibers are
finite sigma types, not cardinality placeholders.

The path congestion bounds give `17 * sum beta` at each small scale and the
sharp `2 * sum beta` at every large scale.  Finally the already audited
`O(yNat)` beta reserve is compared with the worst ordinary marker scale
`(n/log n)/yNat`; this is the uniform little-o estimate required by all moving
grid scales `Q <= yNat`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section





















/-! ## Exact request-fiber cardinality -/

















/-! ## The beta reserve against the worst moving ordinary scale -/



theorem yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) / bankOrdinaryWorstMarkerScale n)
      atTop (nhds 0) := by
  have hsqueeze : Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) /
        bankOrdinaryWorstMarkerScale n) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds Erdos390.Full.Scale.tendsto_endpointRatio_zero
    · filter_upwards [eventually_gt_atTop 2] with n hn
      have hscale : 0 < bankOrdinaryWorstMarkerScale n := by
        rw [bankOrdinaryWorstMarkerScale]
        exact div_pos (secondOrderScale_pos (by omega)) (by positivity)
      exact div_nonneg (Nat.cast_nonneg _) hscale.le
    · filter_upwards [eventually_ge_atTop 3,
          Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
          with n hn hlogY
      have hnPos : (0 : ℝ) < n := by positivity
      have hL : 1 ≤ L n := by
        rw [L]
        exact (show (1 : ℝ) ≤ Real.log (n : ℝ) by
          have hthree : (3 : ℝ) ≤ n := by exact_mod_cast hn
          have : Real.exp 1 ≤ (n : ℝ) :=
            Real.exp_one_lt_three.le.trans hthree
          exact (Real.le_log_iff_exp_le hnPos).2 this)
      have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
      have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
      have hyNatOne : (1 : ℝ) ≤ yNat n := by
        have hlogPos : 0 < Real.log (yNat n : ℝ) := by
          have hLPos : 0 < L n := lt_of_lt_of_le (by norm_num) hL
          nlinarith
        exact ((Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogPos).le
      have hmax : max 1 (yNat n : ℝ) = yNat n := max_eq_right hyNatOne
      rw [bankOrdinaryWorstMarkerScale, secondOrderScale, hmax]
      have hyNatPos : (0 : ℝ) < yNat n := lt_of_lt_of_le (by norm_num) hyNatOne
      have hLPos : 0 < L n := lt_of_lt_of_le (by norm_num) hL
      rw [show Real.log (n : ℝ) = L n by rfl]
      have hidentity :
          (yNat n : ℝ) / (((n : ℝ) / L n) / (yNat n : ℝ)) =
            (yNat n : ℝ) ^ 2 * L n / (n : ℝ) := by
        field_simp
      rw [hidentity, endpointRatio]
      apply div_le_div_of_nonneg_right _ hnPos.le
      calc
        (yNat n : ℝ) ^ 2 * L n ≤ y n ^ 2 * L n := by
          gcongr
        _ ≤ y n ^ 2 * L n ^ 2 := by
          have hySq : 0 ≤ y n ^ 2 := sq_nonneg _
          have hLsq : L n ≤ L n ^ 2 := by
            nlinarith [sq_nonneg (L n)]
          exact mul_le_mul_of_nonneg_left hLsq hySq
  exact hsqueeze















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankOrdinaryPaperComponents -/
section


/-!
# Realized ordinary bank components

An ordinary matching supplies an actual pair `(P,u)` to every concrete path
request `q→b`.  This file materializes the three factor occurrences

* source state `P*q`,
* target state `P*b`, and
* backing donor `P*u`.

All three lie in `(n,M]` and have the same complete rough signature.  The
large prime marker is recovered uniquely from any realized occurrence, which
gives marker injectivity, donor-product injectivity, and collision-freedom
across requests, scales, and orientations.  Finally, cancellation of the
common marker turns the realized component changes back into the actual
finite path telescope.

The public names intentionally mirror `BankBottomPaperComponents`: a
realization object, factor-valued methods, an occurrence-kind enumeration,
and `occurrenceValue`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Coarse global size bounds -/

/-- A prime path has at most `p` nonterminal component sources.  This coarse
bound is deliberately independent of the geometric-cell congestion bounds:
it is the convenient global estimate used when every ordinary marker is
guarded at once. -/
theorem bankOrdinaryPrimeCoreSources_card_le
    {p : ℕ} (hp : p.Prime) :
    (bankOrdinaryCoreSources p).card ≤ p := by
  by_cases hp5 : p ≤ 5
  · simp [bankOrdinaryCoreSources_of_le_five hp5]
  · have hp6 : 6 ≤ p := by omega
    have hpPower : ¬ IsPowerOfTwo p :=
      prime_not_isPowerOfTwo_of_five_le hp (by omega)
    have hsubset : bankOrdinaryCoreSources p ⊆ Finset.Icc 1 p := by
      intro source hsource
      have hspec := bankOrdinaryCoreSource_spec
        (show 5 ≤ p by omega) hpPower hsource
      exact Finset.mem_Icc.mpr
        ⟨(show 1 ≤ 6 by norm_num).trans hspec.1,
          bankOrdinaryCoreSource_le_start hsource⟩
    exact (Finset.card_le_card hsubset).trans (by simp)

/-- The number of signed beta slots is exactly twice the common one-sided
bottom demand. -/
theorem bankOrdinarySignedSlots_card_eq_two_mul_demand (n : ℕ) :
    Fintype.card (SignedBankSlot (bankRoundingBetaOnSupport n)) =
      2 * bankBottomPaperDemand n := by
  rw [Fintype.card_sigma]
  change (∑ p : bankRoundingPrimeSupport n,
    Fintype.card (Fin (bankRoundingBeta n p) ⊕ Fin (bankRoundingBeta n p))) = _
  simp only [Fintype.card_sum, Fintype.card_fin]
  calc
    (∑ p : ↑(bankRoundingPrimeSupport n),
        (bankRoundingBeta n p.1 + bankRoundingBeta n p.1)) =
        2 * ∑ p : ↑(bankRoundingPrimeSupport n),
          bankRoundingBeta n p.1 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _hp
            omega
    _ = 2 * bankBottomPaperDemand n := by
      congr 1
      simpa only [bankBottomPaperDemand] using
        (Finset.sum_attach (bankRoundingPrimeSupport n)
          (fun p ↦ bankRoundingBeta n p))

/-- The complete ordinary request family has the pointwise coarse bound
`2*yNat*sum beta`.  In particular, the source multiplicity contributes only
one additional factor of `yNat`. -/
theorem bankOrdinaryPaperRequests_card_le_two_mul_yNat_mul_demand
    (n : ℕ) :
    (bankOrdinaryPaperRequests n).card ≤
      2 * yNat n * bankBottomPaperDemand n := by
  rw [bankOrdinaryPaperRequests, Finset.card_univ, Fintype.card_sigma]
  calc
    (∑ slot : SignedBankSlot (bankRoundingBetaOnSupport n),
        Fintype.card ↑(bankOrdinaryCoreSources slot.1.1)) ≤
        ∑ _slot : SignedBankSlot (bankRoundingBetaOnSupport n),
          yNat n := by
            apply Finset.sum_le_sum
            intro slot _hslot
            simpa only [Fintype.card_coe] using
              (bankOrdinaryPrimeCoreSources_card_le
                  (bankRoundingPrimeSupport_prime slot.1.property)).trans
                (bankRoundingPrimeSupport_le_yNat slot.1.property)
    _ = Fintype.card
          (SignedBankSlot (bankRoundingBetaOnSupport n)) * yNat n := by
            simp
    _ = 2 * yNat n * bankBottomPaperDemand n := by
      rw [bankOrdinarySignedSlots_card_eq_two_mul_demand]
      ring

/-- Globally there are only `O(yNat²)` ordinary components.  This is the
coarse estimate needed to replace the cofactor of every ordinary marker,
without singling out a collision prefix. -/
theorem bankOrdinaryPaperRequests_card_isBigO_yNat_sq :
    (fun n : ℕ ↦ ((bankOrdinaryPaperRequests n).card : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
  have hpoint :
      (fun n : ℕ ↦ ((bankOrdinaryPaperRequests n).card : ℝ))
        =O[atTop]
          (fun n : ℕ ↦
            2 * (yNat n : ℝ) * bankBottomPaperDemand n) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (bankOrdinaryPaperRequests n).card),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ 2 * (yNat n : ℝ) * bankBottomPaperDemand n),
      one_mul]
    exact_mod_cast
      bankOrdinaryPaperRequests_card_le_two_mul_yNat_mul_demand n
  have hproduct :=
    (isBigO_refl (fun n : ℕ ↦ (yNat n : ℝ)) atTop).mul
      bankBottomPaperDemand_isBigO_yNat
  have hscaled := hproduct.const_mul_left (2 : ℝ)
  exact hpoint.trans (hscaled.congr'
    (Eventually.of_forall fun n ↦ by ring)
    (Eventually.of_forall fun n ↦ (pow_two (yNat n : ℝ)).symm))

/-- The public reserve interface for guarding every ordinary marker at once:
an `O(yNat²)` family consumes `o(secondOrderScale)` positions. -/
theorem yNat_sq_div_secondOrderScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2 / secondOrderScale n)
      atTop (nhds 0) := by
  apply yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hyNatOne : 1 ≤ yNat n := by
    rw [yNat]
    apply Nat.le_floor
    rw [y]
    have hnOneR : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 1 ≤ n by omega)
    simpa only [Nat.cast_one] using
      Real.one_le_rpow hnOneR
        (by norm_num : (0 : ℝ) ≤ 2 / 9)
  have hyNatPos : 0 < yNat n :=
    lt_of_lt_of_le Nat.zero_lt_one hyNatOne
  have hyPos : (0 : ℝ) < yNat n := by exact_mod_cast hyNatPos
  have hsecond : 0 < secondOrderScale n := secondOrderScale_pos hn
  rw [bankOrdinaryWorstMarkerScale,
    max_eq_right (by exact_mod_cast hyNatOne : (1 : ℝ) ≤ yNat n)]
  field_simp [hyPos.ne', hsecond.ne']



/-! ## Arithmetic helpers for rough signatures -/









/-! ## Marker injectivity inherited from the orientation pools -/









/-! ## The public realization object and its actual factors -/



namespace BankOrdinaryPaperRealization





































theorem donorValue_mem_factorInterval
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    R.donorValue request ∈ factorInterval n M := by
  have heligible := mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)
  simp only [donorValue, factorInterval, Finset.mem_Ioc]
  have hlower := heligible.2.2.2.2.2.2.1
  change 2 * n < R.marker request * R.donorCore request at hlower
  exact ⟨by omega, heligible.2.2.2.2.2.2.2⟩





































/-! ## The three actual occurrences and global collision-freedom -/





theorem two_mul_n_lt_donorValue
    {n M : ℕ} (R : BankOrdinaryPaperRealization n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    2 * n < R.donorValue request :=
  (mem_bankOrdinaryEligibleRelation.mp
    (R.markerDonorPair_mem request)).2.2.2.2.2.2.1

































/-! ## Realized component and signed-slot changes -/























end BankOrdinaryPaperRealization

/-! ## Eventual realized allocation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorCutoff -/
section


/-!
# The fixed-prefix central-anchor cutoff

For a fixed prefix depth `R`, the paper splits the central prime blocks at
`n / (R + 1)`.  This file gives an explicit sufficient threshold for all
scale separations and then connects that literal cutoff directly to the
large-prime routing and central-anchor product APIs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





theorem centralAnchorCutoffThreshold_pos (R : ℕ) :
    0 < centralAnchorCutoffThreshold R := by
  simp [centralAnchorCutoffThreshold]

/-- At the explicit threshold, the cutoff is at least `4(R+1)`. -/
theorem four_mul_succ_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    4 * (R + 1) ≤ centralAnchorCutoff R n := by
  rw [centralAnchorCutoff, Nat.le_div_iff_mul_le (by omega)]
  simpa only [centralAnchorCutoffThreshold, pow_two, mul_assoc] using hn



/-- The explicit threshold also puts `2n` strictly below the cutoff square. -/
theorem two_mul_lt_centralAnchorCutoff_sq
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * n < (centralAnchorCutoff R n) ^ 2 := by
  let X := centralAnchorCutoff R n
  have hX : 4 * (R + 1) ≤ X := by
    simpa only [X] using four_mul_succ_le_centralAnchorCutoff hn
  have hXPos : 0 < X := by omega
  have hnUpper : n < (R + 1) * (X + 1) := by
    simpa only [X, centralAnchorCutoff] using
      Nat.lt_mul_div_succ n (by omega : 0 < R + 1)
  have hlinear : 2 * (R + 1) * (X + 1) ≤ X ^ 2 := by
    calc
      2 * (R + 1) * (X + 1) ≤ 2 * (R + 1) * (2 * X) := by
        exact Nat.mul_le_mul_left (2 * (R + 1)) (by omega)
      _ = (4 * (R + 1)) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right X hX
      _ = X ^ 2 := by ring
  calc
    2 * n < 2 * ((R + 1) * (X + 1)) :=
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
    _ = 2 * (R + 1) * (X + 1) := by ring
    _ ≤ X ^ 2 := hlinear







































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperAnchorChangeBudget -/
section


/-!
# The cost of guarding every realized bank marker is negligible

The deliberately coarse global marker bound is `O(yNat²)`.  Since
`yNat² = o(n/log n)`, even changing every realized bank marker which meets
the fixed central prefix consumes only an arbitrarily small fixed fraction
of the central valuation reserve.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section



theorem bankPaperAnchorMarkerBudget_isBigO_yNat_sq :
    (fun n : ℕ ↦ (bankPaperAnchorMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
  have hySq :
      (fun n : ℕ ↦ (yNat n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_bankBottom_six_le_yNat] with n hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ yNat n),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (yNat n : ℝ)), one_mul]
    have hyOne : (1 : ℝ) ≤ yNat n := by exact_mod_cast (show 1 ≤ yNat n by omega)
    nlinarith [sq_nonneg ((yNat n : ℝ) - 1)]
  have hdemandSq := bankBottomPaperDemand_isBigO_yNat.trans hySq
  have hsum := bankOrdinaryPaperRequests_card_isBigO_yNat_sq.add
    (hdemandSq.const_mul_left (8 : ℝ))
  apply hsum.congr'
  · exact Eventually.of_forall fun n ↦ by
      simp only [bankPaperAnchorMarkerBudget, Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat]
  · exact Eventually.of_forall fun _n ↦ rfl

/-- The coarse all-marker budget itself is little-o of the central scale. -/
theorem bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale :
    (fun n : ℕ ↦ (bankPaperAnchorMarkerBudget n : ℝ)) =o[atTop]
      secondOrderScale := by
  have hyLittle :
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) =o[atTop]
        secondOrderScale := by
    apply (isLittleO_iff_tendsto' ?_).mpr
      yNat_sq_div_secondOrderScale_tendsto_zero
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hzero
    exact (hscale.ne' hzero).elim
  exact bankPaperAnchorMarkerBudget_isBigO_yNat_sq.trans_isLittleO hyLittle







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrecharge -/
section


/-!
# The actual precharged bank state

This module is independent of the eventual path selector.  Its component
index is the already realized global request type: every relevant bottom row
and every ordinary row occurs exactly once.  For each component we expose its
orientation-aware base and alternate states and its actual donor occurrence.

The proofs below use only the explicit component geometry.  In particular,
there is no abstract capacity or compatibility hypothesis: global
injectivity follows from the realized occurrence-set disjointness, and the
donor tail is the literal interval `(2n,M]`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section



namespace BankBottomPaperRealization

/-- Every actual bottom donor is in the strict tail above `2n`. -/
theorem two_mul_n_lt_donorFactor
    {n M : ℕ} (R : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    2 * n < R.donorFactor request := by
  have hrow := R.marker_mem_row hTwoN request
  cases hmove : R.move request <;>
    simp only [hmove, bankBottomMarkerInterval, bankBottomMarkerLower,
      bankBottomMarkerUpper, Finset.mem_Ioc, donorFactor,
      bankBottomDonor, bankBottomDonorMultiplier] at hrow ⊢ <;> omega

end BankBottomPaperRealization

namespace BankPaperRealization

attribute [local instance] Erdos390.WholePaper.BankPaperRealization.bankPaperMarkerRequestDecidableEq

/-! ## Global component data -/

























/-! ## Complete rough signatures -/







/-! ## Endpoint and donor injectivity -/





















/-! ## Literal finite states, donor tail, and replacement map -/

























/-- Every donor, ordinary or bottom, is an actual factor in `(2n,M]`. -/
theorem prechargeDonorValue_mem_tail
    {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ Finset.Ioc (2 * n) M := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      have hlower := R.bottom.two_mul_n_lt_donorFactor
        R.ordinary.two_mul_n_le_M fullRequest
      have hupper : R.bottom.donorFactor fullRequest ≤ M := by
        have hdata : n < R.bottom.donorFactor fullRequest ∧
            R.bottom.donorFactor fullRequest ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.bottom.states_donor_mem_factorInterval
              R.ordinary.two_mul_n_le_M fullRequest).2.2
        exact hdata.2
      simpa only [prechargeDonorValue, fullRequest,
        Finset.mem_Ioc] using And.intro hlower hupper
  | inr request =>
      have hlower := R.ordinary.two_mul_n_lt_donorValue request
      have hupper : R.ordinary.donorValue request ≤ M := by
        have hdata : n < R.ordinary.donorValue request ∧
            R.ordinary.donorValue request ≤ M := by
          simpa only [factorInterval, Finset.mem_Ioc] using
            (R.ordinary.donorValue_mem_factorInterval request)
        exact hdata.2
      simpa only [prechargeDonorValue, Finset.mem_Ioc] using
        And.intro hlower hupper

theorem prechargeDonorSet_subset_tail
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet ⊆ Finset.Ioc (2 * n) M := by
  intro donor hdonor
  rw [prechargeDonorSet, indexedPathState, Finset.mem_image] at hdonor
  obtain ⟨request, _hrequest, rfl⟩ := hdonor
  exact R.prechargeDonorValue_mem_tail request





















/-! ## Component counts and the base product -/























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalBacking -/
section


/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section







namespace BankPaperRealization





theorem paperFixedExceptionalFactors_subset_upperBlock
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆ roughUpperBlock n h := by
  intro a ha
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
  exact (mem_paperExceptionalUpperFactors.mp ha.1).1

/-- Every fixed exceptional factor is a literal upper-tail occurrence. -/
theorem paperFixedExceptionalFactors_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  simpa only [roughUpperBlock, upperEndpoint] using
    R.paperFixedExceptionalFactors_subset_upperBlock deltaStar



















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger -/
section


/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/



























/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





























/-! ## Exact local discrepancy ledger -/







/-! ## Exact support reduction for the local deletion set -/

/-- Fixed exceptional factors cannot themselves be raw lower candidates. -/
theorem roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (roughRawCandidateSet n h K)
      (R.paperFixedExceptionalFactors deltaStar) := by
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) (R.paperFixedExceptionalFactors_subset_upperBlock deltaStar)

/-- Actual donors also lie strictly above every raw lower candidate. -/
theorem roughRawCandidateSet_disjoint_prechargeDonorSet
    {n h K : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    Disjoint (roughRawCandidateSet n h K) R.prechargeDonorSet := by
  have hdonor : R.prechargeDonorSet ⊆ roughUpperBlock n h := by
    simpa only [roughUpperBlock, upperEndpoint] using
      R.prechargeDonorSet_subset_tail
  exact (roughUpperBlock_disjoint_rawCandidateSet n h K).symm.mono
    (by rfl) hdonor

/-- Consequently, the only guard families which can delete a raw lower
coordinate are anchors and the two bank endpoint states.  This is a support
statement, not the still-missing per-row cardinality census. -/
theorem roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : ℝ) (K label : ℕ) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
      certificate.anchors ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState := by
  intro a ha
  have haData := Finset.mem_inter.mp ha
  have haRaw := (mem_completeRoughRowFiber.mp haData.1).1
  have haGuard := haData.2
  simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
    Finset.mem_union] at haGuard
  simp only [Finset.mem_union]
  rcases haGuard with (((haAnchor | haFixed) | haDonor) | haBase) | haAlt
  · exact Or.inl (Or.inl haAnchor)
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_paperFixedExceptionalFactors
        deltaStar)) haRaw haFixed).elim
  · exact ((Finset.disjoint_left.mp
      (R.roughRawCandidateSet_disjoint_prechargeDonorSet
        (K := K))) haRaw haDonor).elim
  · exact Or.inl (Or.inr haBase)
  · exact Or.inr haAlt

/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction -/
section


/-!
# Canonical rough-row guard capacity reduction

This file closes the finite part of the three guard-local obligations exposed
by `BankPaperCanonicalGuardLocalRowLedger`.

For every non-smooth complete rough row, at most one central anchor, one bank
base, and one bank alternate can occur.  Thus the literal local guard census
is at most three.  Removing those three possible coordinates from a raw broad
pool gives the guarded-pool capacity, and containment of the guarded broad
pool in the guarded row gives the postcharge capacity.

The only non-finite input left visible is `RoughCanonicalActiveRawBroadSurplus`:
the raw broad pool must contain the larger of the requested pool minimum and
the literal upper-row target, plus the three-coordinate guard slack.  This is
the exact de Bruijn--Saias lower-bound consequence still needed from the
analytic rough-row argument; it contains no selector or bookkeeping premise.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete rough labels remember retained prime divisors -/

/-- A prime divisor above the smooth cutoff is retained in the complete
rough label. -/
theorem prime_dvd_completeRoughLabel_of_cutoff_lt
    {y a p : Nat} (hp : p.Prime) (hyp : y < p)
    (ha : a ≠ 0) (hpa : p ∣ a) :
    p ∣ completeRoughLabel y a := by
  apply (hp.dvd_iff_one_le_factorization
    (completeRoughLabel_ne_zero y a)).mpr
  rw [completeRoughLabel_factorization_apply, if_pos hyp]
  exact (hp.dvd_iff_one_le_factorization ha).mp hpa



/-! ## One central anchor in every non-smooth row -/





namespace BankPaperRealization

/-! ## One base and one alternate in every bank row -/

/-- The global bank marker is prime. -/
theorem paperMarker_prime
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    (R.marker request).Prime := by
  cases request with
  | inl request =>
      exact R.bottom.marker_prime
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.marker_prime request

/-- Every global bank marker lies above the complete rough cutoff. -/
theorem yNat_lt_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    yNat n < R.marker request := by
  cases request with
  | inl request =>
      exact R.bottom.yNat_lt_marker R.ordinary.two_mul_n_le_M
        R.three_mul_yNat_le_n
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.yNat_lt_marker request

/-- The actual donor has the same complete rough signature as its global
marker. -/
theorem prechargeDonor_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n) (R.prechargeDonorValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      simpa only [prechargeDonorValue, marker, fullRequest,
        BankBottomPaperRealization.occurrenceValue_donor] using
        (R.bottom.occurrenceValue_completeRoughSignature R.six_le_yNat
          fullRequest .donor)
  | inr request =>
      have hsignature := completeRoughSignature_marker_mul_smooth_eq
        (y := yNat n) (P := R.ordinary.marker request)
        (a := R.ordinary.donorCore request) (b := 1)
        (R.ordinary.marker_prime request).ne_zero
        (R.ordinary.donorCore_smooth request)
        (by simp [Nat.mem_smoothNumbers])
      simpa only [prechargeDonorValue, marker,
        BankOrdinaryPaperRealization.donorValue, mul_one] using hsignature

theorem prechargeBase_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.prechargeBase_donor_completeRoughSignature_eq request).trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

theorem prechargeAlternate_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.precharge_completeRoughSignature_eq request).2.trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

/-- A prime above the cutoff is its own complete rough label. -/
theorem completeRoughLabel_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.marker request) = R.marker request := by
  have hprime := R.paperMarker_prime request
  have hhigh := R.yNat_lt_paperMarker request
  apply Nat.dvd_antisymm
  · exact completeRoughLabel_dvd (yNat n) (R.marker request)
  · exact prime_dvd_completeRoughLabel_of_cutoff_lt hprime hhigh
      hprime.ne_zero (dvd_refl (R.marker request))

theorem prechargeBase_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      R.marker request := by
  calc
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeBase_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeAlternate_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) = R.marker request := by
  calc
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeAlternate_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request











/-! ## The literal three-coordinate local census -/





/-! ## Guarded broad-pool and postcharge capacities -/







/-! ## The single remaining analytic raw-pool input -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/



/-- The fixed Dickman floor is strictly positive. -/
theorem roughCanonicalPoolDickmanFloor_pos :
    0 < roughCanonicalPoolDickmanFloor := by
  unfold roughCanonicalPoolDickmanFloor
  exact rho_pos_on_zero_five (by norm_num) le_rfl



/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/



/-- The retained raw broad-pool density is strictly positive. -/
theorem roughCanonicalRawBroadPoolDensity_pos (W : Nat) :
    0 < roughCanonicalRawBroadPoolDensity W := by
  unfold roughCanonicalRawBroadPoolDensity
  exact div_pos
    (mul_pos (roughHeadDensity_pos W)
      roughCanonicalPoolDickmanFloor_pos) (by norm_num)









/-! ## Uniform paper-scale choices -/























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankAnchorCollisionFree -/
section


/-!
# Collision freedom between the complete central anchors and the actual bank

The large-anchor branch recovers the common prime marker from the complete
rough factorization above `yNat`.  Once the marker is recovered, the guarded
central-cofactor certificate excludes the two incident state cores.

The residual branch uses the more rigid shape
`2^k * p^e`.  A bottom marker is already above the residual cutoff.  For an
ordinary marker, divisibility first forces the residual base prime to be the
marker; its marker valuation is then one, so cancellation would make the
ordinary state core a power of two, contrary to the path certificate.

Donor-only occurrences do not create an extra case: ordinary donors and the
two nonterminal bottom donors lie above `2n`, while terminal bottom donors
are literally their upper endpoint state.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The two eventual scale separations used by marker recovery -/

/-- The elementary square bound behind the separation
`yNat n < centralAnchorCutoff depth n`. -/
theorem bankAnchor_yNat_mul_self_le_self
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast





/-- At the literal central-anchor threshold, the moving smooth cutoff is
strictly below the residual/large-prime cutoff. -/
theorem yNat_lt_centralAnchorCutoff_of_threshold
    {depth n : ℕ} (hn : 1 ≤ n)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    yNat n < centralAnchorCutoff depth n := by
  have hySq := bankAnchor_yNat_mul_self_le_self hn
  have hcutSq := two_mul_lt_centralAnchorCutoff_sq hnCutoff
  nlinarith

theorem eventually_yNat_lt_centralAnchorCutoff (depth : ℕ) :
    ∀ᶠ n : ℕ in atTop, yNat n < centralAnchorCutoff depth n := by
  filter_upwards [eventually_ge_atTop 1,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth)]
      with n hn hnCutoff
  exact yNat_lt_centralAnchorCutoff_of_threshold hn hnCutoff

/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardedBridgeConnector -/
section


/-!
# Canonical guarded selector to bridge-fit connector

This module joins the finite objects on the two sides of the Section 8/9
interface without asserting the missing selector theorem.

* `bankPaperCanonicalBridgeData` builds the literal `PaperBridgeFit.BridgeData`
  from an existing guarded structured sample, the canonical barycentric
  baseline, and the canonical regular-mesh partition.
* `BankPaperCanonicalGuardedBridgeSelectorConstructor` is the sole
  existential socket.  Its witness is an actual guarded selector satisfying
  the already defined rounded-selector tangent input and agreeing with the
  bridge baseline on the active structured sample.
* the projection and frozen-layer theorems derive the smooth integer quota,
  feasibility, row integrality, prime-band balance and support, tangent
  balance and pointwise/prefix bounds, the frozen feasibility ledger, and the
  total integer quota.  No one of those conclusions is repeated as a new
  premise.

The active structured sample need only be a subset of the guarded smooth row;
it is not silently identified with the whole row.  All other guarded
coordinates are retained in the frozen layer with their selector weights,
while the fixed exceptional factors have weight one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open BankPaperRealization

noncomputable section

/-! ## Canonical bridge data -/















/-! ## Active values and integer row quotas -/



theorem mem_bankPaperCanonicalBridgeActiveValues
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData Head Band} {a : Nat} :
    a ∈ bankPaperCanonicalBridgeActiveValues B ↔
      ∃ m : B.sampleData.Sample, B.sampleData.value m = a := by
  simp [bankPaperCanonicalBridgeActiveValues]





/-! ## The sole missing constructor and all tangent projections -/





/-! ## Guarded smooth support -/

/-- A structured sample lying in `(n,2n]` whose values avoid the literal
numerical guards is a subset of the guarded smooth row. -/
theorem bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalBridgeActiveValues B ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  intro a ha
  obtain ⟨m, hvalue⟩ :=
    mem_bankPaperCanonicalBridgeActiveValues.mp ha
  subst a
  apply mem_completeRoughRowFiber.mpr
  constructor
  · rw [BankPaperRealization.roughCanonicalGuardedCandidateSet,
      Finset.mem_sdiff, roughRawCandidateSet_eq_Ioc hKh]
    exact ⟨Finset.mem_Ioc.mpr ⟨hlower m, hupper m⟩,
      hnotGuard m⟩
  · exact (completeRoughLabel_eq_one_iff_mem_smoothNumbers
      (B.sampleData.value_pos m)).mpr
        (B.sampleData.value_mem_smoothNumbers m)







/-! ## Frozen layer and quota -/























/-! ## Baseline slack and ambient feasibility -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalHeadActiveMassEventually -/
section


/-!
# Eventual lower bound for the paper's head-reserve active mass

The paper obtains its final active mass from the exact ledger

`q^{act}(d) = q₀ - d`,

where the rough smooth active mass satisfies `q₀ ≍ n / log n` and the
height-centering change satisfies `d = O(n / log² n)`.  Only the lower
half of that comparison is needed to prove the constructor hypothesis
`1 <= q^{act}(d)` for all sufficiently large `n`.

The repository's `HeadSimplexReserve` currently stores only
`0 < activeMass`.  It has no family constructor, no connection to the
rough smooth active mass, and no asymptotic lower-bound field.  This file
therefore isolates the exact missing paper input as a positive lower
multiple of `secondOrderScale n = n / log n`.  Everything after that input
is proved here:

* the active mass tends to infinity and eventually exceeds every constant;
* in particular it is eventually at least one;
* an `o(n / log n)` height change preserves a fixed positive lower multiple;
* the paper's stronger `O(n / log² n)` change is automatically little-o;
* the canonical scaled seed has eventual mass at least one and its
  self-selector satisfies the full actual-active-measure constructor.

A concrete reserve of mass `1 / 2` is also constructed.  It proves that
strict positivity alone cannot imply the desired inequality, so the
repository needs an additional growth input until the missing
rough-active-mass construction is connected to `HeadSimplexReserve`.
The predicate below is exactly the lower half of the growth statement
used in the paper.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

/-! ## The irreducible paper-scale input -/





/-! ## Positivity is genuinely insufficient -/









/-! ## All eventual consequences of the minimal input -/

/-- A fixed positive multiple of `n / log n` tends to infinity, hence so
does any active mass lying eventually above it. -/
theorem bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    Tendsto q atTop atTop := by
  rcases H with ⟨c, hc, hq⟩
  have hscale : Tendsto
      (fun n : Nat => c * secondOrderScale n) atTop atTop :=
    secondOrderScale_tendsto_atTop.const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ hscale
  exact hq

/-- Every fixed real threshold is eventually below the active mass. -/
theorem eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) (C : Real) :
    ∀ᶠ n : Nat in atTop, C <= q n :=
  (bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower q H).eventually
    (eventually_ge_atTop C)

/-- The exact constructor threshold follows with `C = 1`. -/
theorem eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    ∀ᶠ n : Nat in atTop, 1 <= q n :=
  eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    q H 1





/-! ## The exact `q₀-d` height-centering algebra -/



/-- Subtracting a little-o height-centering change from a macroscopically
positive base mass preserves half of its lower constant. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =o[atTop] secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  rcases Hq0 with ⟨c, hc, hq0⟩
  refine ⟨c / 2, half_pos hc, ?_⟩
  have hdBound := hd.bound (half_pos hc)
  filter_upwards [hq0, hdBound, eventually_secondOrderScale_pos]
      with n hq0n hdn hscale
  have hdn' : |d n| <= (c / 2) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscale] using hdn
  have hdle : d n <= (c / 2) * secondOrderScale n :=
    (le_abs_self (d n)).trans hdn'
  calc
    (c / 2) * secondOrderScale n =
        c * secondOrderScale n -
          (c / 2) * secondOrderScale n := by ring
    _ <= q0 n - (c / 2) * secondOrderScale n :=
      sub_le_sub_right hq0n _
    _ <= q0 n - d n := sub_le_sub_left hdle _







/-! ## Literal scaled seeds and actual-measure constructors -/







/-! ## The literal paper-head specialization -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic -/
section


/-!
# The analytic Section 8 smooth-row quota and height bridge

The raw active smooth component from the exact companion file has a positive
`n / log n` lower bound by the repository's uniform de Bruijn--Saias and
fixed-head estimates.  This file proves that bound directly for complete-
rough label one, then propagates it through the exact nearest-integer and
height-center constructions.

Only one repository-level analytic ledger remains absent.  It is named
`BankPaperCanonicalSectionEightAnalyticLedger` below and contains exactly:

* the actual post-guard smooth mass differs from the explicit raw base mass
  by `o(n / log n)`;
* the literal frozen height defect `A0` is `O(n / log n)`.

These are precisely the two estimates asserted together in the paper's
Section 8 frozen ledger.  No selector, active-measure, or positivity premise
is hidden in that predicate.  Every consequence after it, including
`d = O(n / log^2 n)` and the positive lower bound for `q0 - d`, is proved
here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The label-one raw base pool is macroscopically large -/







/-- Therefore the literal `betaAct / L` base component has the minimal
positive paper-scale lower bound whenever `betaAct > 0`. -/
theorem bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c) (hbeta : 0 < betaAct) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct) := by
  use betaAct * roughCanonicalRawBroadPoolDensity W,
    mul_pos hbeta (roughCanonicalRawBroadPoolDensity_pos W)
  have hpool :=
    eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower W K hc
  filter_upwards [hpool, eventually_gt_atTop 1] with n hpoolN hn
  have hL : 0 < L n := L_pos hn
  calc
    (betaAct * roughCanonicalRawBroadPoolDensity W) * secondOrderScale n =
        (betaAct / L n) *
          (roughCanonicalRawBroadPoolDensity W * (n : Real)) := by
      unfold secondOrderScale L
      ring
    _ <= (betaAct / L n) *
          ((bankPaperCanonicalRawSmoothBasePool W n
            (upperTailLength c n) K).card : Real) :=
      mul_le_mul_of_nonneg_left hpoolN (div_nonneg hbeta.le hL.le)
    _ = bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) K betaAct := by
      rfl



/-! ## The exact missing analytic ledger -/



/-! ## Nearest-integer initialization preserves the paper scale -/



/-- A negligible raw-to-post-guard loss transfers the positive lower bound
from the explicit raw base mass to the actual mass `qTilde`. -/
theorem bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (rawBase qTilde : Nat -> Real)
    (Hraw : BankPaperCanonicalActiveMassPaperScaleLower rawBase)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower qTilde := by
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      rawBase (fun n => rawBase n - qTilde n) Hraw Hguard with
    ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring







/-! ## The logarithmically smaller height adjustment -/







/-! ## Full propagation from the minimal missing ledger -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction -/
section


/-!
# Reduction of the remaining Section 8 analytic ledger

The analytic quota/height bridge deliberately leaves two estimates in
`BankPaperCanonicalSectionEightAnalyticLedger`.  This file separates all
finite and asymptotic algebra around those estimates from the genuinely
missing paper inputs.

For the active mass, the literal intermediate object is the constant
`betaAct / L` layer on the guarded label-one broad pool.  Its difference
from the raw layer is exactly the same constant times the number of deleted
coordinates.  The natural smooth-guard census envelope

`yNat^2 + bankPaperAnchorMarkerBudget`

is already `o(secondOrderScale)`.  Thus only a census bound for the literal
deleted pool and the post-correction identification with the actual
`qTilde` remain.

For the height, the paper first proves the three baseline relations

* `m0 + qTilde = h + O(N/L)`,
* `Lambda0 = m0 L + O(N)`,
* `logY = h L + O(N)`.

Nearest-integer initialization transfers the first relation from `qTilde`
to `q0`; the displayed identity for `A0` then proves `A0 = O(N)`.  Hence the
height half of the old black-box ledger is reduced exactly to those three
named source estimates.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal guarded smooth base -/





/-- Fixed exceptional factors and donors are in the upper tail, while every
precharged base or alternate state has a nontrivial marker label.  Therefore
only central anchors can delete a coordinate from the label-one raw pool. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchors
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
        deltaStar W K ⊆ certificate.anchors := by
  classical
  intro a ha
  have haData := Finset.mem_inter.mp ha
  have haRawRow : a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n h K) 1 :=
    roughCanonicalBroadCorrectionPool_subset_rawRow
      W n h K (yNat n) 1 haData.2
  have haDeleted : a ∈
      R.roughCanonicalGuardDeletedRow certificate deltaStar K 1 :=
    Finset.mem_inter.mpr ⟨haRawRow, haData.1⟩
  have haSupport :=
    R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
      certificate deltaStar K 1 haDeleted
  rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
  · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
    · exact haAnchor
    · rw [BankPaperRealization.prechargeBaseState, indexedPathState,
        Finset.mem_image] at haBase
      obtain ⟨request, _hrequest, rfl⟩ := haBase
      have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
      rw [R.prechargeBase_completeRoughLabel_eq_marker] at hlabel
      have hhigh := R.yNat_lt_paperMarker request
      have hy := R.six_le_yNat
      omega
  · rw [BankPaperRealization.prechargeAlternateState, indexedPathState,
      Finset.mem_image] at haAlternate
    obtain ⟨request, _hrequest, rfl⟩ := haAlternate
    have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
    rw [R.prechargeAlternate_completeRoughLabel_eq_marker] at hlabel
    have hhigh := R.yNat_lt_paperMarker request
    have hy := R.six_le_yNat
    omega



/-- Retaining the original raw-pool membership sharpens the preceding
support theorem to the exact smooth-anchor intersection. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchorIntersection
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
        deltaStar W K ⊆
      certificate.anchors ∩
        bankPaperCanonicalRawSmoothBasePool W n h K := by
  intro a ha
  exact Finset.mem_inter.mpr
    ⟨bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchors
        R certificate deltaStar W K ha,
      (Finset.mem_inter.mp ha).2⟩

/-- Hence the missing guard count involves only central anchors which
actually lie in the raw head-free smooth base pool. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    (bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
      deltaStar W K).card <=
        (certificate.anchors ∩
          bankPaperCanonicalRawSmoothBasePool W n h K).card :=
  Finset.card_le_card
    (bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchorIntersection
      R certificate deltaStar W K)

/-! ### The smooth central-anchor census -/



/-- Every guarded central anchor in the raw label-one base pool is a promoted
residual anchor whose base prime is at most `yNat`.  Routed large anchors
retain their marker prime in the complete rough label and hence cannot occur
in this row. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_subset_smoothResidual
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (W K : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    certificate.anchors ∩ bankPaperCanonicalRawSmoothBasePool W n h K ⊆
      bankPaperCanonicalSmoothResidualAnchorPool n
        (centralAnchorCutoff depth n) (yNat n) := by
  intro a ha
  have hn : 0 < n :=
    (centralAnchorCutoffThreshold_pos depth).trans_le hnCutoff
  have haRawRow : a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n h K) 1 :=
    roughCanonicalBroadCorrectionPool_subset_rawRow
      W n h K (yNat n) 1 (Finset.mem_inter.mp ha).2
  have haLabel : completeRoughLabel (yNat n) a = 1 :=
    (mem_completeRoughRowFiber.mp haRawRow).2
  have haAnchor : a ∈ fullCentralAnchors n
      (centralAnchorCutoff depth n) certificate.q := by
    simpa only [certificate.anchors_eq] using (Finset.mem_inter.mp ha).1
  rw [fullCentralAnchors] at haAnchor
  rcases Finset.mem_union.mp haAnchor with haPromoted | haLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haPromoted
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    by_contra hpNotLe
    have hyp : yNat n < p := Nat.lt_of_not_ge hpNotLe
    have hpPrime := residualCentralPrimes_prime hp
    have hpDvdFactor : p ∣ promotedCentralFactor n p := by
      unfold promotedCentralFactor promotedBlock centralPrimeBlock
      exact dvd_mul_of_dvd_right
        (dvd_pow_self p (residualCentralPrimes_exponent_pos hp).ne') _
    have hpDvdLabel : p ∣
        completeRoughLabel (yNat n) (promotedCentralFactor n p) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hyp
        (Nat.zero_lt_of_lt (promotedCentralFactor_gt hn)).ne'
        hpDvdFactor
    rw [haLabel] at hpDvdLabel
    exact hpPrime.not_dvd_one hpDvdLabel
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hP
    have hPHigh : yNat n < P :=
      hyCutoff.trans (largeCentralPrimes_gt hP)
    have hPPos : 0 < largeCentralAnchor certificate.q P :=
      Nat.zero_lt_of_lt
        (Finset.mem_Ioc.mp
          (largeCentralAnchor_mem_centralInterval
            certificate.isCofactorChoice hP)).1
    have hPDvdLabel : P ∣
        completeRoughLabel (yNat n)
          (largeCentralAnchor certificate.q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        hPPos.ne' (dvd_mul_right P (certificate.q P))
    rw [haLabel] at hPDvdLabel
    exact (hPPrime.not_dvd_one hPDvdLabel).elim



/-- Pointwise paper-sized bound for the relevant smooth guarded anchors. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (W K : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    (certificate.anchors ∩
      bankPaperCanonicalRawSmoothBasePool W n h K).card <= yNat n :=
  (Finset.card_le_card
    (guardedCentralAnchors_inter_rawSmoothBasePool_subset_smoothResidual
      certificate W K hnCutoff hyCutoff)).trans
    (bankPaperCanonicalSmoothResidualAnchorPool_card_le n
      (centralAnchorCutoff depth n) (yNat n))

/-- Deleting the numerical guards changes the raw active base mass by
exactly `betaAct / L` times the literal deletion cardinality. -/
theorem bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real) :
    bankPaperCanonicalRawSmoothBaseMass W n h K betaAct -
        bankPaperCanonicalGuardedSmoothBaseMass R certificate
          deltaStar W K betaAct =
      betaAct / L n *
        ((bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
          deltaStar W K).card : Real) := by
  let rawPool : Finset Nat :=
    bankPaperCanonicalRawSmoothBasePool W n h K
  let guardSet : Finset Nat :=
    R.roughCanonicalGuardSet certificate deltaStar
  change
    betaAct / L n * (rawPool.card : Real) -
        betaAct / L n * ((rawPool \ guardSet).card : Real) =
      betaAct / L n * ((guardSet ∩ rawPool).card : Real)
  have hcard :
      (guardSet ∩ rawPool).card <= rawPool.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hcardDiff :
      ((rawPool \ guardSet).card : Real) =
        (rawPool.card : Real) - ((guardSet ∩ rawPool).card : Real) := by
    rw [Finset.card_sdiff, Nat.cast_sub hcard]
  rw [hcardDiff, mul_sub]
  ring

/-! ## Honest tail families and their total asymptotic extensions -/















/-! ## The already-small guard census envelope -/



/-- The census envelope is pointwise nonnegative. -/
theorem bankPaperCanonicalSmoothGuardCensusEnvelope_nonneg (n : Nat) :
    0 <= bankPaperCanonicalSmoothGuardCensusEnvelope n := by
  unfold bankPaperCanonicalSmoothGuardCensusEnvelope
  positivity

/-- The moving square cutoff is little-o of the central paper scale. -/
theorem bankPaperCanonical_yNat_sq_isLittleO_secondOrderScale :
    (fun n : Nat => (yNat n : Real) ^ 2) =o[atTop]
      secondOrderScale := by
  have hzero : ∀ᶠ n : Nat in atTop,
      secondOrderScale n = 0 -> (yNat n : Real) ^ 2 = 0 := by
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hzero
    exact (hscale.ne' hzero).elim
  apply (isLittleO_iff_tendsto' hzero).mpr
  exact yNat_sq_div_secondOrderScale_tendsto_zero

/-- Consequently the complete smooth-guard census envelope is negligible. -/
theorem bankPaperCanonicalSmoothGuardCensusEnvelope_isLittleO :
    bankPaperCanonicalSmoothGuardCensusEnvelope =o[atTop]
      secondOrderScale := by
  have hsum := bankPaperCanonical_yNat_sq_isLittleO_secondOrderScale.add
    bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale
  exact hsum.congr_left fun n => by
    rfl

/-- Uniformly over every honest tail family of guarded certificates, the
total relevant-anchor extension is `O` of the census envelope.  This closes
the finite guard-deletion census with no new analytic input and no
realization request on the finite prefix. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_isBigO_envelope
    {c : Real} {N : Nat} (depth W K : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    F.extendedAnchorIntersectionCard W K =O[atTop]
      bankPaperCanonicalSmoothGuardCensusEnvelope := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop
      (centralAnchorCutoffThreshold depth),
    eventually_yNat_lt_centralAnchorCutoff depth,
    eventually_bankBottom_six_le_yNat] with
      n hnTail hnCutoff hyCutoff hySix
  rw [BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard,
    dif_pos hnTail, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs,
    abs_of_nonneg (bankPaperCanonicalSmoothGuardCensusEnvelope_nonneg n),
    one_mul]
  have hcard :
      (((BankPaperCanonicalGuardedTailFamily.certificate
          F n hnTail).anchors ∩
        bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) <= (yNat n : Real) := by
    exact_mod_cast
      guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
        (BankPaperCanonicalGuardedTailFamily.certificate F n hnTail)
          W K hnCutoff hyCutoff
  have hyOne : (1 : Real) <= yNat n := by
    exact_mod_cast (show 1 <= yNat n by omega)
  have hyNonneg : (0 : Real) <= yNat n := by positivity
  have hySq : (yNat n : Real) <= (yNat n : Real) ^ 2 := by
    calc
      (yNat n : Real) = (yNat n : Real) * 1 := by ring
      _ <= (yNat n : Real) * (yNat n : Real) :=
        mul_le_mul_of_nonneg_left hyOne hyNonneg
      _ = (yNat n : Real) ^ 2 := by ring
  exact hcard.trans <| hySq.trans <|
    le_add_of_nonneg_right (by positivity)



/-- Every family satisfying the named finite census is automatically
little-o of the paper scale. -/
theorem bankPaperCanonicalSmoothGuardDeletionCard_isLittleO
    (deletedCard : Nat -> Real)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    deletedCard =o[atTop] secondOrderScale :=
  Hcensus.trans_isLittleO
    bankPaperCanonicalSmoothGuardCensusEnvelope_isLittleO

/-- For fixed `betaAct`, the coefficient `betaAct / L` is uniformly
bounded. -/
theorem bankPaperCanonical_beta_div_L_isBigO_one (betaAct : Real) :
    (fun n : Nat => betaAct / L n) =O[atTop]
      (fun _n : Nat => (1 : Real)) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLone : ∀ᶠ n : Nat in atTop, 1 <= L n :=
    hLTop.eventually (eventually_ge_atTop (1 : Real))
  apply IsBigO.of_bound ‖betaAct‖
  filter_upwards [hLone] with n hn
  have hnormL : 1 <= ‖L n‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hn)]
    exact hn
  rw [norm_div, norm_one, mul_one]
  exact div_le_self (norm_nonneg betaAct) hnormL

/-- A census-sized family of deleted coordinates has negligible weighted
mass under the literal `betaAct / L` base layer. -/
theorem bankPaperCanonicalSmoothGuardDeletionMass_isLittleO
    (betaAct : Real) (deletedCard : Nat -> Real)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    (fun n => betaAct / L n * deletedCard n) =o[atTop]
      secondOrderScale := by
  have hweighted :=
    (bankPaperCanonical_beta_div_L_isBigO_one betaAct).mul_isLittleO
      (bankPaperCanonicalSmoothGuardDeletionCard_isLittleO
        deletedCard Hcensus)
  simpa only [one_mul] using hweighted



/-- Exact identities plus the finite deletion census transfer the raw base
to the explicit guarded base at little-o cost. -/
theorem bankPaperCanonicalRawSmoothBase_sub_guarded_isLittleO_of_census
    (betaAct : Real) (rawBase guardedBase deletedCard : Nat -> Real)
    (hidentity : forall n,
      rawBase n - guardedBase n =
        betaAct / L n * deletedCard n)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    (fun n => rawBase n - guardedBase n) =o[atTop]
      secondOrderScale := by
  exact (bankPaperCanonicalSmoothGuardDeletionMass_isLittleO
    betaAct deletedCard Hcensus).congr_left fun n =>
      (hidentity n).symm



/-! ## Reduction of the frozen height defect -/











/-! ## The complete reduced source ledger -/











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureAdditiveRefinement -/
section


/-!
# Actual active measure carried by the protected additive refinement

The canonical scaled active seed has exact literal mass `q`.  The protected
additive refinement places its ambient push-forward below the pre-selector
by construction: on every active coordinate it is the active weight plus
the nonnegative protected constant `betaProt / L`.

This file joins those two independent facts.  It proves the minimized
coordinate-fit predicate, candidate nonnegativity, and hence the full
actual-active-measure constructor on the literal guarded candidate set.
The first connector below records the older, stronger hypothesis that all
structured active values lie in the guarded *broad* correction pool.  That
hypothesis is false for the nonzero paper head vertices: the correction pool
is head-free.  The second half of the file therefore gives the literal
paper-faithful placement.  It extends the protected refinement only on the
finite structured active image, which already lies in the guarded smooth
row, and leaves the old refinement unchanged on its whole correction pool.
Its exact capacity predicate is discharged either pointwise or from the
existing cell-density/base-weight bound.

No rounded-selector transport is asserted here.  Replacing a smooth row
can change its integer row sum and prime moments; those equalities are the
separate additive-ledger boundary recorded by the refinement module.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Pointwise fit and feasibility -/





/-! ## Full guarded actual-measure constructor -/



/-! ## Structured placement on the whole guarded smooth row

The broad correction pool is the head-free part of the smooth row, whereas
the structured sample contains the nonzero paper head vertices as well.  The
following selector therefore keeps the protected refinement on its original
pool and, at every remaining structured active value, installs precisely the
active seed (the protected layer is zero there). -/

/-- Fixed physical endpoints in `[1,2]` put every structured value in the
literal interval `(n,2n]`. -/
theorem bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n) :
    (forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m) ∧
      forall m : B.sampleData.Sample,
        B.sampleData.value m <= 2 * B.sampleData.n := by
  constructor
  · intro m
    have hnlo : B.sampleData.n <=
        B.sampleData.lo (B.sampleData.cellOf m).2 := by
      rw [hlo]
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : Real) <=
        I.lower (B.sampleData.cellOf m).2 *
          (B.sampleData.n : Real) by
        nlinarith [show (0 : Real) <= (B.sampleData.n : Real) by
          positivity,
          hlowerOne (B.sampleData.cellOf m).2])
    exact hnlo.trans_lt (B.sampleData.lo_lt_value m)
  · intro m
    let sigma := (B.sampleData.cellOf m).2
    have hvalue : B.sampleData.value m <=
        physicalBound (I.upper sigma) B.sampleData.n := by
      simpa only [sigma, hhi] using B.sampleData.value_le_hi m
    have hupperPos : 0 < I.upper sigma :=
      (I.lower_pos sigma).trans (I.lower_lt_upper sigma)
    have hfloor :
        (physicalBound (I.upper sigma) B.sampleData.n : Real) <=
          I.upper sigma * (B.sampleData.n : Real) := by
      unfold physicalBound
      exact Nat.floor_le
        (mul_nonneg hupperPos.le (by positivity))
    have htwo : I.upper sigma * (B.sampleData.n : Real) <=
        2 * (B.sampleData.n : Real) :=
      mul_le_mul_of_nonneg_right (hupperTwo sigma) (by positivity)
    have hbound : physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n := by
      have hcast := hfloor.trans htwo
      exact_mod_cast hcast
    exact hvalue.trans hbound

/-- Physical fixed-partition endpoints, pointwise rough-guard avoidance, and the rough tail
inequality place every structured head cell in the guarded smooth row. -/
theorem bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  have hbounds := bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    B I hlowerOne hupperTwo hlo hhi
  intro a ha
  apply bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
    B R certificate deltaStar hKh hbounds.1 hbounds.2 hnotGuard
  exact mem_bankPaperCanonicalBridgeActiveValues.mpr
    (mem_bankPaperCanonicalStructuredActiveValues.mp ha)



















/-! ## Exact frozen remainder of the corrected placement -/











/-! ## Exact coordinate capacity and selector feasibility -/









/-! ## Full guarded constructor with the corrected placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector -/
section


/-!
# Concrete producer and mass choice for the two zero-head cells

This file isolates the two finite facts needed by the structured
prebridge producer.

First, a sample in the zero head cell is coprime to the complete head
modulus.  Hence it belongs to the guarded broad correction pool as soon as
its physical interval lies below the literal broad cutoff and every sample
value is known pointwise to avoid the canonical guard set.  In particular, no
cardinality surplus theorem is used to prove membership.

Second, the height adjustment has a canonical symmetric realization: put
`-d / 2` in each of the two physical zero-head cells.  Its total change is
the integer `-d`, and the exact lower and upper coordinate-capacity
conditions reduce to two scalar inequalities involving the old total cell
mass and the guard-deleted cell cardinality.

The nearest-integer normalization from `qTilde` to `q0` is recorded
separately.  That first change is generally real rather than integral; the
integer prebridge ledger applies to the subsequent height change from
`q0` to `q0 - d`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums

noncomputable section

namespace BankPaperRealization

/-! ## The fixed physical intervals eventually lie below the broad cutoff -/

/-- A fixed endpoint strictly below `2` eventually leaves enough room for
the whole `K * upperTailLength` top strip.  This is the literal numerical
inequality used in the paper to put the upper physical pool below
`2n-Kh`. -/
theorem eventually_physicalBound_le_two_mul_sub_upperTailLength
    (K : Nat) {c b : Real} (hc : 0 < c) (hb0 : 0 <= b) (hbTwo : b < 2) :
    ∀ᶠ n : Nat in atTop,
      physicalBound b n <= 2 * n - K * upperTailLength c n := by
  have htailEvent : ∀ᶠ n : Nat in atTop,
      (((K * upperTailLength c n : Nat) : Real) / (n : Real)) < 2 - b := by
    have hT := (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
    have hzeroLt : (K : Real) * 0 < 2 - b := by
      simpa using sub_pos.mpr hbTwo
    have hsmall := hT.eventually
      (eventually_lt_nhds hzeroLt)
    filter_upwards [hsmall] with n hn
    have hn' :
        (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) < 2 - b := hn
    simpa [Nat.cast_mul, mul_div_assoc] using hn'
  filter_upwards [htailEvent, eventually_gt_atTop 0] with n htail hn
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have htailCross :
      ((K * upperTailLength c n : Nat) : Real) <
        (2 - b) * (n : Real) :=
    (div_lt_iff₀ hnReal).mp htail
  have hfloor :
      (physicalBound b n : Real) <= b * (n : Real) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hb0 (by positivity))
  have hsumReal :
      (physicalBound b n : Real) +
          (K * upperTailLength c n : Nat) < 2 * (n : Real) := by
    calc
      (physicalBound b n : Real) +
          (K * upperTailLength c n : Nat) <=
        b * (n : Real) + (K * upperTailLength c n : Nat) :=
          add_le_add hfloor le_rfl
      _ < 2 * (n : Real) := by nlinarith
  have hsumNat :
      physicalBound b n + K * upperTailLength c n <= 2 * n := by
    exact_mod_cast hsumReal.le
  omega

/-- Simultaneous two-sign form for the paper's fixed physical intervals. -/
theorem eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
    (I : PhysicalIntervals) (K : Nat) {c : Real} (hc : 0 < c)
    (hupperStrict : forall sigma, I.upper sigma < 2) :
    ∀ᶠ n : Nat in atTop, forall sigma,
      physicalBound (I.upper sigma) n <=
        2 * n - K * upperTailLength c n := by
  have hminus :=
    eventually_physicalBound_le_two_mul_sub_upperTailLength K hc
      (le_of_lt ((I.lower_pos .minus).trans (I.lower_lt_upper .minus)))
      (hupperStrict .minus)
  have hplus :=
    eventually_physicalBound_le_two_mul_sub_upperTailLength K hc
      (le_of_lt ((I.lower_pos .plus).trans (I.lower_lt_upper .plus)))
      (hupperStrict .plus)
  filter_upwards [hminus, hplus] with n hnMinus hnPlus
  intro sigma
  cases sigma with
  | minus => exact hnMinus
  | plus => exact hnPlus

/-! ## The zero head pattern produces head-freeness -/









/-! ## Canonical symmetric mass choices -/















/-! ## Exact finite coordinate capacity -/















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalBridgeRelevantGuardLedger -/
section


/-!
# The bridge-relevant numerical-guard ledger

The literal rough construction uses the global five-family guard

`anchors ∪ fixedExceptional ∪ donors ∪ baseState ∪ alternateState`.

That global set is not the guard census used by the smooth bridge.  Fixed
exceptional factors and donors lie above `2n`, while the two bank endpoint
states have a prime complete-rough label above `yNat n`.  Hence, on the
positive `yNat n`-smooth values at most `2n` which occur in every bridge
cell, the global guard agrees exactly with the promoted residual anchors
whose base prime is at most `yNat n`.

This file makes that relevant guard literal.  Its cardinality is at most
`yNat n`, so it fits in the promoted part of `GuardSlot`.  We adjoin the
harmless sentinel value `0` before enumerating it.  This avoids a false
nonemptiness requirement on an image of a nonempty slot type; the sentinel
cannot occur in a structured cell.  Two promoted slots per smooth integer
therefore suffice uniformly, and no bank slot is required.

Thus the correct replacement for a global
`ledger.guards = roughCanonicalGuardSet` hypothesis is the eventual local
predicate `BankPaperCanonicalBridgeGuardAgreement`.  A total fixed ledger
family, chosen before any realization or certificate, uses a harmless
zero-valued fallback on the finite prefix where the relevant guard does not
fit.  Once a realization exists the paper census forces the canonical branch,
so this fixed family agrees with the global rough guard on the bridge
universe.  The concrete elimination interfaces below give equality after
deleting guards from a raw cell, equality after restricting deletion to
structured active values, and pointwise avoidance of the full guard.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Enumerating an arbitrary finite guard together with a zero sentinel -/





/-- The padded enumeration has exactly the requested guard together with
the sentinel; no other integer is introduced. -/
theorem ledgerOfFinsetWithZero_guards
    {n Cprom Cbank : Nat} (guards : Finset Nat)
    (hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n Cprom Cbank)) :
    (ledgerOfFinsetWithZero guards hcard).guards = insert 0 guards := by
  classical
  let e : (insert 0 guards : Finset Nat) ↪
      GuardSlot n Cprom Cbank :=
    guardFinsetWithZeroEmbedding guards hcard
  change Finset.univ.image
      (Function.extend e
        (fun a : (insert 0 guards : Finset Nat) => a.1)
        (fun _ => 0)) =
    insert 0 guards
  ext a
  constructor
  · intro ha
    rw [Finset.mem_image] at ha
    obtain ⟨slot, _hslot, rfl⟩ := ha
    by_cases hslot : ∃ x, e x = slot
    · rw [Function.extend_def, dif_pos hslot]
      exact (Classical.choose hslot).property
    · rw [Function.extend_apply'
        (g := fun x : (insert 0 guards : Finset Nat) => x.1)
        (e' := fun _ : GuardSlot n Cprom Cbank => 0)
        slot hslot]
      exact Finset.mem_insert_self 0 guards
  · intro ha
    rw [Finset.mem_image]
    refine ⟨e ⟨a, ha⟩, Finset.mem_univ _, ?_⟩
    simpa only using
      e.injective.extend_apply
        (fun x : (insert 0 guards : Finset Nat) => x.1)
        (fun _ : GuardSlot n Cprom Cbank => 0)
        ⟨a, ha⟩

/-! ## The literal bridge-relevant subfamily -/





/-- Every relevant promoted anchor belongs to the certificate's full anchor
set. -/
theorem roughCanonicalBridgeRelevantGuardSet_subset_anchors
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    roughCanonicalBridgeRelevantGuardSet certificate ⊆
      certificate.anchors := by
  intro a ha
  rw [roughCanonicalBridgeRelevantGuardSet,
    bankPaperCanonicalSmoothResidualAnchorPool,
    Finset.mem_image] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  rw [certificate.anchors_eq, fullCentralAnchors]
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr
    ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩

/-- A smooth guarded central anchor is necessarily one of the relevant
promoted residual anchors.  Large routed anchors retain their marker prime
above the smooth cutoff. -/
theorem guardedCentralAnchor_mem_bridgeRelevant_of_smooth
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    {a : Nat} (ha : a ∈ certificate.anchors) (haPos : 0 < a)
    (haSmooth : a ∈ Nat.smoothNumbers (yNat n + 1)) :
    a ∈ roughCanonicalBridgeRelevantGuardSet certificate := by
  have haLabel : completeRoughLabel (yNat n) a = 1 :=
    (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mpr haSmooth
  rw [certificate.anchors_eq, fullCentralAnchors] at ha
  rcases Finset.mem_union.mp ha with haPromoted | haLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haPromoted
    rw [roughCanonicalBridgeRelevantGuardSet,
      bankPaperCanonicalSmoothResidualAnchorPool]
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    by_contra hpNotLe
    have hpHigh : yNat n < p := Nat.lt_of_not_ge hpNotLe
    have hpPrime := residualCentralPrimes_prime hp
    have hpDvdFactor : p ∣ promotedCentralFactor n p := by
      unfold promotedCentralFactor promotedBlock centralPrimeBlock
      exact dvd_mul_of_dvd_right
        (dvd_pow_self p
          (residualCentralPrimes_exponent_pos hp).ne') _
    have hpDvdLabel :
        p ∣ completeRoughLabel (yNat n)
          (promotedCentralFactor n p) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hpHigh
        haPos.ne' hpDvdFactor
    rw [haLabel] at hpDvdLabel
    exact hpPrime.not_dvd_one hpDvdLabel
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hP
    have hPHigh : yNat n < P :=
      hyCutoff.trans (largeCentralPrimes_gt hP)
    have hPDvdLabel :
        P ∣ completeRoughLabel (yNat n)
          (largeCentralAnchor certificate.q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        haPos.ne' (dvd_mul_right P (certificate.q P))
    rw [haLabel] at hPDvdLabel
    exact (hPPrime.not_dvd_one hPDvdLabel).elim



namespace BankPaperRealization

/-- On every positive smooth integer at most `2n`, membership in the
bridge-relevant guard is equivalent to membership in the global five-family
rough guard. -/
theorem mem_roughCanonicalBridgeRelevantGuardSet_iff_mem_guardSet
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    {a : Nat} (haPos : 0 < a) (haUpper : a <= 2 * n)
    (haSmooth : a ∈ Nat.smoothNumbers (yNat n + 1)) :
    a ∈ roughCanonicalBridgeRelevantGuardSet certificate ↔
      a ∈ R.roughCanonicalGuardSet certificate deltaStar := by
  classical
  constructor
  · intro ha
    have haAnchor :=
      roughCanonicalBridgeRelevantGuardSet_subset_anchors certificate ha
    simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
      Finset.mem_union]
    exact Or.inl <| Or.inl <| Or.inl <| Or.inl haAnchor
  · intro haGuard
    have haLabel : completeRoughLabel (yNat n) a = 1 :=
      (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mpr haSmooth
    simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
      Finset.mem_union] at haGuard
    rcases haGuard with
      (((haAnchor | haFixed) | haDonor) | haBase) | haAlternate
    · exact guardedCentralAnchor_mem_bridgeRelevant_of_smooth
        certificate hyCutoff haAnchor haPos haSmooth
    · have haTail :=
        R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
      exact (Nat.not_lt_of_ge haUpper (Finset.mem_Ioc.mp haTail).1).elim
    · have haTail := R.prechargeDonorSet_subset_tail haDonor
      exact (Nat.not_lt_of_ge haUpper (Finset.mem_Ioc.mp haTail).1).elim
    · rw [prechargeBaseState, indexedPathState, Finset.mem_image] at haBase
      obtain ⟨request, _hrequest, rfl⟩ := haBase
      rw [R.prechargeBase_completeRoughLabel_eq_marker] at haLabel
      have hmarker := R.yNat_lt_paperMarker request
      have hySix := R.six_le_yNat
      omega
    · rw [prechargeAlternateState, indexedPathState,
        Finset.mem_image] at haAlternate
      obtain ⟨request, _hrequest, rfl⟩ := haAlternate
      rw [R.prechargeAlternate_completeRoughLabel_eq_marker] at haLabel
      have hmarker := R.yNat_lt_paperMarker request
      have hySix := R.six_le_yNat
      omega

/-! ## The canonical two-promoted-slot ledger -/





/-- Whenever a realization exists, its pointwise canonical relevant ledger is
the fixed family chosen before the realization and certificate.  The
realization supplies only the proof that the canonical branch of the total
family is active. -/
theorem roughCanonicalBridgeRelevantLedgerFamily_eq
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    roughCanonicalBridgeRelevantLedgerFamily depth n =
      R.roughCanonicalBridgeRelevantLedger certificate := by
  have hcard :
      (insert 0
        (bankPaperCanonicalSmoothResidualAnchorPool n
          (centralAnchorCutoff depth n) (yNat n))).card <=
        Fintype.card (GuardSlot n 2 0) := by
    simpa only [roughCanonicalBridgeRelevantGuardSet] using
      R.roughCanonicalBridgeRelevantGuardSet_insert_zero_card_le_guardSlot
        certificate
  unfold roughCanonicalBridgeRelevantLedgerFamily
  rw [dif_pos hcard]
  unfold roughCanonicalBridgeRelevantLedger
    roughCanonicalBridgeRelevantGuardSet
  rfl

/-- Exact image of the canonical relevant ledger. -/
theorem roughCanonicalBridgeRelevantLedger_guards
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    (R.roughCanonicalBridgeRelevantLedger certificate).guards =
      insert 0 (roughCanonicalBridgeRelevantGuardSet certificate) := by
  unfold roughCanonicalBridgeRelevantLedger
  apply ledgerOfFinsetWithZero_guards



/-- The canonical relevant ledger satisfies the local agreement interface. -/
theorem roughCanonicalBridgeRelevantLedger_agreement
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    BankPaperCanonicalBridgeGuardAgreement
      (R.roughCanonicalBridgeRelevantLedger certificate)
      R certificate deltaStar := by
  intro a haPos haUpper haSmooth
  rw [R.roughCanonicalBridgeRelevantLedger_guards certificate,
    Finset.mem_insert]
  have haZero : a ≠ 0 := haPos.ne'
  simp only [haZero, false_or]
  exact R.mem_roughCanonicalBridgeRelevantGuardSet_iff_mem_guardSet
    certificate deltaStar hyCutoff haPos haUpper haSmooth

/-- Finite local agreement for the fixed ledger family. -/
theorem roughCanonicalBridgeRelevantLedgerFamily_agreement
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    BankPaperCanonicalBridgeGuardAgreement
      (roughCanonicalBridgeRelevantLedgerFamily depth n)
      R certificate deltaStar := by
  rw [R.roughCanonicalBridgeRelevantLedgerFamily_eq certificate]
  exact R.roughCanonicalBridgeRelevantLedger_agreement
    certificate deltaStar hyCutoff



/-- Eventual agreement with the ledger family fixed before quantifying over
the realization and certificate.  This is the quantifier order consumed by
the canonical structured-sample and one-shot bridge interfaces. -/
theorem eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
    {c : Real} (depth : Nat) (deltaStar : Real) :
    ∀ᶠ n : Nat in atTop,
      forall
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        BankPaperCanonicalBridgeGuardAgreement
          (roughCanonicalBridgeRelevantLedgerFamily depth n)
          R certificate deltaStar := by
  filter_upwards [eventually_yNat_lt_centralAnchorCutoff depth] with
    n hyCutoff
  intro R certificate
  exact R.roughCanonicalBridgeRelevantLedgerFamily_agreement
    certificate deltaStar hyCutoff

/-! ## Equality on raw cells and structured active values -/









/-- Any locally agreeing ledger turns the structured sample's built-in guard
avoidance into avoidance of the full global rough guard.  This is the generic
`hnotGuard` migration interface; it does not require a global equality of
finite guard sets. -/
theorem structuredSample_value_not_fullGuard_of_agreement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    {c : Real} {depth h Cprom Cbank : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (G : Ledger D.n Cprom Cbank)
    (R : BankPaperRealization D.n (upperEndpoint D.n h))
    (certificate : GuardedCentralAnchorCertificate c depth D.n
      left right changed)
    (deltaStar : Real)
    (hagreement : BankPaperCanonicalBridgeGuardAgreement
      G R certificate deltaStar)
    (hupper : forall m : D.Sample, D.value m <= 2 * D.n)
    (hguards : D.guards = G.guards)
    (m : D.Sample) :
    D.value m ∉ R.roughCanonicalGuardSet certificate deltaStar := by
  intro haFull
  apply D.value_not_guard m
  rw [hguards]
  exact
    (hagreement (D.value m) (D.value_pos m) (hupper m)
      (D.value_mem_smoothNumbers m)).mpr haFull



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector -/
section


/-!
# One-shot Section 8 orchestration for the two zero-head cells

This file joins the three already audited layers of the literal Section 8
construction:

* the analytic ledger gives the `q0` and integer-height asymptotics;
* the two-zero-cell producer realizes the height change by `-d / 2` in
  each physical copy of the zero head cell; and
* the structured prebridge ledger transports the resulting integral row
  change and the exact head-prime moments.

The source selector is not postulated through a new interface.  It is the
canonical protected-plus-ambient selector, and its finite selector state is
read directly from the existing
`BankPaperCanonicalRoundedSelectorTangentInput`.  Consequently the only
new feasibility work is at the two coordinates that actually change.

The terminal eventual theorem uses the same `hcanonical` and
`cellMassMargin` arguments as the canonical Proposition 8.7 statement.  It
only assumes that the ledger and rough guard agree on the positive, smooth,
at-most-`2n` structured universe.  Together with the canonical sample guards,
this yields pointwise exclusion from the full rough guard without any global
Finset equality.  To invoke the existing actual P87 endpoint consumer after
the structured placement, one must additionally identify
the rebalanced seed with a bridge baseline (`Hmeasure` and `hseed`) and
supply the existing analytic `Hfit`; those are retained under their
existing names rather than hidden in a new assumption package.
-/

open Filter Topology Asymptotics Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A reusable two-cell scalar capacity lemma -/



/-! ## Height-only capacity from the Section 8 ledger -/









/-! ## Reusing the rounded source selector -/







/-! ## Exact quota transport -/











/-! ## Canonical P87-local one-shot orchestration -/

/-- A fixed multiple of the upper-tail length is eventually at most the
ambient sample size. -/
theorem eventually_mul_upperTailLength_le_self
    (K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      K * upperTailLength c n <= n := by
  have hT : Tendsto
      (fun n : Nat => (K : Real) *
        ((upperTailLength c n : Real) / (n : Real)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
  have hsmall := hT.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnPos
  have hn' :
      (K : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := hn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hnPos
  have hnDiv :
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) < 1 := by
    calc
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) =
          (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) := by ring
      _ < 1 := hn'
  have hcross :
      (K : Real) * (upperTailLength c n : Real) < (n : Real) := by
    simpa only [one_mul] using (div_lt_iff₀ hnReal).mp hnDiv
  have hcast :
      ((K * upperTailLength c n : Nat) : Real) < (n : Real) := by
    push_cast
    exact hcross
  exact_mod_cast hcast.le







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPhysicalMarginAlgebra -/
section


/-!
# The explicit post-height physical margin

This file fixes one completely explicit pair of paper-valid physical
intervals around

`mu = log (3 / 2)`.

The minus pool is `[1, 4 / 3]` and the plus pool is
`[5 / 3, 7 / 4]`.  Thus both pools lie in the paper's physical range
`[1, 2]`, and there is a fixed logarithmic gap on either side of `mu`.

The analytic input is kept transparent.  A generic lemma says that an
error which is `O(scale)` tends to zero whenever `scale` does, and hence
the corresponding centered mean eventually retains half of any fixed
`PhysicalInterpolationTarget` margin.  It is then applied to the literal
post-height physical-mean error and the paper's scale

`L / N`, where `N = secondOrderScale = n / L`.

No target/source wrapper and no conclusion-bearing premise is introduced.
-/

open Filter Topology Set Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

/-! ## Explicit paper-valid physical data -/













/-- The explicit intervals satisfy the lower endpoint restriction used by
the canonical guarded sample. -/
theorem bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
    (sigma : PhysicalSign) :
    1 ≤ bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
      sigma := by
  cases sigma <;> norm_num

/-- The explicit intervals satisfy the upper endpoint restriction used by
the canonical guarded sample. -/
theorem bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
    (sigma : PhysicalSign) :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper sigma ≤
      2 := by
  cases sigma <;> norm_num





















/-! ## The elementary asymptotic margin algebra -/







/-! ## The literal post-height physical mean -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightCoherentTargetConstructor -/
section


/-!
# The coherent finite post-height target constructor

This file closes the finite choice boundary between the depth-first
combined-charge terminal and the fresh Section 9 post-height bridge.

There are two deliberately separate pieces.

* The first theorem turns the eventual existential output of
  `BankPaperCombinedChargeTerminalAtDepth` into one honest tail family.  Its
  conclusion repeats the six literal terminal properties pointwise; no
  conclusion-bearing structure is introduced.
* The bridge definitions below start from an actual
  `StructuredSampleData`, build a harmless scaffold bridge, form the
  paper's literal head/physical barycentric target on that sample, and then
  install that same target in a canonical bridge.  This removes the
  otherwise circular-looking dependence of `barycentricTargetOfPaperData`
  on an already supplied `BridgeData`.

The eventual head and physical interior estimates are proved in the
remaining sections of this module.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

/-! ## One coherent family chosen from the eventual terminal -/



/-! ## Uniform finite head bounds from the same fibers -/



theorem bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos
    {c : Real} (hc : C0 < c) {W : Nat} (hW : 0 < W) :
    0 < bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W := by
  unfold bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
  exact div_pos (sub_pos.mpr hc)
    (mul_pos (by norm_num) (by exact_mod_cast hW))







/-! ## One pair of source/post-height mass envelopes -/





/-! ## Exact synchronization of the local and family physical means -/



/-! ## A non-circular bridge built from structured sample data -/





















/-- The target installed in the constructed source bridge is exactly the
paper's head/physical barycentric target when viewed from that bridge.
This is the equality consumed by the rounded-source residual connector. -/
theorem bankPaperCanonicalSectionNineCoherentSourceTarget_eq_bridgeTarget
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    let Tsource :=
      bankPaperCanonicalSectionNineCoherentSourceTarget
        M D I hlo hhi Rhead Kphysical hdelta hn hW S hw
    let Bsource :=
      bankPaperCanonicalSectionNineCoherentSourceBridge
        M D I hlo hhi Rhead Kphysical hdelta hn hW S hw
    Tsource =
      Bsource.barycentricTargetOfPaperData
        I hlo hhi Rhead Kphysical := by
  rfl

/-! ## Finite coherent assembly of the fresh bridge inputs -/



namespace BankPaperRealization



/-! ## Eventual coherent target construction on supplied sample geometry -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightActiveMassScaleLowerConnector -/
section


/-!
# Paper-scale lower bound for the guarded Section 8 active mass

The explicit raw smooth base has a positive `secondOrderScale` lower bound.
This connector shows that the concrete guarded tail-family base inherits
that bound without any additional analytic input:

* the guard-deletion pool is bounded by the already controlled smooth
  anchor intersection;
* its weighted mass is therefore `o(secondOrderScale)`; and
* deleting that negligible mass preserves the positive lower comparison.

The tie-lower nearest-integer initialization changes the guarded mass by at
most one half, so the literal Section 8 `q0` family inherits the same type of
lower bound.  No frozen-height or selector-mass hypothesis is used here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.Scale

noncomputable section

/-! ## The concrete guard-deletion census -/

/-- Every honest guarded tail family has the smooth guard-deletion census
needed by the raw-to-guarded mass comparison. -/
theorem bankPaperCanonicalGuardedTailSmoothBaseDeletionCensus
    {c : Real} {N : Nat} (depth W K : Nat) (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    BankPaperCanonicalSmoothGuardDeletionCensus
      (F.extendedSmoothBaseGuardDeletionCard W K deltaStar) := by
  have hdeletedToAnchors :
      F.extendedSmoothBaseGuardDeletionCard W K deltaStar =O[atTop]
        F.extendedAnchorIntersectionCard W K := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [
      BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
      dif_pos hn,
      BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard,
      dif_pos hn, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
    exact_mod_cast
      bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
        (BankPaperCanonicalGuardedTailFamily.realization F n hn)
        (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
          deltaStar W K
  exact hdeletedToAnchors.trans
    (guardedCentralAnchors_inter_rawSmoothBasePool_isBigO_envelope
      depth W K F)

/-! ## Raw-to-guarded loss -/

/-- Guard deletion changes the explicit smooth base by
`o(secondOrderScale)`, uniformly for the concrete guarded tail-family
extension. -/
theorem
    bankPaperCanonicalRawSmoothBase_sub_extendedGuardedSmoothBase_isLittleO
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    (fun n =>
      bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) K betaAct -
        F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n)
      =o[atTop] secondOrderScale := by
  apply bankPaperCanonicalRawSmoothBase_sub_guarded_isLittleO_of_census
    betaAct
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
    (F.extendedSmoothBaseGuardDeletionCard W K deltaStar)
  · intro n
    by_cases hn : N ≤ n
    · simpa only [
          BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
          BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
          dif_pos hn] using
        bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
          (BankPaperCanonicalGuardedTailFamily.realization F n hn)
          (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
            deltaStar W K betaAct
    · simp only [
        BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
        BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
        dif_neg hn, sub_self, mul_zero]
  · exact bankPaperCanonicalGuardedTailSmoothBaseDeletionCensus
      depth W K deltaStar F

/-! ## Positive paper-scale mass -/

/-- The literal guarded smooth base retains a fixed positive multiple of
`secondOrderScale` whenever the active broad coefficient is positive. -/
theorem
    bankPaperCanonicalExtendedGuardedSmoothBaseMass_paperScaleLower
    {c betaAct : Real} {N : Nat} (depth W K : Nat)
    (hc : 0 < c) (hbeta : 0 < betaAct) (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar) := by
  exact bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
    (bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
      W K hc hbeta)
    (bankPaperCanonicalRawSmoothBase_sub_extendedGuardedSmoothBase_isLittleO
      depth W K betaAct deltaStar F)



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPostHfitBalancedAlphaEventually -/
section


/-!
# Eventual feasibility of the canonical Post-Hfit balanced coefficient

The paper first chooses a positive total broad coefficient
`beta < c / (3 * roughHeadDensity W)` and then takes the fixed high-block
multiplicity sufficiently large.  This file records that choice at the
exact finite level.

No quota or height-ledger asymptotic is needed.  The defining ceiling gives

`c * n / log n <= upperTailLength c n`

pointwise, which already makes the numerator of the balanced coefficient
nonnegative.  Taking the multiplicity at least the reciprocal head density
makes the same numerator at most its denominator.
-/

open Filter Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit

noncomputable section

/-! ## Finite balanced-coefficient algebra -/

/-- The exact two inequalities behind feasibility of the balanced raw
coefficient.  The hypotheses are deliberately stated before specializing
`h` to the paper's integral upper-tail length. -/
theorem roughHeadBalancedAlpha_mem_Icc_of_tail_lower
    {W n h K : Nat} {c beta ell : Real}
    (hc : 0 < c) (hn : 0 < n) (hKpos : 0 < K)
    (hell : 0 < ell) (hbeta : 0 ≤ beta)
    (hbetaUpper : beta ≤ c / roughHeadDensity W)
    (hKlarge : 1 / roughHeadDensity W ≤ (K : Real))
    (htail : c * (n : Real) / ell ≤ (h : Real)) :
    roughHeadBalancedAlpha W n h K beta ell ∈
      Icc (0 : Real) 1 := by
  have hdensity : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have htailBase : 0 < c * (n : Real) / ell :=
    div_pos (mul_pos hc hnReal) hell
  have hhReal : (0 : Real) < (h : Real) :=
    htailBase.trans_le htail
  have hh : 0 < h := by
    exact_mod_cast hhReal
  have hden :
      0 < (((K * h : Nat) : Real)) := by
    exact_mod_cast Nat.mul_pos hKpos hh
  have hsub :
      (((n - K * h : Nat) : Real)) ≤ (n : Real) := by
    exact_mod_cast Nat.sub_le n (K * h)
  have hbetaDiv : 0 ≤ beta / ell :=
    div_nonneg hbeta hell.le
  have htermNonneg :
      0 ≤ (beta / ell) * (((n - K * h : Nat) : Real)) :=
    mul_nonneg hbetaDiv (Nat.cast_nonneg _)
  have htermUpper :
      (beta / ell) * (((n - K * h : Nat) : Real)) ≤
        (h : Real) / roughHeadDensity W := by
    calc
      (beta / ell) * (((n - K * h : Nat) : Real)) ≤
          (beta / ell) * (n : Real) :=
        mul_le_mul_of_nonneg_left hsub hbetaDiv
      _ = beta * ((n : Real) / ell) := by ring
      _ ≤ (c / roughHeadDensity W) * ((n : Real) / ell) :=
        mul_le_mul_of_nonneg_right hbetaUpper
          (div_nonneg hnReal.le hell.le)
      _ = (c * (n : Real) / ell) / roughHeadDensity W := by ring
      _ ≤ (h : Real) / roughHeadDensity W :=
        div_le_div_of_nonneg_right htail hdensity.le
  have hnumNonneg :
      0 ≤ (h : Real) / roughHeadDensity W -
        (beta / ell) * (((n - K * h : Nat) : Real)) :=
    sub_nonneg.mpr htermUpper
  have hheadUpper :
      (h : Real) / roughHeadDensity W ≤
        (((K * h : Nat) : Real)) := by
    calc
      (h : Real) / roughHeadDensity W =
          (1 / roughHeadDensity W) * (h : Real) := by ring
      _ ≤ (K : Real) * (h : Real) :=
        mul_le_mul_of_nonneg_right hKlarge hhReal.le
      _ = (((K * h : Nat) : Real)) := by
        norm_num only [Nat.cast_mul]
  constructor
  · rw [roughHeadBalancedAlpha]
    exact div_nonneg hnumNonneg hden.le
  · rw [roughHeadBalancedAlpha]
    exact
      (div_le_one hden).2
        ((sub_le_self _ htermNonneg).trans hheadUpper)

namespace BankPaperRealization

/-! ## Canonical bridge specialization -/

/-- Pointwise feasibility for the literal Post-Hfit coefficient.  The only
scale input is the paper's exact upper-tail ceiling. -/
theorem bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {c : Real} (K0 : Nat)
    (betaProt betaAct : Real) (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤
        c / roughHeadDensity B.sampleData.W)
    (hKlarge :
      1 / roughHeadDensity B.sampleData.W ≤
        (((K0 + 1 : Nat) : Real))) :
    bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  have htail :
      c * (B.sampleData.n : Real) / B.L ≤
        (upperTailLength c B.sampleData.n : Real) := by
    calc
      c * (B.sampleData.n : Real) / B.L =
          c * secondOrderScale B.sampleData.n := by
        unfold BridgeData.L secondOrderScale
        ring
      _ ≤ (upperTailLength c B.sampleData.n : Real) := by
        simpa only [upperTailLength] using
          (Nat.le_ceil
            (c * secondOrderScale B.sampleData.n))
  simpa only [bankPaperCanonicalPostHfitBalancedAlpha] using
    (roughHeadBalancedAlpha_mem_Icc_of_tail_lower
      (W := B.sampleData.W) (n := B.sampleData.n)
      (h := upperTailLength c B.sampleData.n) (K := K0 + 1)
      (c := c) (beta := betaProt + betaAct) (ell := B.L)
      hc (Nat.zero_lt_of_lt B.n_gt_one) (by omega)
      B.L_pos hbeta hbetaUpper hKlarge htail)

/-- Uniform family form used by the Section 9 supplier.  It applies to every
bridge with the synchronized width, hence in particular to the coherent
canonical/post-height bridge family. -/
theorem eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W K0 : Nat) {c betaProt betaAct : Real} (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real))) :
    ∀ᶠ n : Nat in atTop,
      ∀ B : BridgeData Head Band,
        B.sampleData.n = n →
        B.sampleData.W = W →
        bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  refine Eventually.of_forall ?_
  intro n B _hBn hBW
  apply
    bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
      B K0 betaProt betaAct hc hbeta
  · simpa only [hBW] using hbetaUpper
  · simpa only [hBW] using hKlarge





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstRichSourceWithFixedNumericalData -/
section


/-!
# Rich source family from fixed pre-mesh numerical data

This file is the mesh-dependent continuation of
`BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshNumericalData`.
The source mass coefficients, head exponent, and source cell margin are
fixed before the regular mesh is introduced.

The conclusion contains only the genuine rich source geometry, its literal
thin projection, and the three eventual source, readiness, and canonical
geometry events.  No named conclusion contract, analytic ledger, frozen
family, post-height bridge, or downstream input package is assumed.
-/

open Filter Topology Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000 in
/-- Construct the mesh-dependent rich source family after all numerical
data supplied by the pre-mesh theorem have been fixed.

The equality for `sourceCellMargin` is retained explicitly because it is
the bridge between the fixed pre-mesh choice and the literal barycentric
target margin constructed below. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceWithFixedNumericalData
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : C0 < c)
    (hdeltaStar : IsPaperCombinedChargeDeltaStar c deltaStar)
    (hW : 0 < W)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)))
    (hprefix : 2 * depth + 1 ≤ W)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hterminal :
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n))
    (cSource cUpper : Real) (E : Nat) (sourceCellMargin : Real)
    (hcSource : 0 < cSource)
    (hcUpper : 0 < cUpper)
    (hE : 0 < E)
    (hsourceCellMarginEq :
      sourceCellMargin =
        bankPaperCanonicalSectionNinePostHeightHeadMargin E
            (fun _ : {p : Nat // p ∈ primesUpTo W} =>
              bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
            cUpper *
          bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau)
    (hElarge :
      2 *
            (∑ p : {p : Nat // p ∈ primesUpTo W},
              bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                c p.1) ≤
          (E : Real) * (cSource / 4))
    (Hmass :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n ∧
          F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n ≤
            cUpper * secondOrderScale n)
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) :
    let P := primesUpTo W
    let I :=
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
    let Patterns :=
      PaperHeadSimplex.pattern P
        (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W) E
    let G : ∀ n, Ledger n 2 0 :=
      roughCanonicalBridgeRelevantLedgerFamily depth
    let hw : 0 < delta + eta :=
      add_pos hdelta (M.ratio_pos.trans_le M.ratio_le_eta)
    let RichFiber : Type :=
      Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
      Σ' _hnTail : N ≤ D.n,
      Σ' _hnD : 1 < D.n,
      Σ' _hWD : D.W ≠ 0,
      Σ' _S : ScaleSeparation M D.n D.W,
      Σ' _hlo : (∀ sigma, D.lo sigma =
          physicalBound (I.lower sigma) D.n),
      Σ' _hhi : (∀ sigma, D.hi sigma =
          physicalBound (I.upper sigma) D.n),
        HeadSimplexReserve P
    let ThinFiber : Type :=
      Σ B : BridgeData (PaperHeadSimplex.Tag P)
          (BankPaperCanonicalExponentBand M),
        BankPaperCanonicalGuardedTailFiber
            c depth B.sampleData.n ×
          BarycentricTarget B.sampleData
    let thinOfRich : RichFiber → ThinFiber := fun Z => by
      change
        (Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
          Σ' _hnTail : N ≤ D.n,
          Σ' _hnD : 1 < D.n,
          Σ' _hWD : D.W ≠ 0,
          Σ' _S : ScaleSeparation M D.n D.W,
          Σ' _hlo : (∀ sigma, D.lo sigma =
              physicalBound (I.lower sigma) D.n),
          Σ' _hhi : (∀ sigma, D.hi sigma =
              physicalBound (I.upper sigma) D.n),
            HeadSimplexReserve P) at Z
      rcases Z with
        ⟨D, hnTail, hnD, hWD, S, hlo, hhi, Rhead⟩
      let Kphysical :=
        bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
      let Tsource :=
        bankPaperCanonicalSectionNineCoherentSourceTarget
          M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
      let Bsource :=
        bankPaperCanonicalSectionNineCoherentSourceBridge
          M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
      refine ⟨Bsource, ?_⟩
      change
        BankPaperCanonicalGuardedTailFiber c depth D.n ×
          BarycentricTarget D
      exact
        ⟨⟨F.realization D.n hnTail, F.certificate D.n hnTail⟩,
          Tsource⟩
    ∃ sourceGeom : ∀ n, N ≤ n → RichFiber,
    ∃ source : ∀ n, N ≤ n → ThinFiber,
      (∀ n hn, source n hn = thinOfRich (sourceGeom n hn)) ∧
      (∀ᶠ n : Nat in atTop,
        ∀ hn : N ≤ n,
          let X := source n hn
          let B := X.1
          let R := X.2.1.1
          let certificate := X.2.1.2
          let T := X.2.2
          let alpha :=
            bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct
          let qTilde :=
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n
          B.sampleData.n = n ∧
            B.sampleData.W = W ∧
            qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass
                R certificate deltaStar B.sampleData.W
                  (K0 + 1) betaAct ∧
            1 ≤ qTilde ∧
            B.sampleData.HeadPatternsSeparated ∧
            bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
              R.roughCanonicalGuardedRow
                certificate deltaStar (K0 + 1) 1 ∧
            (0 ≤ alpha ∧ alpha ≤ 1) ∧
            (0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1) ∧
            BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
              (K := K0 + 1) B R certificate
              (R.paperFixedExceptionalFactors deltaStar)
              T deltaStar betaProt alpha
                (betaProt + betaAct) qTilde ∧
            certificate.prechargedTailTarget =
              (F.certificate n hn).prechargedTailTarget) ∧
      (∀ᶠ n : Nat in atTop,
        ∀ hn : N ≤ n,
          let X := source n hn
          let B := X.1
          let R := X.2.1.1
          let certificate := X.2.1.2
          let T := X.2.2
          let target :
              {p : Nat // p ∈ primesUpTo W} → Real :=
            fun p =>
              ((certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors
                  deltaStar)).factorization p.1 : Real)
          B.sampleData.n = n ∧
            (∀ p : {p : Nat // p ∈ primesUpTo W},
              bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
                      c W *
                    secondOrderScale n ≤
                  target p ∧
                target p ≤
                  bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                      c p.1 *
                    secondOrderScale n) ∧
            ∃ _hWB : B.sampleData.W ≠ 0,
            ∃ _S : ScaleSeparation
                M B.sampleData.n B.sampleData.W,
            ∃ hlo : ∀ sigma, B.sampleData.lo sigma =
                physicalBound (I.lower sigma) B.sampleData.n,
            ∃ hhi : ∀ sigma, B.sampleData.hi sigma =
                physicalBound (I.upper sigma) B.sampleData.n,
            ∃ Rhead : HeadSimplexReserve (primesUpTo W),
            ∃ Kphysical : PhysicalInterpolationTarget I,
              Rhead.exponent = E ∧
                (∀ p : {p : Nat // p ∈ primesUpTo W},
                  Rhead.target p = target p) ∧
                F.extendedGuardedSmoothBaseMass
                    W (K0 + 1) betaAct deltaStar n =
                  Rhead.activeMass ∧
                sourceCellMargin ≤ T.cellMassMargin ∧
                T =
                  B.barycentricTargetOfPaperData
                    I hlo hhi Rhead Kphysical) ∧
      ∀ᶠ n : Nat in atTop,
        ∀ hn : N ≤ n,
          let X := source n hn
          let B := X.1
          let R := X.2.1.1
          let certificate := X.2.1.2
          ∃ hsep :
              physicalBound (I.upper .minus) n <
                physicalBound (I.lower .plus) n,
          ∃ hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
              (rawCell Patterns I n cell \ (G n).guards).Nonempty,
            B.sampleData =
                canonicalSampleData
                  (W := W) Patterns I (G n) hsep hremaining ∧
              BankPaperCanonicalBridgeGuardAgreement
                (G B.sampleData.n) R certificate deltaStar := by
  have hC0Pos : (0 : Real) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hdeltaStarPos : 0 < deltaStar := hdeltaStar.1
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  let P := primesUpTo W
  have hprime : ∀ p ∈ P, p.Prime := by
    simpa only [P] using
      bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  let Patterns : PaperHeadSimplex.Tag P → Pattern :=
    PaperHeadSimplex.pattern P hprime E
  let G : ∀ n, Ledger n 2 0 :=
    roughCanonicalBridgeRelevantLedgerFamily depth
  have hetaPos : 0 < eta :=
    M.ratio_pos.trans_le M.ratio_le_eta
  have hw : 0 < delta + eta := add_pos hdelta hetaPos
  let RichFiber : Type :=
    Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
    Σ' _hnTail : N ≤ D.n,
    Σ' _hnD : 1 < D.n,
    Σ' _hWD : D.W ≠ 0,
    Σ' _S : ScaleSeparation M D.n D.W,
    Σ' _hlo : (∀ sigma, D.lo sigma =
        physicalBound (I.lower sigma) D.n),
    Σ' _hhi : (∀ sigma, D.hi sigma =
        physicalBound (I.upper sigma) D.n),
      HeadSimplexReserve P
  let ThinFiber : Type :=
    Σ B : BridgeData (PaperHeadSimplex.Tag P)
        (BankPaperCanonicalExponentBand M),
      BankPaperCanonicalGuardedTailFiber
          c depth B.sampleData.n ×
        BarycentricTarget B.sampleData
  let thinOfRich : RichFiber → ThinFiber := fun Z => by
    change
      (Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
        Σ' _hnTail : N ≤ D.n,
        Σ' _hnD : 1 < D.n,
        Σ' _hWD : D.W ≠ 0,
        Σ' _S : ScaleSeparation M D.n D.W,
        Σ' _hlo : (∀ sigma, D.lo sigma =
            physicalBound (I.lower sigma) D.n),
        Σ' _hhi : (∀ sigma, D.hi sigma =
            physicalBound (I.upper sigma) D.n),
          HeadSimplexReserve P) at Z
    rcases Z with
      ⟨D, hnTail, hnD, hWD, S, hlo, hhi, Rhead⟩
    let Kphysical :=
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
    let Tsource :=
      bankPaperCanonicalSectionNineCoherentSourceTarget
        M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
    let Bsource :=
      bankPaperCanonicalSectionNineCoherentSourceBridge
        M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
    refine ⟨Bsource, ?_⟩
    change
      BankPaperCanonicalGuardedTailFiber c depth D.n ×
        BarycentricTarget D
    exact
      ⟨⟨F.realization D.n hnTail, F.certificate D.n hnTail⟩,
        Tsource⟩
  change
    ∃ sourceGeom : ∀ n, N ≤ n → RichFiber,
    ∃ source : ∀ n, N ≤ n → ThinFiber,
      (∀ n hn, source n hn = thinOfRich (sourceGeom n hn)) ∧
      _ ∧ _ ∧ _
  let a : {p : Nat // p ∈ P} → Real :=
    fun _ =>
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W
  let b : {p : Nat // p ∈ P} → Real :=
    fun p =>
      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c p.1
  have ha : ∀ p, 0 < a p := by
    intro p
    simpa only [a] using
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos hc hW
  have hb : ∀ p, 0 ≤ b p := by
    intro p
    have hpPrime : p.1.Prime := hprime p.1 p.2
    have hpredNat : 0 < p.1 - 1 :=
      Nat.sub_pos_of_lt hpPrime.one_lt
    have hpredReal :
        (0 : Real) < ((p.1 - 1 : Nat) : Real) := by
      exact_mod_cast hpredNat
    dsimp only [b,
      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient]
    exact
      (add_pos (div_pos hcPos hpredReal) (by norm_num)).le
  have hfiberHead :
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n) := by
    intro n hn
    dsimp only
    have h := hterminal n hn
    dsimp only at h
    exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩
  have Hhead :=
    eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds
      (W := W) hc hdeltaStar hW P hprime
        (by
          intro p hp
          exact (mem_primesUpTo.mp hp).2)
        F hfiberHead
  have Hsep := eventually_physicalBound_separated I
  have Hremaining :=
    eventually_guarded_rawCell_nonempty Patterns I G
  have Hmesh :=
    Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.eventually_scaleSeparation
      M hdelta W
  have HmassPaper :
      BankPaperCanonicalActiveMassPaperScaleLower qTilde := by
    simpa only [qTilde] using
      bankPaperCanonicalExtendedGuardedSmoothBaseMass_paperScaleLower
        depth W (K0 + 1) hcPos hbetaAct deltaStar F
  have Hone :=
    eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
      qTilde HmassPaper
  have hupperStrict :
      ∀ sigma, I.upper sigma < 2 := by
    intro sigma
    cases sigma <;>
      norm_num [I,
        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals]
  have HupperBroad :=
    eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
      I (K0 + 1) hcPos hupperStrict
  have HroughDepth :=
    eventually_mul_upperTailLength_le_self (K0 + 1) hcPos
  have Hagreement :=
    eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
      (c := c) depth deltaStar
  have hbetaNonneg : 0 ≤ betaProt + betaAct :=
    add_nonneg hbetaProt hbetaAct.le
  have Halpha :=
    eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
      (Head := PaperHeadSimplex.Tag P)
      (Band := BankPaperCanonicalExponentBand M)
      W K0 hcPos hbetaNonneg hbetaUpper hKlarge
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have HbetaProtRoom : ∀ᶠ n : Nat in atTop, betaProt ≤ L n :=
    hLTop.eventually (eventually_ge_atTop betaProt)
  have Hresidual :=
    eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget
      (Band := BankPaperCanonicalExponentBand M)
      Patterns I 2 0 G depth W K0
      hcPos hdeltaStarPos hbetaProt hbetaAct
      (by norm_num : (0 : Real) ≤ 0) hbetaProt
      hbetaUpper hKlarge hprefix
  have Hgood :
      ∀ᶠ n : Nat in atTop,
        ∃ Z : RichFiber,
          (∀ hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            let T := X.2.2
            let alpha :=
              bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct
            let qSource :=
              F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n
            B.sampleData.n = n ∧
              B.sampleData.W = W ∧
              qSource =
                bankPaperCanonicalGuardedSmoothBaseMass
                  R certificate deltaStar B.sampleData.W
                    (K0 + 1) betaAct ∧
              1 ≤ qSource ∧
              B.sampleData.HeadPatternsSeparated ∧
              bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
                R.roughCanonicalGuardedRow
                  certificate deltaStar (K0 + 1) 1 ∧
              (0 ≤ alpha ∧ alpha ≤ 1) ∧
              (0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1) ∧
              BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
                (K := K0 + 1) B R certificate
                (R.paperFixedExceptionalFactors deltaStar)
                T deltaStar betaProt alpha
                  (betaProt + betaAct) qSource ∧
              certificate.prechargedTailTarget =
                (F.certificate n hn).prechargedTailTarget) ∧
          (∀ _hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            let T := X.2.2
            let target : {p : Nat // p ∈ primesUpTo W} → Real :=
              fun p =>
                ((certificate.selectorTailTarget R
                  (R.paperFixedExceptionalFactors
                    deltaStar)).factorization p.1 : Real)
            B.sampleData.n = n ∧
              (∀ p : {p : Nat // p ∈ primesUpTo W},
                bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
                      secondOrderScale n ≤
                    target p ∧
                  target p ≤
                    bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                        c p.1 *
                      secondOrderScale n) ∧
              ∃ _hWB : B.sampleData.W ≠ 0,
              ∃ _S : ScaleSeparation
                  M B.sampleData.n B.sampleData.W,
              ∃ hlo : ∀ sigma, B.sampleData.lo sigma =
                  physicalBound (I.lower sigma) B.sampleData.n,
              ∃ hhi : ∀ sigma, B.sampleData.hi sigma =
                  physicalBound (I.upper sigma) B.sampleData.n,
              ∃ Rhead : HeadSimplexReserve (primesUpTo W),
              ∃ Kphysical : PhysicalInterpolationTarget I,
                Rhead.exponent = E ∧
                  (∀ p : {p : Nat // p ∈ primesUpTo W},
                    Rhead.target p = target p) ∧
                  F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar n =
                    Rhead.activeMass ∧
                  sourceCellMargin ≤ T.cellMassMargin ∧
                  T =
                    B.barycentricTargetOfPaperData
                      I hlo hhi Rhead Kphysical) ∧
          ∀ _hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            ∃ hsep :
                physicalBound (I.upper .minus) n <
                  physicalBound (I.lower .plus) n,
            ∃ hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
                (rawCell Patterns I n cell \ (G n).guards).Nonempty,
              B.sampleData =
                  canonicalSampleData
                    (W := W) Patterns I (G n) hsep hremaining ∧
                BankPaperCanonicalBridgeGuardAgreement
                  (G B.sampleData.n) R certificate deltaStar := by
    filter_upwards [
        Hmass, Hhead, Hsep, Hremaining, Hmesh, Hone,
        HupperBroad, HroughDepth, Hagreement, Halpha,
        HbetaProtRoom, Hresidual, eventually_secondOrderScale_pos,
        eventually_ge_atTop N, eventually_ge_atTop 2]
      with n hmassN hheadN hsepN hremainingN hmeshN honeN
        hupperBroadN hroughDepthN hagreementN halphaN
        hbetaProtRoomN hresidualN hscaleN hnTail hnTwo
    let D : StructuredSampleData (PaperHeadSimplex.Tag P) :=
      canonicalSampleData
        (W := W) Patterns I (G n) hsepN hremainingN
    have hnD : 1 < D.n := by
      simpa only [D, canonicalSampleData_n] using hnTwo
    have hWD : D.W ≠ 0 := by
      simpa only [D, canonicalSampleData_W] using Nat.ne_of_gt hW
    have S : ScaleSeparation M D.n D.W := by
      simpa only [D, canonicalSampleData_n, canonicalSampleData_W] using
        hmeshN
    have hlo :
        ∀ sigma, D.lo sigma =
          physicalBound (I.lower sigma) D.n := by
      intro sigma
      rfl
    have hhi :
        ∀ sigma, D.hi sigma =
          physicalBound (I.upper sigma) D.n := by
      intro sigma
      rfl
    let R := F.realization n hnTail
    let certificate := F.certificate n hnTail
    let qSource :=
      F.extendedGuardedSmoothBaseMass
        W (K0 + 1) betaAct deltaStar n
    let target : {p : Nat // p ∈ P} → Real :=
      fun p =>
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
            Real)
    have hqLower :
        cSource * secondOrderScale n ≤ qSource := by
      simpa only [qSource] using hmassN.1
    have hqUpper :
        qSource ≤ cUpper * secondOrderScale n := by
      simpa only [qSource] using hmassN.2
    have hquarterLe : cSource / 4 ≤ cSource := by
      nlinarith
    have hqLowerQuarter :
        (cSource / 4) * secondOrderScale n ≤ qSource :=
      (mul_le_mul_of_nonneg_right hquarterLe hscaleN.le).trans hqLower
    have hqPos : 0 < qSource :=
      (mul_pos hcSource hscaleN).trans_le hqLower
    have htargetLower :
        ∀ p, a p * secondOrderScale n ≤ target p := by
      intro p
      simpa only [a, target, P, R, certificate] using
        (hheadN hnTail p).1
    have htargetUpper :
        ∀ p, target p ≤ b p * secondOrderScale n := by
      intro p
      simpa only [b, target, P, R, certificate] using
        (hheadN hnTail p).2
    have hElarge' :
        2 * (∑ p : {p : Nat // p ∈ P}, b p) ≤
          (E : Real) * (cSource / 4) := by
      simpa only [P, b] using hElarge
    let margin :=
      bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper
    have hmargins :=
      bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
        E hE a b (cSource / 4) cUpper
        (secondOrderScale n) qSource target
        ha hb (by positivity) hcUpper hscaleN hqPos
        htargetLower htargetUpper hqLowerQuarter hqUpper hElarge'
    have hmarginPos : 0 < margin := by
      simpa only [margin] using hmargins.1
    have hvertex :
        ∀ p, margin ≤ target p / ((E : Real) * qSource) := by
      simpa only [margin] using hmargins.2.1
    have hzero :
        margin ≤
          1 - ∑ p : {p : Nat // p ∈ P},
            target p / ((E : Real) * qSource) := by
      simpa only [margin] using hmargins.2.2
    let Rhead : HeadSimplexReserve P :=
      bankPaperCanonicalSectionNineCoherentSourceHeadReserve
        E qSource target margin hE hqPos hmarginPos hvertex hzero
    let Kphysical :=
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
    let Tsource :=
      bankPaperCanonicalSectionNineCoherentSourceTarget
        M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
    let Bsource :=
      bankPaperCanonicalSectionNineCoherentSourceBridge
        M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
    let Z : RichFiber :=
      ⟨D, hnTail, hnD, hWD, S, hlo, hhi, Rhead⟩
    have hthin :
        thinOfRich Z =
          ⟨Bsource,
            ⟨⟨F.realization n hnTail, F.certificate n hnTail⟩,
              Tsource⟩⟩ := by
      rfl
    have hqActual :
        qSource =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar Bsource.sampleData.W
              (K0 + 1) betaAct := by
      simp only [
        qSource,
        BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
        dif_pos hnTail, R, certificate, Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_W]
    have hpattern :
        Bsource.sampleData.pattern =
          PaperHeadSimplex.pattern P hprime Rhead.exponent := by
      simp only [
        Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_pattern, Patterns, Rhead,
        bankPaperCanonicalSectionNineCoherentSourceHeadReserve_exponent]
    have hheadSeparated :
        Bsource.sampleData.HeadPatternsSeparated := by
      apply
        Erdos390.Full.PaperBridgeFit.StructuredSampleData.headPatternsSeparated_of_paperHeadSimplex
          P hprime E hE
      simp only [
        Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_pattern, Patterns]
    have hbounds :=
      bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
        Bsource I
          (by
            intro sigma
            simpa only [I] using
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
                sigma)
          (by
            intro sigma
            simpa only [I] using
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
                sigma)
          hlo hhi
    have hguardAgreement :
        BankPaperCanonicalBridgeGuardAgreement
          (G n) R certificate deltaStar := by
      simpa only [G, R, certificate] using
        hagreementN R certificate
    have hnotGuard :
        ∀ m : Bsource.sampleData.Sample,
          Bsource.sampleData.value m ∉
            R.roughCanonicalGuardSet certificate deltaStar := by
      intro m
      exact
        structuredSample_value_not_fullGuard_of_agreement
          Bsource.sampleData (G n) R certificate deltaStar
          hguardAgreement hbounds.2 (by rfl) m
    have hactiveSmooth :
        bankPaperCanonicalStructuredActiveValues Bsource.sampleData ⊆
          R.roughCanonicalGuardedRow
            certificate deltaStar (K0 + 1) 1 :=
      bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
        Bsource R certificate deltaStar I
          (by
            intro sigma
            simpa only [I] using
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
                sigma)
          (by
            intro sigma
            simpa only [I] using
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
                sigma)
          hlo hhi (by
            simpa only [
              Bsource,
              bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
              D, canonicalSampleData_n] using hroughDepthN)
          hnotGuard
    have halpha :
        bankPaperCanonicalPostHfitBalancedAlpha
            Bsource c K0 betaProt betaAct ∈ Set.Icc (0 : Real) 1 := by
      exact halphaN Bsource (by rfl) (by rfl)
    have hbetaBox :
        0 ≤ betaProt / Bsource.L ∧
          betaProt / Bsource.L ≤ 1 := by
      constructor
      · exact div_nonneg hbetaProt Bsource.L_pos.le
      · apply (div_le_iff₀ Bsource.L_pos).2
        simpa only [
          BridgeData.L, Bsource,
          bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
          D, canonicalSampleData_n, one_mul] using hbetaProtRoomN
    have hTsource :
        Tsource =
          Bsource.barycentricTargetOfPaperData
            I hlo hhi Rhead Kphysical := by
      exact
        bankPaperCanonicalSectionNineCoherentSourceTarget_eq_bridgeTarget
          M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
    have hsourceCellMargin :
        sourceCellMargin ≤ Tsource.cellMassMargin := by
      rw [hsourceCellMarginEq, hTsource,
        Bsource.barycentricTargetOfPaperData_cellMassMargin]
      exact le_rfl
    have hqRhead : qSource = Rhead.activeMass := by
      rfl
    have hheadSubset :
        primesUpTo Bsource.sampleData.W ⊆ P := by
      intro p hp
      simpa only [
        Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_W, P] using hp
    have htargetCompatibility :
        ∀ p : {p : Nat // p ∈ P},
          p.1 ≤ Bsource.sampleData.W →
            Rhead.target p =
              ((certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar)).factorization
                  p.1 : Real) := by
      intro p _hp
      rfl
    have hchargeDvd :
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget := by
      have h := hterminal n hnTail
      simpa only [R, certificate] using h.2.2.1
    have hresidual :
        BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
          (K := K0 + 1) Bsource R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          Tsource deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            (betaProt + betaAct) qSource := by
      apply
        hresidualN Bsource (by rfl) (by rfl)
          hsepN hremainingN (by rfl)
          R certificate Tsource qSource hqActual
          hprime Rhead Kphysical hlo hhi hTsource hqRhead
          hpattern hheadSubset hheadSeparated
      · intro sigma
        simpa only [I] using
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
            sigma
      · intro sigma
        simpa only [I] using
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
            sigma
      · simpa only [
          Bsource,
          bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
          D, canonicalSampleData_n] using hupperBroadN
      · simpa only [
          Bsource,
          bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
          D, canonicalSampleData_n] using hroughDepthN
      · exact hnotGuard
      · exact htargetCompatibility
      · exact hchargeDvd
    refine ⟨Z, ?_, ?_, ?_⟩
    · intro hn
      have hproof : hn = hnTail := Subsingleton.elim _ _
      subst hn
      rw [hthin]
      dsimp only
      refine
        ⟨rfl, rfl, ?_, ?_, hheadSeparated, hactiveSmooth,
          halpha, hbetaBox, hresidual, rfl⟩
      · simpa only [R, certificate] using hqActual
      · simpa only [qSource, qTilde] using honeN
    · intro _hn
      rw [hthin]
      dsimp only
      refine ⟨rfl, ?_, hWD, S, hlo, hhi, Rhead, Kphysical,
        rfl, ?_, rfl, hsourceCellMargin, hTsource⟩
      intro p
      simpa only [target, P, R, certificate] using hheadN hnTail p
      intro p
      rfl
    · intro _hn
      rw [hthin]
      dsimp only
      refine ⟨hsepN, hremainingN, rfl, ?_⟩
      simpa only [
        Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_n] using hguardAgreement
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp Hgood
  let Nsource := max N N₀
  have hgoodFrom :
      ∀ n, Nsource ≤ n →
        ∃ Z : RichFiber,
          (∀ hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            let T := X.2.2
            let alpha :=
              bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct
            let qSource :=
              F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n
            B.sampleData.n = n ∧
              B.sampleData.W = W ∧
              qSource =
                bankPaperCanonicalGuardedSmoothBaseMass
                  R certificate deltaStar B.sampleData.W
                    (K0 + 1) betaAct ∧
              1 ≤ qSource ∧
              B.sampleData.HeadPatternsSeparated ∧
              bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
                R.roughCanonicalGuardedRow
                  certificate deltaStar (K0 + 1) 1 ∧
              (0 ≤ alpha ∧ alpha ≤ 1) ∧
              (0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1) ∧
              BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
                (K := K0 + 1) B R certificate
                (R.paperFixedExceptionalFactors deltaStar)
                T deltaStar betaProt alpha
                  (betaProt + betaAct) qSource ∧
              certificate.prechargedTailTarget =
                (F.certificate n hn).prechargedTailTarget) ∧
          (∀ _hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            let T := X.2.2
            let target : {p : Nat // p ∈ primesUpTo W} → Real :=
              fun p =>
                ((certificate.selectorTailTarget R
                  (R.paperFixedExceptionalFactors
                    deltaStar)).factorization p.1 : Real)
            B.sampleData.n = n ∧
              (∀ p : {p : Nat // p ∈ primesUpTo W},
                bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
                      secondOrderScale n ≤
                    target p ∧
                  target p ≤
                    bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                        c p.1 *
                      secondOrderScale n) ∧
              ∃ _hWB : B.sampleData.W ≠ 0,
              ∃ _S : ScaleSeparation
                  M B.sampleData.n B.sampleData.W,
              ∃ hlo : ∀ sigma, B.sampleData.lo sigma =
                  physicalBound (I.lower sigma) B.sampleData.n,
              ∃ hhi : ∀ sigma, B.sampleData.hi sigma =
                  physicalBound (I.upper sigma) B.sampleData.n,
              ∃ Rhead : HeadSimplexReserve (primesUpTo W),
              ∃ Kphysical : PhysicalInterpolationTarget I,
                Rhead.exponent = E ∧
                  (∀ p : {p : Nat // p ∈ primesUpTo W},
                    Rhead.target p = target p) ∧
                  F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar n =
                    Rhead.activeMass ∧
                  sourceCellMargin ≤ T.cellMassMargin ∧
                  T =
                    B.barycentricTargetOfPaperData
                      I hlo hhi Rhead Kphysical) ∧
          ∀ _hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            ∃ hsep :
                physicalBound (I.upper .minus) n <
                  physicalBound (I.lower .plus) n,
            ∃ hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
                (rawCell Patterns I n cell \ (G n).guards).Nonempty,
              B.sampleData =
                  canonicalSampleData
                    (W := W) Patterns I (G n) hsep hremaining ∧
                BankPaperCanonicalBridgeGuardAgreement
                  (G B.sampleData.n) R certificate deltaStar := by
    intro n hn
    exact hN₀ n ((le_max_right N N₀).trans hn)
  choose genuine hgenuine using hgoodFrom
  let fallback : RichFiber :=
    genuine Nsource le_rfl
  let sourceGeom : ∀ n, N ≤ n → RichFiber := fun n _hn =>
    if h : Nsource ≤ n then genuine n h else fallback
  let source : ∀ n, N ≤ n → ThinFiber := fun n hn =>
    thinOfRich (sourceGeom n hn)
  refine ⟨sourceGeom, source, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rfl
  · filter_upwards [eventually_ge_atTop Nsource] with n hnLarge
    intro hn
    have hz : sourceGeom n hn = genuine n hnLarge := by
      simp only [sourceGeom, dif_pos hnLarge]
    have hs :
        source n hn = thinOfRich (genuine n hnLarge) := by
      simp only [source, hz]
    rw [hs]
    exact (hgenuine n hnLarge).1 hn
  · filter_upwards [eventually_ge_atTop Nsource] with n hnLarge
    intro hn
    have hz : sourceGeom n hn = genuine n hnLarge := by
      simp only [sourceGeom, dif_pos hnLarge]
    have hs :
        source n hn = thinOfRich (genuine n hnLarge) := by
      simp only [source, hz]
    rw [hs]
    exact (hgenuine n hnLarge).2.1 hn
  · filter_upwards [eventually_ge_atTop Nsource] with n hnLarge
    intro hn
    have hz : sourceGeom n hn = genuine n hnLarge := by
      simp only [sourceGeom, dif_pos hnLarge]
    have hs :
        source n hn = thinOfRich (genuine n hnLarge) := by
      simp only [source, hz]
    rw [hs]
    exact (hgenuine n hnLarge).2.2 hn

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal006_001 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceWithFixedNumericalData
