-- Prove2me | solution 1 for mme_stothers_general_support_entropy_eq_entropyProduct
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T05:26:03.5479+00:00
-- url     : https://prove2.me/submissions/9ecb0c33-88a4-4e90-bd3f-37d8a22f872d

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.GenEnt

/-- The ten class orbits partition the forty-five supported grade triples:
every triple lies in exactly one of them. -/
private theorem orbit_unique (sigma : GenHashSupportTriple) :
    (Finset.univ.filter
      (fun r : Fin 10 ↦ genSameOrbitExplicit sigma.1 (classRep r))).card = 1 := by
  revert sigma
  decide

/-- The orbit of class `r` inside the forty-five supported triples has size
`3 c_r`. -/
private theorem orbit_card (r : Fin 10) :
    (Finset.univ.filter
      (fun sigma : GenHashSupportTriple ↦
        genSameOrbitExplicit sigma.1 (classRep r))).card =
      3 * classMultiplicity r := by
  fin_cases r <;> decide

/-- Any function of the joint multiplicity table sums over the forty-five
supported triples to a class-weighted sum over the ten classes. -/
private theorem sum_transfer (base : Fin 10 → ℕ) (g : ℝ → ℝ) :
    (∑ sigma : GenHashSupportTriple,
        g ((genJointMultiplicity base 1 sigma.1 : ℕ) : ℝ)) =
      ∑ r : Fin 10, ((3 * classMultiplicity r : ℕ) : ℝ) * g ((base r : ℝ)) := by
  classical
  have hpt : ∀ sigma : GenHashSupportTriple,
      g ((genJointMultiplicity base 1 sigma.1 : ℕ) : ℝ) =
        ∑ r : Fin 10,
          if genSameOrbitExplicit sigma.1 (classRep r) then g ((base r : ℝ)) else 0 := by
    intro sigma
    obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp (orbit_unique sigma)
    have hJ : genJointMultiplicity base 1 sigma.1 = base r0 := by
      simp only [genJointMultiplicity, ← Finset.sum_filter]
      rw [hr0, Finset.sum_singleton, genProfileCount, mul_one]
    have hR :
        (∑ r : Fin 10,
          if genSameOrbitExplicit sigma.1 (classRep r) then g ((base r : ℝ)) else 0) =
          g ((base r0 : ℝ)) := by
      rw [← Finset.sum_filter, hr0, Finset.sum_singleton]
    rw [hJ, hR]
  rw [Finset.sum_congr rfl (fun sigma _ => hpt sigma), Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [← Finset.sum_filter, Finset.sum_const, orbit_card r]
  simp [nsmul_eq_mul]

private theorem scale_pos (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r) :
    0 < genProfileScale base := by
  have h0 : 0 < classMultiplicity 0 * base 0 := by
    have hb := hbase 0
    have hc : classMultiplicity 0 = 1 := by decide
    rw [hc]
    omega
  exact Finset.sum_pos' (fun r _ => Nat.zero_le _) ⟨0, Finset.mem_univ 0, h0⟩

private theorem profileB_pos (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r)
    (r : Fin 10) : 0 < genProfileB base r := by
  have hD : (0 : ℝ) < (genProfileScale base : ℝ) := by
    exact_mod_cast scale_pos base hbase
  have : (0 : ℝ) < (base r : ℝ) := by exact_mod_cast hbase r
  simpa only [genProfileB] using div_pos this hD

private theorem class_weights_sum_one (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r) :
    (∑ r : Fin 10, (classMultiplicity r : ℝ) * genProfileB base r) = 1 := by
  have hD : (0 : ℝ) < (genProfileScale base : ℝ) := by
    exact_mod_cast scale_pos base hbase
  have hstep : (∑ r : Fin 10, (classMultiplicity r : ℝ) * genProfileB base r) =
      (∑ r : Fin 10, ((classMultiplicity r * base r : ℕ) : ℝ)) /
        (genProfileScale base : ℝ) := by
    simp only [genProfileB, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro r _
    push_cast
    ring
  rw [hstep, div_eq_one_iff_eq hD.ne']
  rw [← Nat.cast_sum]
  rfl

private theorem log_entropyProduct (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r) :
    Real.log (entropyProduct (genProfileB base)) =
      ∑ r : Fin 10,
        ((classMultiplicity r : ℝ) * genProfileB base r) *
          Real.log (genProfileB base r) := by
  simp only [entropyProduct]
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro r _
    exact Real.log_rpow (profileB_pos base hbase r) _
  · intro r _
    exact (Real.rpow_pos_of_pos (profileB_pos base hbase r) _).ne'

end MME.StothersFourth.GenEnt

open MME.StothersFourth.GenEnt

theorem solution
    (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r) :
    Real.log 2 *
        mme_modern_entropyBits
          (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
            (MME.StothersFourth.genHashTargetJointTable base 1 sigma : ℝ) /
              (MME.StothersFourth.genOuterLength base 1 : ℝ)) =
      Real.log 3 -
        Real.log (MME.StothersFourth.entropyProduct
          (MME.StothersFourth.genProfileB base)) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hDpos : (0 : ℝ) < (MME.StothersFourth.genProfileScale base : ℝ) := by
    exact_mod_cast scale_pos base hbase
  have hlen : ((MME.StothersFourth.genOuterLength base 1 : ℕ) : ℝ) =
      3 * (MME.StothersFourth.genProfileScale base : ℝ) := by
    simp only [MME.StothersFourth.genOuterLength]
    push_cast
    ring
  set D : ℝ := (MME.StothersFourth.genProfileScale base : ℝ) with hDdef
  have step1 :
      Real.log 2 * mme_modern_entropyBits
          (fun sigma : MME.StothersFourth.GenHashSupportTriple ↦
            (MME.StothersFourth.genHashTargetJointTable base 1 sigma : ℝ) /
              (MME.StothersFourth.genOuterLength base 1 : ℝ)) =
        ∑ sigma : MME.StothersFourth.GenHashSupportTriple,
          Real.negMulLog
            (((MME.StothersFourth.genJointMultiplicity base 1 sigma.1 : ℕ) : ℝ) /
              (3 * D)) := by
    simp only [mme_modern_entropyBits,
      MME.StothersFourth.genHashTargetJointTable, hlen]
    field_simp
  have step2 :=
    sum_transfer base (fun x ↦ Real.negMulLog (x / (3 * D)))
  have hterm : ∀ r : Fin 10,
      ((3 * MME.StothersFourth.classMultiplicity r : ℕ) : ℝ) *
          Real.negMulLog ((base r : ℝ) / (3 * D)) =
        (MME.StothersFourth.classMultiplicity r : ℝ) *
            MME.StothersFourth.genProfileB base r * Real.log 3 -
          ((MME.StothersFourth.classMultiplicity r : ℝ) *
            MME.StothersFourth.genProfileB base r) *
            Real.log (MME.StothersFourth.genProfileB base r) := by
    intro r
    have hbr : (0 : ℝ) < MME.StothersFourth.genProfileB base r :=
      profileB_pos base hbase r
    have hsplit : (base r : ℝ) / (3 * D) =
        MME.StothersFourth.genProfileB base r / 3 := by
      simp only [MME.StothersFourth.genProfileB, hDdef]
      field_simp
    rw [hsplit, Real.negMulLog, Real.log_div hbr.ne' (by norm_num)]
    push_cast
    ring
  have hsum :
      (∑ sigma : MME.StothersFourth.GenHashSupportTriple,
        Real.negMulLog
          (((MME.StothersFourth.genJointMultiplicity base 1 sigma.1 : ℕ) : ℝ) /
            (3 * D))) =
        Real.log 3 -
          Real.log (MME.StothersFourth.entropyProduct
            (MME.StothersFourth.genProfileB base)) := by
    rw [step2, Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_sub_distrib,
      ← Finset.sum_mul, class_weights_sum_one base hbase, one_mul,
      ← log_entropyProduct base hbase]
  rw [step1, hsum]
