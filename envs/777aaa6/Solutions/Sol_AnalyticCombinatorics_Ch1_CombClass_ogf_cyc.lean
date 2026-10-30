-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.ogf_cyc
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:42.286125+00:00
-- url     : https://prove2.me/submissions/5042dfae-d051-496f-84c2-e307860398f9

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_CycleOGF
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.Rat
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.1 — Combinatorial classes and ordinary generating functions

A faithful encoding of Flajolet & Sedgewick, *Analytic Combinatorics*, Part A,
Chapter I, §I.1. A combinatorial class is a set of objects equipped with a size
function such that only finitely many objects have any given size. We encode it
as a graded family of finite types `Obj : ℕ → Type`, where `Obj n` is the set of
objects of size `n`. Its counting sequence is `Aₙ = #(Obj n)`, and its *ordinary
generating function* (OGF) is `A(z) = ∑ₙ Aₙ zⁿ`, here a formal power series over
`ℚ`.

This file defines the OGF, the `CombClass` structure, and the three primitive
classes (empty `∅`, neutral `ε`, atom `Z`) with their counting sequences and
generating functions `ε(z) = 1`, `Z(z) = z`. The admissible constructions (sum,
product, sequence) and their transfer theorems live in sibling files.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_ogfSeq (a : ℕ → ℕ) (n : ℕ) : coeff n (ogfSeq a) = (a n : ℚ) := by
  rw [ogfSeq, coeff_mk]

attribute [instance] CombClass.finObj

@[simp] lemma CombClass.coeff_ogf (C : CombClass) (n : ℕ) :
    coeff n C.ogf = (C.counts n : ℚ) := by
  rw [CombClass.ogf, coeff_ogfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2 — Cycle model, fixed-point layer

This file builds the bounded word model for cycles and proves the fixed-point
cardinality used by Burnside in the next layer.
-/

namespace AnalyticCombinatorics.Ch1

open scoped BigOperators

universe u

lemma addOrderOf_eq_k_div_gcd_val
    (k : ℕ) [NeZero k] (a : ZMod k) :
    addOrderOf a = k / k.gcd a.val := by
  calc
    addOrderOf a = addOrderOf (a.val : ZMod k) := by
      rw [ZMod.natCast_zmod_val]
    _ = k / k.gcd a.val := ZMod.addOrderOf_coe a.val (NeZero.ne k)

lemma card_quotient_zmultiples_eq_gcd
    (k : ℕ) [NeZero k] (a : ZMod k) :
    Fintype.card (ZMod k ⧸ AddSubgroup.zmultiples a) = k.gcd a.val := by
  classical
  let Q := ZMod k ⧸ AddSubgroup.zmultiples a
  have hcard :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (AddSubgroup.zmultiples a)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_zmultiples, ZMod.card, addOrderOf_eq_k_div_gcd_val] at hcard
  have hg : k.gcd a.val ∣ k := Nat.gcd_dvd_left k a.val
  have hk : k.gcd a.val * (k / k.gcd a.val) = k :=
    Nat.mul_div_cancel' hg
  have hdpos : 0 < k / k.gcd a.val := by
    rw [← addOrderOf_eq_k_div_gcd_val k a]
    exact addOrderOf_pos a
  apply Nat.eq_of_mul_eq_mul_right hdpos
  exact hcard.symm.trans hk.symm

lemma fixedBy_rotation_isEmpty_of_not_dvd
    (C : CombClass) (n k : ℕ) [NeZero k] (a : ZMod k)
    (hndiv : ¬ addOrderOf a ∣ n) :
    IsEmpty (AddAction.fixedBy (Word C n k) a) := by
  refine ⟨fun w => ?_⟩
  have qf := (fixedBy_rotation_equiv_quotientRaw C n k a) w
  exact hndiv
    ⟨∑ q : ZMod k ⧸ AddSubgroup.zmultiples a, compSize (qf.1 q), qf.2.symm⟩

lemma card_fixedBy_rotation
    (C : CombClass) (n k : ℕ) [NeZero k] (a : ZMod k) :
    Fintype.card (AddAction.fixedBy (Word C n k) a) =
      if _h : addOrderOf a ∣ n then
        Fintype.card
          (BlockWord C (n / addOrderOf a) (k.gcd a.val))
      else 0 := by
  classical
  by_cases h : addOrderOf a ∣ n
  · rw [dif_pos h]
    calc
      Fintype.card (AddAction.fixedBy (Word C n k) a) =
          Fintype.card
            (WordOn C (n / addOrderOf a)
              (ZMod k ⧸ AddSubgroup.zmultiples a)) := by
        exact Fintype.card_congr
          (fixedBy_rotation_equiv_word_quotient C n k a h)
      _ = Fintype.card
          (BlockWord C (n / addOrderOf a) (k.gcd a.val)) := by
        exact Fintype.card_congr
          (wordOn_equiv_fin_of_card C (n / addOrderOf a) (k.gcd a.val)
            (card_quotient_zmultiples_eq_gcd k a))
  · rw [dif_neg h]
    haveI : IsEmpty (AddAction.fixedBy (Word C n k) a) :=
      fixedBy_rotation_isEmpty_of_not_dvd C n k a h
    exact Fintype.card_eq_zero

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2 — Cycle Burnside layer

This file assembles the per-length Burnside count and groups rotations by
their gcd with the cycle length.
-/

namespace AnalyticCombinatorics.Ch1

open scoped BigOperators

lemma burnside_necklaces_k
    (C : CombClass) (n k : ℕ) [NeZero k] :
    k * Fintype.card (necklaces_k C n k) =
      ∑ a : ZMod k, Fintype.card (AddAction.fixedBy (Word C n k) a) := by
  classical
  have h :=
    AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
      (ZMod k) (Word C n k)
  rw [ZMod.card] at h
  rw [mul_comm]
  exact h.symm

lemma sum_zmod_by_gcd
    (k : ℕ) [NeZero k] (F : ℕ → ℕ) :
    (∑ a : ZMod k, F (k.gcd a.val)) =
      ∑ g ∈ k.divisors, Nat.totient (k / g) * F g := by
  classical
  have hzmod_fin :
      (∑ a : ZMod k, F (k.gcd a.val)) =
        ∑ i : Fin k, F (k.gcd i.val) := by
    cases k with
    | zero =>
        exact (NeZero.ne 0 rfl).elim
    | succ _ =>
        rfl
  have hfin_range :
      (∑ i : Fin k, F (k.gcd i.val)) =
        ∑ i ∈ Finset.range k, F (k.gcd i) := by
    refine
      (Finset.sum_fin_eq_sum_range
        (fun i : Fin k => F (k.gcd i.val))).trans ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  have hmaps : ∀ i ∈ Finset.range k, k.gcd i ∈ k.divisors := by
    intro i _hi
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left k i, NeZero.ne k⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := Finset.range k) (t := k.divisors)
      (g := fun i : ℕ => k.gcd i) hmaps
      (fun i : ℕ => F (k.gcd i))
  calc
    (∑ a : ZMod k, F (k.gcd a.val)) =
        ∑ i ∈ Finset.range k, F (k.gcd i) :=
      hzmod_fin.trans hfin_range
    _ = ∑ g ∈ k.divisors, Nat.totient (k / g) * F g := by
      rw [← hfiber]
      refine Finset.sum_congr rfl ?_
      intro g hg
      calc
        (∑ i ∈ Finset.range k with k.gcd i = g, F (k.gcd i)) =
            ∑ i ∈ Finset.range k with k.gcd i = g, F g := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact congrArg F (Finset.mem_filter.mp hi).2
        _ = (Finset.filter (fun i => k.gcd i = g) (Finset.range k)).card * F g := by
          simp
        _ = Nat.totient (k / g) * F g := by
          rw [← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hg)]

lemma counts_necklaces_k
    (C : CombClass) (n k : ℕ) [NeZero k] :
    k * Fintype.card (necklaces_k C n k) =
      ∑ g ∈ k.divisors,
        if k / g ∣ n then
          Nat.totient (k / g) *
            Fintype.card (BlockWord C (n / (k / g)) g)
        else 0 := by
  classical
  let F : ℕ → ℕ := fun g =>
    if k / g ∣ n then
      Fintype.card (BlockWord C (n / (k / g)) g)
    else 0
  calc
    k * Fintype.card (necklaces_k C n k) =
        ∑ a : ZMod k, Fintype.card (AddAction.fixedBy (Word C n k) a) :=
      burnside_necklaces_k C n k
    _ = ∑ a : ZMod k, F (k.gcd a.val) := by
      refine Finset.sum_congr rfl ?_
      intro a _ha
      simp [F, card_fixedBy_rotation, addOrderOf_eq_k_div_gcd_val]
    _ = ∑ g ∈ k.divisors,
        if k / g ∣ n then
          Nat.totient (k / g) *
            Fintype.card (BlockWord C (n / (k / g)) g)
        else 0 := by
      simpa [F, mul_ite] using (sum_zmod_by_gcd k F)

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2 — The cycle construction OGF layer

This file connects the Burnside count for cycle necklaces to the ordinary
generating function identity

  `CYC(C)(z) = ∑_{d ≥ 1} φ(d)/d * mlog(C(z^d))`.
-/

namespace AnalyticCombinatorics.Ch1

open scoped BigOperators PowerSeries.WithPiTopology
open PowerSeries
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatCycleOGF

local instance instDiscRatCycleOGF : DiscreteTopology ℚ := ⟨rfl⟩

lemma card_blockWord_eq_coeff_pow
    (C : CombClass) (m g : ℕ) :
    (Fintype.card (BlockWord C m g) : ℚ) =
      PowerSeries.coeff m (C.ogf ^ g) := by
  classical
  let B := { l : Fin g → ℕ // ∑ i, l i = m }
  let A := (Finset.range g).finsuppAntidiag m
  letI : Fintype B := Fintype.ofEquiv A (finsuppAntidiagRangeEquivFin m g)
  have hcard :
      (Fintype.card (BlockWord C m g) : ℚ) =
        ∑ l : B, ∏ i : Fin g, (C.counts (l.1 i) : ℚ) := by
    rw [Fintype.card_congr (blockWordSigmaEquiv C m g)]
    rw [Fintype.card_sigma, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro l _hl
    rw [Fintype.card_pi, Nat.cast_prod]
    refine Finset.prod_congr rfl ?_
    intro i _hi
    simp [CombClass.counts]
  rw [hcard, PowerSeries.coeff_pow]
  have hreindex :
      (∑ l : B, ∏ i : Fin g, (C.counts (l.1 i) : ℚ)) =
        ∑ a : A, ∏ i ∈ Finset.range g, PowerSeries.coeff (a.1 i) C.ogf := by
    exact Fintype.sum_equiv (finsuppAntidiagRangeEquivFin m g).symm
      (fun l : B => ∏ i : Fin g, (C.counts (l.1 i) : ℚ))
      (fun a : A => ∏ i ∈ Finset.range g, PowerSeries.coeff (a.1 i) C.ogf) (by
    intro l
    calc
      (∏ i : Fin g, (C.counts (l.1 i) : ℚ)) =
          ∏ i : Fin g,
            PowerSeries.coeff (((finsuppAntidiagRangeEquivFin m g).symm l).1 i.val) C.ogf := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            rw [CombClass.coeff_ogf]
            simp [finsuppAntidiagRangeEquivFin]
      _ = ∏ i ∈ Finset.range g,
          PowerSeries.coeff (((finsuppAntidiagRangeEquivFin m g).symm l).1 i) C.ogf := by
            exact Fin.prod_univ_eq_prod_range
              (fun i => PowerSeries.coeff (((finsuppAntidiagRangeEquivFin m g).symm l).1 i) C.ogf) g)
  rw [hreindex]
  simpa [A, Finset.univ_eq_attach] using
    (Finset.sum_attach A (fun a : ℕ →₀ ℕ => ∏ i ∈ Finset.range g,
      PowerSeries.coeff (a i) C.ogf))

lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {f : ℚ⟦X⟧} (hf0 : f.constantCoeff = 0)
    {n p : ℕ} (hnp : n < p) :
    PowerSeries.coeff n (f ^ p) = 0 := by
  exact PowerSeries.coeff_of_lt_order n
    (lt_of_lt_of_le (ENat.coe_lt_coe.mpr hnp)
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero p hf0))

lemma summable_mlog_terms
    {f : ℚ⟦X⟧} (hf0 : f.constantCoeff = 0) :
    Summable fun j : ℕ => (((j + 1 : ℕ) : ℚ)⁻¹) • f ^ (j + 1) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr
    (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro j hj
  exact lt_of_lt_of_le
    (ENat.coe_lt_coe.mpr (Nat.lt_succ_of_le hj))
    ((PowerSeries.le_order_pow_of_constantCoeff_eq_zero (j + 1) hf0).trans
      PowerSeries.le_order_smul)

lemma coeff_mlog
    {f : ℚ⟦X⟧} (hf0 : f.constantCoeff = 0) (n : ℕ) :
    PowerSeries.coeff n (mlog f) =
      ∑ j ∈ Finset.range n,
        (((j + 1 : ℕ) : ℚ)⁻¹) *
          PowerSeries.coeff n (f ^ (j + 1)) := by
  classical
  have hs := summable_mlog_terms hf0
  rw [mlog, hs.map_tsum _ (PowerSeries.WithPiTopology.continuous_coeff ℚ n)]
  rw [tsum_eq_sum (s := Finset.range n)]
  · refine Finset.sum_congr rfl ?_
    intro j _hj
    simp [map_smul]
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    simp [map_smul, coeff_pow_eq_zero_of_constantCoeff_eq_zero hf0
      (Nat.lt_succ_of_le hj)]

lemma coeff_mlog_subst_X_pow
    (C : CombClass) (hC0 : C.counts 0 = 0)
    {d n : ℕ} (hd : d ≠ 0) :
    PowerSeries.coeff n
        (mlog (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ d) C.ogf)) =
      if _hdn : d ∣ n then
        ∑ j ∈ Finset.range (n / d),
          (((j + 1 : ℕ) : ℚ)⁻¹) *
            (Fintype.card (BlockWord C (n / d) (j + 1)) : ℚ)
      else
        0 := by
  classical
  have hCcoeff0 : C.ogf.constantCoeff = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [CombClass.coeff_ogf, hC0]
    norm_num
  have hsubst0 :
      (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ d) C.ogf).constantCoeff = 0 := by
    set_option backward.isDefEq.respectTransparency false in
      change PowerSeries.constantCoeff
        (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ d) C.ogf) = 0
      exact PowerSeries.constantCoeff_subst_eq_zero
        (by
          rw [map_pow]
          change PowerSeries.constantCoeff (PowerSeries.X : ℚ⟦X⟧) ^ d = 0
          rw [PowerSeries.constantCoeff_X, zero_pow hd]) C.ogf hCcoeff0
  have hcoeff (j : ℕ) :
      PowerSeries.coeff n
          ((PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ d) C.ogf) ^ (j + 1)) =
        if _hdn : d ∣ n then
          PowerSeries.coeff (n / d) (C.ogf ^ (j + 1))
        else
          0 := by
    set_option backward.isDefEq.respectTransparency false in
      have hsubst (f : ℚ⟦X⟧) (m : ℕ) :
          PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ d) f) =
            if d ∣ m then algebraMap ℚ ℚ (PowerSeries.coeff (m / d) f) else 0 := by
        -- Canonical Mathlib 8a178386 PowerSeries.coeff_subst_X_pow proof,
        -- specialized here to ℚ; Apache-2.0 source retained in candidate evidence.
        split_ifs with h
        · rw [PowerSeries.coeff_subst' (.X_pow hd), finsum_eq_single _ (m / d),
            ← pow_mul, Nat.mul_div_cancel' h, PowerSeries.coeff_X_pow_self,
            Algebra.algebraMap_eq_smul_one]
          intro k hk
          rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
          contrapose! hk
          rw [hk, Nat.mul_div_cancel_left k hd.pos]
        · rw [PowerSeries.coeff_subst' (.X_pow hd), finsum_eq_zero_of_forall_eq_zero]
          intro k
          rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
          contrapose! h
          use k
      rw [← PowerSeries.subst_pow
        (PowerSeries.HasSubst.X_pow (R := ℚ) hd) C.ogf (j + 1)]
      rw [hsubst (C.ogf ^ (j + 1)) n]
      split_ifs <;> simp
  rw [coeff_mlog hsubst0 n]
  by_cases hdn : d ∣ n
  · rw [dif_pos hdn]
    have hle_div : n / d ≤ n := Nat.div_le_self n d
    have hsubset : Finset.range (n / d) ⊆ Finset.range n := by
      intro j hj
      exact Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hle_div)
    calc
      (∑ j ∈ Finset.range n,
          (((j + 1 : ℕ) : ℚ)⁻¹) *
              PowerSeries.coeff n
              ((PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ d) C.ogf) ^ (j + 1))) =
          ∑ j ∈ Finset.range n,
            (((j + 1 : ℕ) : ℚ)⁻¹) *
              PowerSeries.coeff (n / d) (C.ogf ^ (j + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [hcoeff j, dif_pos hdn]
      _ = ∑ j ∈ Finset.range (n / d),
            (((j + 1 : ℕ) : ℚ)⁻¹) *
              PowerSeries.coeff (n / d) (C.ogf ^ (j + 1)) := by
            refine (Finset.sum_subset hsubset ?_).symm
            intro j hj hjsmall
            rw [Finset.mem_range, not_lt] at hjsmall
            have hz : PowerSeries.coeff (n / d) (C.ogf ^ (j + 1)) = 0 :=
              coeff_pow_eq_zero_of_constantCoeff_eq_zero hCcoeff0
                (Nat.lt_succ_of_le hjsmall)
            simp [hz]
      _ = ∑ j ∈ Finset.range (n / d),
            (((j + 1 : ℕ) : ℚ)⁻¹) *
              (Fintype.card (BlockWord C (n / d) (j + 1)) : ℚ) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [← card_blockWord_eq_coeff_pow C (n / d) (j + 1)]
  · rw [dif_neg hdn]
    refine Finset.sum_eq_zero ?_
    intro j _hj
    rw [hcoeff j, dif_neg hdn]
    simp

lemma counts_cyc_rational_formula
    (C : CombClass) (hC0 : C.counts 0 = 0)
    {n : ℕ} (hn : n ≠ 0) :
    (C.cyc.counts n : ℚ) =
      ∑ d ∈ n.divisors,
        ((Nat.totient d : ℚ) / (d : ℚ)) *
          ∑ j ∈ Finset.Icc 1 (n / d),
            ((j : ℚ)⁻¹) *
              (Fintype.card (BlockWord C (n / d) j) : ℚ) := by
  classical
  have _hC0_used : C.counts 0 = 0 := hC0
  let K := Finset.Icc 1 n
  let S : Finset (Σ _k : K, ℕ) :=
    (Finset.univ : Finset K).sigma (fun k => k.1.divisors)
  let S₀ : Finset (Σ _k : K, ℕ) :=
    S.filter (fun x => x.1.1 / x.2 ∣ n)
  let T : Finset (Σ _d : ℕ, ℕ) :=
    n.divisors.sigma (fun d => Finset.Icc 1 (n / d))
  let sTerm : (Σ _k : K, ℕ) → ℚ := fun x =>
    ((x.1.1 : ℚ)⁻¹) *
      ((Nat.totient (x.1.1 / x.2) : ℚ) *
        (Fintype.card (BlockWord C (n / (x.1.1 / x.2)) x.2) : ℚ))
  let tTerm : (Σ _d : ℕ, ℕ) → ℚ := fun x =>
    ((Nat.totient x.1 : ℚ) / (x.1 : ℚ)) *
      (((x.2 : ℚ)⁻¹) *
        (Fintype.card (BlockWord C (n / x.1) x.2) : ℚ))
  let neckCard : K → ℚ := fun k =>
    letI : NeZero k.1 :=
      ⟨Nat.ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp k.2).1)⟩
    (Fintype.card (necklaces_k C n k.1) : ℚ)
  have hneck (k : K) :
      neckCard k =
        ((k.1 : ℚ)⁻¹) *
          ∑ g ∈ k.1.divisors,
            if k.1 / g ∣ n then
              (Nat.totient (k.1 / g) : ℚ) *
                (Fintype.card (BlockWord C (n / (k.1 / g)) g) : ℚ)
            else 0 := by
    have hkpos : 0 < k.1 :=
      Nat.succ_le_iff.mp (Finset.mem_Icc.mp k.2).1
    letI : NeZero k.1 := ⟨Nat.ne_of_gt hkpos⟩
    have hraw := congrArg (fun x : ℕ => (x : ℚ))
      (counts_necklaces_k C n k.1)
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] at hraw
    have hkq : (k.1 : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hkpos)
    calc
      (Fintype.card (necklaces_k C n k.1) : ℚ) =
          (k.1 : ℚ)⁻¹ *
            ((k.1 : ℚ) * (Fintype.card (necklaces_k C n k.1) : ℚ)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hkq, one_mul]
      _ = (k.1 : ℚ)⁻¹ *
          ∑ g ∈ k.1.divisors,
            if k.1 / g ∣ n then
              (Nat.totient (k.1 / g) : ℚ) *
                (Fintype.card (BlockWord C (n / (k.1 / g)) g) : ℚ)
            else 0 := by
            rw [hraw]
  have hcard :
      (C.cyc.counts n : ℚ) =
        ∑ k : K, neckCard k := by
    rw [CombClass.counts]
    change (Fintype.card
      (Σ k : K,
        letI : NeZero k.1 :=
          ⟨Nat.ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp k.2).1)⟩
        necklaces_k C n k.1) : ℚ) =
      ∑ k : K, neckCard k
    rw [Fintype.card_sigma, Nat.cast_sum]
  have hreindex :
      ∑ x ∈ S₀, sTerm x = ∑ x ∈ T, tTerm x := by
    refine Finset.sum_bij'
      (fun x _hx => ⟨x.1.1 / x.2, x.2⟩)
      (fun x hx =>
        ⟨⟨x.2 * x.1, by
            have hxdvd : x.1 ∣ n := Nat.dvd_of_mem_divisors
              (Finset.mem_sigma.mp hx).1
            have hxpos : 0 < x.1 :=
              Nat.pos_of_dvd_of_pos hxdvd (Nat.pos_of_ne_zero hn)
            have hxj := Finset.mem_Icc.mp (Finset.mem_sigma.mp hx).2
            have hxjpos : 0 < x.2 := Nat.succ_le_iff.mp hxj.1
            have hmul_le : x.2 * x.1 ≤ n :=
              (Nat.le_div_iff_mul_le hxpos).mp hxj.2
            exact Finset.mem_Icc.mpr
              ⟨Nat.succ_le_iff.mpr (Nat.mul_pos hxjpos hxpos), hmul_le⟩⟩,
          x.2⟩) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hxS := (Finset.mem_filter.mp hx).1
      have hdiv : x.1.1 / x.2 ∣ n := (Finset.mem_filter.mp hx).2
      have hgmem : x.2 ∈ x.1.1.divisors := (Finset.mem_sigma.mp hxS).2
      have hgdvd : x.2 ∣ x.1.1 := Nat.dvd_of_mem_divisors hgmem
      have hkpos : 0 < x.1.1 :=
        Nat.succ_le_iff.mp (Finset.mem_Icc.mp x.1.2).1
      have hgpos : 0 < x.2 :=
        Nat.pos_of_dvd_of_pos hgdvd hkpos
      have hdpos : 0 < x.1.1 / x.2 :=
        Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hn)
      refine Finset.mem_sigma.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdiv, hn⟩, ?_⟩
      refine Finset.mem_Icc.mpr
        ⟨Nat.succ_le_iff.mpr hgpos, ?_⟩
      have hk_le_n : x.1.1 ≤ n := (Finset.mem_Icc.mp x.1.2).2
      have hmul : x.2 * (x.1.1 / x.2) = x.1.1 := by
        rw [mul_comm, Nat.div_mul_cancel hgdvd]
      exact (Nat.le_div_iff_mul_le hdpos).mpr (by simpa [hmul] using hk_le_n)
    · intro x hx
      have hxT := Finset.mem_sigma.mp hx
      have hxdvd : x.1 ∣ n := Nat.dvd_of_mem_divisors hxT.1
      have hxpos : 0 < x.1 :=
        Nat.pos_of_dvd_of_pos hxdvd (Nat.pos_of_ne_zero hn)
      have hxj := Finset.mem_Icc.mp hxT.2
      have hxjpos : 0 < x.2 := Nat.succ_le_iff.mp hxj.1
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩
        refine Nat.mem_divisors.mpr ⟨dvd_mul_right x.2 x.1, ?_⟩
        exact Nat.ne_of_gt (Nat.mul_pos hxjpos hxpos)
      · simpa [Nat.mul_div_right x.1 hxjpos] using hxdvd
    · intro x hx
      have hxS := (Finset.mem_filter.mp hx).1
      have hgmem : x.2 ∈ x.1.1.divisors := (Finset.mem_sigma.mp hxS).2
      have hgdvd : x.2 ∣ x.1.1 := Nat.dvd_of_mem_divisors hgmem
      apply Sigma.ext
      · apply Subtype.ext
        change x.2 * (x.1.1 / x.2) = x.1.1
        rw [mul_comm, Nat.div_mul_cancel hgdvd]
      · simp
    · intro x hx
      have hxT := Finset.mem_sigma.mp hx
      have hxdvd : x.1 ∣ n := Nat.dvd_of_mem_divisors hxT.1
      have hxpos : 0 < x.1 :=
        Nat.pos_of_dvd_of_pos hxdvd (Nat.pos_of_ne_zero hn)
      have hxj := Finset.mem_Icc.mp hxT.2
      have hxjpos : 0 < x.2 := Nat.succ_le_iff.mp hxj.1
      apply Sigma.ext
      · exact Nat.mul_div_right x.1 hxjpos
      · simp
    · intro x hx
      have hxS := (Finset.mem_filter.mp hx).1
      have hdiv : x.1.1 / x.2 ∣ n := (Finset.mem_filter.mp hx).2
      have hgmem : x.2 ∈ x.1.1.divisors := (Finset.mem_sigma.mp hxS).2
      have hgdvd : x.2 ∣ x.1.1 := Nat.dvd_of_mem_divisors hgmem
      have hkpos : 0 < x.1.1 :=
        Nat.succ_le_iff.mp (Finset.mem_Icc.mp x.1.2).1
      have hgpos : 0 < x.2 :=
        Nat.pos_of_dvd_of_pos hgdvd hkpos
      have hdpos : 0 < x.1.1 / x.2 :=
        Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hn)
      have hk_eq : (x.1.1 : ℚ) = (x.2 : ℚ) * ((x.1.1 / x.2 : ℕ) : ℚ) := by
        rw [← Nat.cast_mul]
        congr 1
        rw [mul_comm, Nat.div_mul_cancel hgdvd]
      dsimp [sTerm, tTerm]
      rw [hk_eq]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hgpos),
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt hdpos)]
  calc
    (C.cyc.counts n : ℚ) =
        ∑ k : K, neckCard k := hcard
    _ = ∑ k : K,
        ((k.1 : ℚ)⁻¹) *
          ∑ g ∈ k.1.divisors,
            if k.1 / g ∣ n then
              (Nat.totient (k.1 / g) : ℚ) *
                (Fintype.card (BlockWord C (n / (k.1 / g)) g) : ℚ)
            else 0 := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          exact hneck k
    _ = ∑ k : K, ∑ g ∈ k.1.divisors,
        ((k.1 : ℚ)⁻¹) *
          (if k.1 / g ∣ n then
            (Nat.totient (k.1 / g) : ℚ) *
              (Fintype.card (BlockWord C (n / (k.1 / g)) g) : ℚ)
          else 0) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          rw [Finset.mul_sum]
    _ = ∑ x ∈ S,
        ((x.1.1 : ℚ)⁻¹) *
          (if x.1.1 / x.2 ∣ n then
            (Nat.totient (x.1.1 / x.2) : ℚ) *
              (Fintype.card (BlockWord C (n / (x.1.1 / x.2)) x.2) : ℚ)
          else 0) := by
          dsimp [S]
          rw [Finset.sum_sigma']
    _ = ∑ x ∈ S₀, sTerm x := by
          dsimp [S₀, sTerm]
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro x hx
          by_cases hdiv : x.1.1 / x.2 ∣ n <;> simp [hdiv]
    _ = ∑ x ∈ T, tTerm x := hreindex
    _ = ∑ d ∈ n.divisors,
        ((Nat.totient d : ℚ) / (d : ℚ)) *
          ∑ j ∈ Finset.Icc 1 (n / d),
            ((j : ℚ)⁻¹) *
              (Fintype.card (BlockWord C (n / d) j) : ℚ) := by
          dsimp [T, tTerm]
          calc
            (∑ x ∈ n.divisors.sigma (fun d => Finset.Icc 1 (n / d)),
                ((Nat.totient x.1 : ℚ) / (x.1 : ℚ)) *
                  (((x.2 : ℚ)⁻¹) *
                    (Fintype.card (BlockWord C (n / x.1) x.2) : ℚ))) =
                ∑ d ∈ n.divisors, ∑ j ∈ Finset.Icc 1 (n / d),
                  ((Nat.totient d : ℚ) / (d : ℚ)) *
                    (((j : ℚ)⁻¹) *
                      (Fintype.card (BlockWord C (n / d) j) : ℚ)) := by
                  exact (Finset.sum_sigma' n.divisors
                    (fun d => Finset.Icc 1 (n / d))
                    (fun d j =>
                      ((Nat.totient d : ℚ) / (d : ℚ)) *
                        (((j : ℚ)⁻¹) *
                          (Fintype.card (BlockWord C (n / d) j) : ℚ)))).symm
            _ = ∑ d ∈ n.divisors,
                ((Nat.totient d : ℚ) / (d : ℚ)) *
                  ∑ j ∈ Finset.Icc 1 (n / d),
                    ((j : ℚ)⁻¹) *
                      (Fintype.card (BlockWord C (n / d) j) : ℚ) := by
                  refine Finset.sum_congr rfl ?_
                  intro d _hd
                  rw [← Finset.mul_sum]

lemma order_mlog_subst_X_pow_ge
    (C : CombClass) (hC0 : C.counts 0 = 0) (d : ℕ) :
    ((d + 1 : ℕ) : ℕ∞) ≤
      (mlog (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ (d + 1)) C.ogf)).order := by
  apply PowerSeries.nat_le_order
  intro i hi
  rw [coeff_mlog_subst_X_pow C hC0 (Nat.succ_ne_zero d)]
  by_cases hdiv : d + 1 ∣ i
  · rw [dif_pos hdiv]
    have hdivzero : i / (d + 1) = 0 := Nat.div_eq_of_lt hi
    simp [hdivzero]
  · rw [dif_neg hdiv]

lemma summable_cycRHS_terms
    (C : CombClass) (hC0 : C.counts 0 = 0) :
    Summable fun d : ℕ =>
      ((Nat.totient (d + 1) : ℚ) / ((d + 1 : ℕ) : ℚ)) •
        mlog (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ (d + 1)) C.ogf) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr
    (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro d hd
  exact lt_of_lt_of_le
    (ENat.coe_lt_coe.mpr (Nat.lt_succ_of_le hd))
    ((order_mlog_subst_X_pow_ge C hC0 d).trans PowerSeries.le_order_smul)

lemma coeff_cycRHS_zero
    (C : CombClass) (hC0 : C.counts 0 = 0) :
    PowerSeries.coeff 0 (cycRHS C) = 0 := by
  classical
  have hs := summable_cycRHS_terms C hC0
  rw [cycRHS, hs.map_tsum _ (PowerSeries.WithPiTopology.continuous_coeff ℚ 0)]
  rw [tsum_eq_sum (s := (∅ : Finset ℕ))]
  · simp
  · intro d _hd
    rw [map_smul]
    have hcoeff :=
      coeff_mlog_subst_X_pow C hC0 (d := d + 1) (n := 0) (Nat.succ_ne_zero d)
    simp at hcoeff
    simp [hcoeff]

lemma coeff_cycRHS
    (C : CombClass) (hC0 : C.counts 0 = 0)
    {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n (cycRHS C) =
      ∑ d ∈ n.divisors,
        ((Nat.totient d : ℚ) / (d : ℚ)) *
          ∑ j ∈ Finset.Icc 1 (n / d),
            ((j : ℚ)⁻¹) *
              (Fintype.card (BlockWord C (n / d) j) : ℚ) := by
  classical
  have hIcc (m : ℕ) :
      (∑ j ∈ Finset.range m,
          (((j + 1 : ℕ) : ℚ)⁻¹) *
            (Fintype.card (BlockWord C m (j + 1)) : ℚ)) =
        ∑ j ∈ Finset.Icc 1 m,
          ((j : ℚ)⁻¹) *
            (Fintype.card (BlockWord C m j) : ℚ) := by
    refine Finset.sum_bij'
      (fun j _hj => j + 1)
      (fun j _hj => j - 1) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_Icc.mpr
        ⟨Nat.succ_pos j, Nat.succ_le_of_lt (Finset.mem_range.mp hj)⟩
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact Finset.mem_range.mpr (by
        change j - 1 < m
        omega)
    · intro j _hj
      exact Nat.add_sub_cancel j 1
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact Nat.sub_one_add_one_eq_of_pos (by omega)
    · intro j _hj
      simp
  let term : ℕ → ℚ := fun d =>
    ((Nat.totient (d + 1) : ℚ) / ((d + 1 : ℕ) : ℚ)) *
      ∑ j ∈ Finset.Icc 1 (n / (d + 1)),
        ((j : ℚ)⁻¹) *
          (Fintype.card (BlockWord C (n / (d + 1)) j) : ℚ)
  have hcoeff (d : ℕ) :
      PowerSeries.coeff n
          (((Nat.totient (d + 1) : ℚ) / ((d + 1 : ℕ) : ℚ)) •
            mlog (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ (d + 1)) C.ogf)) =
        if d + 1 ∣ n then term d else 0 := by
    rw [map_smul]
    rw [coeff_mlog_subst_X_pow C hC0 (d := d + 1) (n := n) (Nat.succ_ne_zero d)]
    by_cases hd : d + 1 ∣ n
    · rw [dif_pos hd]
      dsimp [term]
      rw [hIcc]
      rw [if_pos hd]
    · rw [dif_neg hd]
      simp [term, hd]
  have hs := summable_cycRHS_terms C hC0
  rw [cycRHS, hs.map_tsum _ (PowerSeries.WithPiTopology.continuous_coeff ℚ n)]
  calc
    (∑' d : ℕ,
        PowerSeries.coeff n
          (((Nat.totient (d + 1) : ℚ) / ((d + 1 : ℕ) : ℚ)) •
            mlog (PowerSeries.subst ((PowerSeries.X : ℚ⟦X⟧) ^ (d + 1)) C.ogf))) =
        ∑' d : ℕ, if d + 1 ∣ n then term d else 0 := by
          refine tsum_congr ?_
          intro d
          exact hcoeff d
    _ = ∑ d ∈ Finset.range n, if d + 1 ∣ n then term d else 0 := by
          rw [tsum_eq_sum (s := Finset.range n)]
          intro d hd
          rw [Finset.mem_range, not_lt] at hd
          have hndvd : ¬ d + 1 ∣ n := by
            intro hdiv
            have hle : d + 1 ≤ n :=
              Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
            omega
          rw [if_neg hndvd]
    _ = ∑ d ∈ (Finset.range n).filter (fun d => d + 1 ∣ n), term d := by
          rw [Finset.sum_filter]
    _ = ∑ d ∈ n.divisors,
        ((Nat.totient d : ℚ) / (d : ℚ)) *
          ∑ j ∈ Finset.Icc 1 (n / d),
            ((j : ℚ)⁻¹) *
              (Fintype.card (BlockWord C (n / d) j) : ℚ) := by
          refine Finset.sum_bij'
            (fun d _hd => d + 1)
            (fun d _hd => d - 1) ?_ ?_ ?_ ?_ ?_
          · intro d hd
            have hdvd : d + 1 ∣ n := (Finset.mem_filter.mp hd).2
            exact Nat.mem_divisors.mpr ⟨hdvd, hn⟩
          · intro d hd
            have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
            have hdpos : 0 < d := Nat.pos_of_ne_zero (by
              intro hdz
              rw [hdz] at hdvd
              exact hn (by simpa using hdvd))
            have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · exact Finset.mem_range.mpr (by
                change d - 1 < n
                omega)
            · simpa [Nat.sub_one_add_one_eq_of_pos hdpos] using hdvd
          · intro d _hd
            exact Nat.add_sub_cancel d 1
          · intro d hd
            have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
            have hdpos : 0 < d := Nat.pos_of_ne_zero (by
              intro hdz
              rw [hdz] at hdvd
              exact hn (by simpa using hdvd))
            exact Nat.sub_one_add_one_eq_of_pos hdpos
          · intro d hd
            simp [term]

end AnalyticCombinatorics.Ch1

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatCycleOGF
attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instDiscRatCycleOGF
open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open scoped BigOperators PowerSeries.WithPiTopology
open PowerSeries
open PowerSeries.WithPiTopology
theorem solution
    (C : CombClass) (hC0 : C.counts 0 = 0) :
    C.cyc.ogf = cycRHS C := by
  classical
  ext n
  by_cases hn0 : n = 0
  · subst n
    have hcounts0 : C.cyc.counts 0 = 0 := by
      rw [CombClass.counts]
      change Fintype.card
        (Σ k : (Finset.Icc 1 0),
          letI : NeZero k.1 :=
            ⟨Nat.ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp k.2).1)⟩
          necklaces_k C 0 k.1) = 0
      have hempty :
          IsEmpty
            (Σ k : (Finset.Icc 1 0),
              letI : NeZero k.1 :=
                ⟨Nat.ne_of_gt (Nat.succ_le_iff.mp (Finset.mem_Icc.mp k.2).1)⟩
              necklaces_k C 0 k.1) := by
        refine ⟨fun x => ?_⟩
        have hk := Finset.mem_Icc.mp x.1.2
        exact Nat.not_succ_le_zero 0 (hk.1.trans hk.2)
      exact Fintype.card_eq_zero
    rw [CombClass.coeff_ogf, hcounts0, coeff_cycRHS_zero C hC0]
    norm_num
  · rw [CombClass.coeff_ogf, counts_cyc_rational_formula C hC0 hn0,
      coeff_cycRHS C hC0 hn0]
