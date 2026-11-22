-- Prove2me | solution 1 for Erdos390.WholePaper.finiteAsymmetricLocalLemma_conditionalBound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:18:20.231077+00:00
-- url     : https://prove2.me/submissions/6ae97ae6-fe71-4cf9-8f40-21e67553515f

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007

/- Source module: Erdos390.WholePaper.FiniteAsymmetricLocalLemma -/
section


/-!
# The finite asymmetric Lovasz local lemma

This file proves the standard finite asymmetric local lemma directly on a
probability space.  The dependency hypothesis is stated as the exact measure
factorization that the proof uses: a bad event is independent of every finite
intersection of complements indexed by non-neighbors.

The key theorem `finiteAsymmetricLocalLemma_conditionalBound` is the genuine
conditional-probability induction.  For every finite conditioning family not
containing `i`, it proves

`P(A i | all events in the family are avoided) <= x i`

in denominator-free form.  It does not assume this conditional estimate.
The final induction then gives the usual positive product lower bound for the
probability that all bad events are avoided.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





/-- Adding one index removes its bad event from the event already being
conditioned on. -/
theorem avoidEvents_insert {I Omega : Type*} [DecidableEq I]
    (A : I -> Set Omega) (i : I) (s : Finset I) :
    avoidEvents A (insert i s) = avoidEvents A s \ A i := by
  simp [avoidEvents, Set.diff_eq, Set.inter_comm]



/-- Avoidance reverses inclusion of finite index sets. -/
theorem avoidEvents_anti {I Omega : Type*} [DecidableEq I]
    (A : I -> Set Omega) {s t : Finset I} (hst : s ⊆ t) :
    avoidEvents A t ⊆ avoidEvents A s := by
  intro omega homega
  simp only [avoidEvents, Set.mem_iInter] at homega ⊢
  intro i hi
  exact homega i (hst hi)

/-!
## The conditional-probability induction

For a fixed event `i` and conditioning set `s`, split `s` into the neighbors
of `i` and the non-neighbors of `i`.  Independence removes the latter.  The
strong induction hypothesis is then applied successively while the neighbors
are inserted.  This proves the denominator lower bound required to cancel
the neighborhood product in the asymmetric-LLL hypothesis.
-/

/-- The conditional estimate at the heart of the asymmetric local lemma,
written without division so it remains valid even before positivity of the
conditioning event has been established.

`hindep` is the literal finite dependency hypothesis.  It is required only
when `s` omits `i` and is disjoint from the declared dependency neighborhood
`Gamma i`.
-/
theorem finiteAsymmetricLocalLemma_conditionalBound
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ avoidEvents A s) =
        mu.real (A i) * mu.real (avoidEvents A s))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    ∀ (s : Finset I) (i : I), i ∉ s ->
      mu.real (A i ∩ avoidEvents A s) ≤
        x i * mu.real (avoidEvents A s) := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
      intro i hi
      let far : Finset I := s \ Gamma i
      let near : Finset I := s ∩ Gamma i
      have hfarSubset : far ⊆ s := by
        simpa only [far] using
          (Finset.sdiff_subset : s \ Gamma i ⊆ s)
      have hnearSubsetS : near ⊆ s := by
        simpa only [near] using
          (Finset.inter_subset_left : s ∩ Gamma i ⊆ s)
      have hnearSubsetGamma : near ⊆ Gamma i := by
        simpa only [near] using
          (Finset.inter_subset_right : s ∩ Gamma i ⊆ Gamma i)

      /- Successively insert the neighboring conditioning events.  Every
      intermediate conditioning set is a strict subset of `s`, so this is
      exactly where the strong induction hypothesis supplies the conditional
      estimate, rather than that estimate being assumed. -/
      have hnearLower :
          ∀ u : Finset I, u ⊆ near ->
            mu.real (avoidEvents A far) *
                ∏ j ∈ u, (1 - x j) ≤
              mu.real (avoidEvents A (far ∪ u)) := by
        intro u
        induction u using Finset.induction_on with
        | empty =>
            intro _hu
            simp
        | @insert a u ha hrec =>
            intro hau
            have huNear : u ⊆ near := by
              intro j hj
              exact hau (Finset.mem_insert_of_mem hj)
            have haNear : a ∈ near :=
              hau (Finset.mem_insert_self a u)
            have haGamma : a ∈ Gamma i := by
              have haNear' := haNear
              simp only [near, Finset.mem_inter] at haNear'
              exact haNear'.2
            have haS : a ∈ s := hnearSubsetS haNear
            have haNotFar : a ∉ far := by
              intro haFar
              have haFar' : a ∈ s \ Gamma i := by
                simpa only [far] using haFar
              exact (Finset.mem_sdiff.mp haFar').2 haGamma
            have haNotStage : a ∉ far ∪ u := by
              simp only [Finset.mem_union, not_or]
              exact ⟨haNotFar, ha⟩
            have hstageSubset : far ∪ u ⊆ s := by
              intro j hj
              rcases Finset.mem_union.mp hj with hj | hj
              · exact hfarSubset hj
              · exact hnearSubsetS (huNear hj)
            have hstageProper : far ∪ u ⊂ s :=
              Finset.ssubset_iff_subset_ne.mpr
                ⟨hstageSubset, fun heq =>
                  haNotStage (heq ▸ haS)⟩
            have hconditional :=
              ih (far ∪ u) hstageProper a haNotStage
            have hconditional' :
                mu.real (avoidEvents A (far ∪ u) ∩ A a) ≤
                  x a * mu.real (avoidEvents A (far ∪ u)) := by
              simpa only [Set.inter_comm] using hconditional
            have hsplit := measureReal_inter_add_diff
              (μ := mu) (s := avoidEvents A (far ∪ u))
              (t := A a) (hA a)
            have hstep :
                (1 - x a) * mu.real (avoidEvents A (far ∪ u)) ≤
                  mu.real (avoidEvents A (far ∪ u) \ A a) := by
              nlinarith [hconditional', hsplit]
            have hrecBound := hrec huNear
            have hfactorNonneg : 0 ≤ 1 - x a :=
              sub_nonneg.mpr (le_of_lt (hx a).2)
            have hscaled :=
              mul_le_mul_of_nonneg_left hrecBound hfactorNonneg
            have hindexInsert :
                far ∪ insert a u = insert a (far ∪ u) := by
              ext j
              simp only [Finset.mem_union, Finset.mem_insert]
              constructor
              · intro hj
                rcases hj with hfar | haEq | hu
                · exact Or.inr (Or.inl hfar)
                · exact Or.inl haEq
                · exact Or.inr (Or.inr hu)
              · intro hj
                rcases hj with haEq | hfar | hu
                · exact Or.inr (Or.inl haEq)
                · exact Or.inl hfar
                · exact Or.inr (Or.inr hu)
            have havoidInsert :
                avoidEvents A (far ∪ insert a u) =
                  avoidEvents A (far ∪ u) \ A a := by
              rw [hindexInsert, avoidEvents_insert]
            calc
              mu.real (avoidEvents A far) *
                    ∏ j ∈ insert a u, (1 - x j) =
                  (1 - x a) *
                    (mu.real (avoidEvents A far) *
                      ∏ j ∈ u, (1 - x j)) := by
                        rw [Finset.prod_insert ha]
                        ring
              _ ≤ (1 - x a) *
                    mu.real (avoidEvents A (far ∪ u)) := hscaled
              _ ≤ mu.real (avoidEvents A (far ∪ u) \ A a) :=
                    hstep
              _ = mu.real (avoidEvents A (far ∪ insert a u)) :=
                    congrArg mu.real havoidInsert.symm

      have hfarNear : far ∪ near = s := by
        simpa only [far, near] using
          Finset.sdiff_union_inter s (Gamma i)
      have hdenominator :
          mu.real (avoidEvents A far) *
              ∏ j ∈ near, (1 - x j) ≤
            mu.real (avoidEvents A s) := by
        have h := hnearLower near (fun _j hj => hj)
        simpa only [hfarNear] using h

      /- Since all factors lie in `[0, 1]`, the product over the whole
      dependency neighborhood is no larger than the product over those
      neighbors which actually occur in `s`. -/
      have hproductSplit :
          (∏ j ∈ Gamma i, (1 - x j)) =
            (∏ j ∈ near, (1 - x j)) *
              ∏ j ∈ Gamma i \ near, (1 - x j) := by
        calc
          (∏ j ∈ Gamma i, (1 - x j)) =
              ∏ j ∈ near ∪ (Gamma i \ near), (1 - x j) := by
                rw [Finset.union_sdiff_of_subset hnearSubsetGamma]
          _ = (∏ j ∈ near, (1 - x j)) *
                ∏ j ∈ Gamma i \ near, (1 - x j) :=
              Finset.prod_union Finset.disjoint_sdiff
      have hrestLeOne :
          (∏ j ∈ Gamma i \ near, (1 - x j)) ≤ 1 := by
        apply Finset.prod_le_one
        · intro j _hj
          exact sub_nonneg.mpr (le_of_lt (hx j).2)
        · intro j _hj
          linarith [(hx j).1]
      have hnearNonneg :
          0 ≤ ∏ j ∈ near, (1 - x j) := by
        apply Finset.prod_nonneg
        intro j _hj
        exact sub_nonneg.mpr (le_of_lt (hx j).2)
      have hproductComparison :
          (∏ j ∈ Gamma i, (1 - x j)) ≤
            ∏ j ∈ near, (1 - x j) := by
        rw [hproductSplit]
        calc
          (∏ j ∈ near, (1 - x j)) *
                ∏ j ∈ Gamma i \ near, (1 - x j) ≤
              (∏ j ∈ near, (1 - x j)) * 1 :=
                mul_le_mul_of_nonneg_left hrestLeOne hnearNonneg
          _ = ∏ j ∈ near, (1 - x j) := mul_one _

      have hiFar : i ∉ far := by
        intro hiFar
        have hiFar' : i ∈ s \ Gamma i := by
          simpa only [far] using hiFar
        exact hi (Finset.mem_sdiff.mp hiFar').1
      have hfarDisjoint : Disjoint far (Gamma i) := by
        simpa only [far] using
          (Finset.sdiff_disjoint : Disjoint (s \ Gamma i) (Gamma i))
      have hindependent := hindep i far hiFar hfarDisjoint
      have havoidSubset : avoidEvents A s ⊆ avoidEvents A far :=
        avoidEvents_anti A hfarSubset
      have hintersectionSubset :
          A i ∩ avoidEvents A s ⊆ A i ∩ avoidEvents A far := by
        intro omega homega
        exact ⟨homega.1, havoidSubset homega.2⟩
      have hintersectionMeasure :
          mu.real (A i ∩ avoidEvents A s) ≤
            mu.real (A i ∩ avoidEvents A far) :=
        measureReal_mono hintersectionSubset
      have hprobabilityScaled :
          mu.real (A i) * mu.real (avoidEvents A far) ≤
            (x i * ∏ j ∈ Gamma i, (1 - x j)) *
              mu.real (avoidEvents A far) :=
        mul_le_mul_of_nonneg_right (hprobability i)
          measureReal_nonneg
      have hproductScaled :
          (x i * ∏ j ∈ Gamma i, (1 - x j)) *
                mu.real (avoidEvents A far) ≤
            (x i * ∏ j ∈ near, (1 - x j)) *
                mu.real (avoidEvents A far) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hproductComparison (hx i).1
        · exact measureReal_nonneg
      calc
        mu.real (A i ∩ avoidEvents A s) ≤
            mu.real (A i ∩ avoidEvents A far) :=
              hintersectionMeasure
        _ = mu.real (A i) * mu.real (avoidEvents A far) :=
              hindependent
        _ ≤ (x i * ∏ j ∈ Gamma i, (1 - x j)) *
              mu.real (avoidEvents A far) := hprobabilityScaled
        _ ≤ (x i * ∏ j ∈ near, (1 - x j)) *
              mu.real (avoidEvents A far) := hproductScaled
        _ = x i *
              (mu.real (avoidEvents A far) *
                ∏ j ∈ near, (1 - x j)) := by ring
        _ ≤ x i * mu.real (avoidEvents A s) :=
              mul_le_mul_of_nonneg_left hdenominator (hx i).1

/-!
## Product lower bound and the local lemma
-/













end

end Erdos390.WholePaper

end

universe u_1 u_2
theorem solution :
∀ {I : Type u_1} {Omega : Type u_2} [Fintype.{u_1} I] [DecidableEq.{u_1 + 1} I] [inst : MeasurableSpace.{u_2} Omega]
  (mu : MeasureTheory.Measure.{u_2} Omega) [MeasureTheory.IsProbabilityMeasure.{u_2} mu] (A : I → Set.{u_2} Omega)
  (Gamma : I → Finset.{u_1} I) (x : I → Real),
  (∀ (i : I), MeasurableSet.{u_2} (A i)) →
    (∀ (i : I), And (LE.le.{0} (0 : Real) (x i)) (LT.lt.{0} (x i) (1 : Real))) →
      (∀ (i : I) (s : Finset.{u_1} I),
          i ∉ s →
            Disjoint.{u_1} s (Gamma i) →
              Eq.{1}
                (MeasureTheory.Measure.real.{u_2} mu
                  (Inter.inter.{u_2} (A i) (Erdos390.WholePaper.avoidEvents.{u_1, u_2} A s)))
                (HMul.hMul.{0, 0, 0} (MeasureTheory.Measure.real.{u_2} mu (A i))
                  (MeasureTheory.Measure.real.{u_2} mu (Erdos390.WholePaper.avoidEvents.{u_1, u_2} A s)))) →
        (∀ (i : I),
            LE.le.{0} (MeasureTheory.Measure.real.{u_2} mu (A i))
              (HMul.hMul.{0, 0, 0} (x i) (∏ j ∈ Gamma i, HSub.hSub.{0, 0, 0} (1 : Real) (x j)))) →
          ∀ (s : Finset.{u_1} I),
            ∀ i ∉ s,
              LE.le.{0}
                (MeasureTheory.Measure.real.{u_2} mu
                  (Inter.inter.{u_2} (A i) (Erdos390.WholePaper.avoidEvents.{u_1, u_2} A s)))
                (HMul.hMul.{0, 0, 0} (x i)
                  (MeasureTheory.Measure.real.{u_2} mu (Erdos390.WholePaper.avoidEvents.{u_1, u_2} A s))) := by
  exact @Erdos390.WholePaper.finiteAsymmetricLocalLemma_conditionalBound
