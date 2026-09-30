-- Prove2me | solution 1 for lean_workbook_plus_30442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:56:02.343065+00:00
-- url     : https://prove2.me/submissions/9fac49bc-fbf9-4481-90b8-2a39f738ae24

import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Tactic

open Set

namespace IrrationalRotationDensity

theorem circle_density_iff (a : Real) :
    DenseRange (fun n : Nat => n • (a : AddCircle (1 : Real))) ↔ Irrational a := by
  rw [← denseRange_zsmul_iff_nsmul, AddCircle.denseRange_zsmul_coe_iff, div_one]

theorem circle_tail_identity (a b : Real) (N n : Nat) :
    ((b + (n + N : Nat) * a : Real) : AddCircle (1 : Real)) =
      n • (a : AddCircle (1 : Real)) + ((b + N * a : Real) : AddCircle (1 : Real)) := by
  rw [show b + (n + N : Nat) * a = (n : Real) * a + (b + N * a) by
    push_cast
    ring, AddCircle.coe_add]
  congr 1
  simpa only [nsmul_eq_mul] using (AddCircle.coe_nsmul (1 : Real) (n := n) (x := a))

theorem circle_tail_density_iff (a b : Real) (N : Nat) :
    DenseRange (fun n : Nat => ((b + (n + N : Nat) * a : Real) :
      AddCircle (1 : Real))) ↔ Irrational a := by
  let c : AddCircle (1 : Real) := ((b + N * a : Real) : AddCircle (1 : Real))
  have hadd : Function.Surjective (fun z : AddCircle (1 : Real) => z + c) :=
    fun z => ⟨z - c, by simp⟩
  have hsub : Function.Surjective (fun z : AddCircle (1 : Real) => z - c) :=
    fun z => ⟨z + c, by simp⟩
  constructor
  · intro h
    apply (circle_density_iff a).mp
    have hd := hsub.denseRange.comp h (by fun_prop)
    convert hd using 1
    ext n
    simp only [Function.comp_apply, circle_tail_identity]
    simp [c]
  · intro h
    have hd := hadd.denseRange.comp ((circle_density_iff a).mpr h) (by fun_prop)
    convert hd using 1
    ext n
    exact circle_tail_identity a b N n

theorem every_tail_hits_interval (a b : Real) (ha : Irrational a) (N : Nat)
    {u v : Real} (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) :
    ∃ n : Nat, N ≤ n ∧ u < Int.fract (b + n * a) ∧ Int.fract (b + n * a) < v := by
  let q : Real → AddCircle (1 : Real) := fun x => x
  have hopen : IsOpen (q '' Ioo u v) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : (q '' Ioo u v).Nonempty := (nonempty_Ioo.mpr huv).image q
  obtain ⟨n, t, ht, he⟩ := ((circle_tail_density_iff a b N).mpr ha).exists_mem_open hopen hne
  have hfract : Int.fract (b + (n + N : Nat) * a) ∈ Ico (0 : Real) (0 + 1) :=
    ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one (b + (n + N : Nat) * a)⟩
  have ht' : t ∈ Ico (0 : Real) (0 + 1) := ⟨hu.trans ht.1.le, by linarith [ht.2]⟩
  have heq : Int.fract (b + (n + N : Nat) * a) = t := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico hfract ht').mp
    exact (AddCircle.coe_fract _).trans he.symm
  refine ⟨n + N, Nat.le_add_left N n, ?_⟩
  rw [heq]
  exact ht

theorem tail_closure (a b : Real) (ha : Irrational a) (N : Nat) :
    closure (range (fun n : Nat => Int.fract (b + (n + N : Nat) * a))) = Icc (0 : Real) 1 := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_Icc
    rintro x ⟨n, rfl⟩
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  · have hi : Ioo (0 : Real) 1 ⊆
        closure (range (fun n : Nat => Int.fract (b + (n + N : Nat) * a))) := by
      intro x hx
      rw [Metric.mem_closure_iff]
      intro e he
      have hu : max 0 (x - e / 2) < x := max_lt hx.1 (by linarith)
      have hv : x < min 1 (x + e / 2) := lt_min hx.2 (by linarith)
      obtain ⟨n, hn, hl, hr⟩ := every_tail_hits_interval a b ha N
        (le_max_left _ _) (min_le_left _ _) (hu.trans hv)
      refine ⟨Int.fract (b + n * a), ⟨n - N, by dsimp; rw [Nat.sub_add_cancel hn]⟩, ?_⟩
      rw [Real.dist_eq, abs_lt]
      have hleft := (le_max_right 0 (x - e / 2)).trans_lt hl
      have hright := hr.trans_le (min_le_right 1 (x + e / 2))
      constructor <;> linarith
    calc
      Icc (0 : Real) 1 = closure (Ioo (0 : Real) 1) := (closure_Ioo (by norm_num)).symm
      _ ⊆ closure (closure (range (fun n : Nat => Int.fract (b + (n + N : Nat) * a)))) :=
        closure_mono hi
      _ = _ := closure_closure

theorem irrational_of_tail_closure (a b : Real) (N : Nat)
    (h : closure (range (fun n : Nat => Int.fract (b + (n + N : Nat) * a))) =
      Icc (0 : Real) 1) : Irrational a := by
  apply (circle_tail_density_iff a b N).mp
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hx : Int.fract x ∈ closure
      (range (fun n : Nat => Int.fract (b + (n + N : Nat) * a))) := by
    rw [h]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hc := mem_closure_image (AddCircle.continuous_mk' (1 : Real)).continuousAt hx
  change ((Int.fract x : Real) : AddCircle (1 : Real)) ∈
    closure ((fun t : Real => (t : AddCircle (1 : Real))) ''
      range (fun n : Nat => Int.fract (b + (n + N : Nat) * a))) at hc
  rw [AddCircle.coe_fract] at hc
  apply closure_mono _ hc
  rintro y ⟨t, ⟨n, rfl⟩, rfl⟩
  exact ⟨n, (AddCircle.coe_fract _).symm⟩

theorem tail_closure_iff (a b : Real) (N : Nat) :
    closure (range (fun n : Nat => Int.fract (b + (n + N : Nat) * a))) =
      Icc (0 : Real) 1 ↔ Irrational a :=
  ⟨irrational_of_tail_closure a b N, fun h => tail_closure a b h N⟩

theorem source_density_iff (a : Real) :
    closure (range (fun n : Nat => Int.fract ((n : Real) * a))) = Icc (0 : Real) 1 ↔
      Irrational a := by
  simpa using tail_closure_iff a 0 0

theorem rational_obstruction (a b : Real) (N : Nat) (ha : ∃ q : Rat, a = q) :
    closure (range (fun n : Nat => Int.fract (b + (n + N : Nat) * a))) ≠
      Icc (0 : Real) 1 := by
  intro h
  obtain ⟨q, rfl⟩ := ha
  exact (irrational_of_tail_closure q b N h) ⟨q, rfl⟩

theorem infinitely_many_visits (a b : Real) (ha : Irrational a)
    {u v : Real} (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u < v) :
    {n : Nat | u < Int.fract (b + n * a) ∧ Int.fract (b + n * a) < v}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hl, hr⟩ := every_tail_hits_interval a b ha (N + 1) hu hv huv
  exact ⟨n, ⟨hl, hr⟩, by omega⟩

theorem positive_approximation (a : Real) (ha : Irrational a) (N : Nat)
    {e : Real} (he : 0 < e) :
    ∃ n : Nat, N < n ∧ 0 < Int.fract ((n : Real) * a) ∧
      Int.fract ((n : Real) * a) < e := by
  obtain ⟨n, hn, hl, hr⟩ := every_tail_hits_interval a 0 ha (N + 1)
    (le_refl 0) (min_le_left 1 e) (lt_min (by norm_num) he)
  refine ⟨n, by omega, ?_, ?_⟩
  · simpa using hl
  · simpa using hr.trans_le (min_le_right 1 e)

end IrrationalRotationDensity

theorem solution (a : Real) (h : ¬ ∃ q : Rat, a = q) :
    ∀ e : Real, e > 0 → ∃ n : Nat, |n * a - ⌊n * a⌋| < e := by
  intro e he
  have ha : Irrational a := by
    rintro ⟨q, hq⟩
    exact h ⟨q, hq.symm⟩
  obtain ⟨n, _, _, hn⟩ := IrrationalRotationDensity.positive_approximation a ha 0 he
  refine ⟨n, ?_⟩
  change |Int.fract ((n : Real) * a)| < e
  rw [abs_of_nonneg (Int.fract_nonneg _)]
  exact hn

#print axioms IrrationalRotationDensity.circle_density_iff
#print axioms IrrationalRotationDensity.circle_tail_identity
#print axioms IrrationalRotationDensity.circle_tail_density_iff
#print axioms IrrationalRotationDensity.every_tail_hits_interval
#print axioms IrrationalRotationDensity.tail_closure
#print axioms IrrationalRotationDensity.irrational_of_tail_closure
#print axioms IrrationalRotationDensity.tail_closure_iff
#print axioms IrrationalRotationDensity.source_density_iff
#print axioms IrrationalRotationDensity.rational_obstruction
#print axioms IrrationalRotationDensity.infinitely_many_visits
#print axioms IrrationalRotationDensity.positive_approximation
#print axioms solution
