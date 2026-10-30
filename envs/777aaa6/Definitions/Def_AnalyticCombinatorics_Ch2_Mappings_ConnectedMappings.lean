-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ConnectedMappings
-- name    : AnalyticCombinatorics_Ch2_Mappings_ConnectedMappings
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:40:10.254096+00:00
-- url     : https://prove2.me/theorems/3f00f02c-2892-4c86-9555-794d82083d25
-- title:
--   Finite self-maps, periodic cores and attached forests
-- statement:
--   Weak connectivity of a self-map means every pair of vertices has forward iterates that meet. Periodic points are vertices with a positive return time; the restriction of the map to them is a permutation. Maps with a fixed periodic core are represented by a core permutation and parent maps absorbed by that core. Single-cycle core permutations characterize the connected case. The objects include finite correspondences reconstructing a map from these data.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/ConnectedMappings.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ForestCount
import Mathlib

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Connected random mappings

This file banks the iteration-level periodic-core facts used in the standard
cyclic-core decomposition of connected mappings.  The exact enumeration is not
completed here.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

/-- Weak connectivity of a functional graph, stated directly in terms of iterates. -/
def MappingConnected {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ x y : Fin n, ∃ i j : ℕ, f^[i] x = f^[j] y

/-- A point is periodic for `f` if a positive iterate returns to it. -/
def PeriodicPoint {α : Type*} (f : α → α) (x : α) : Prop :=
  ∃ m : ℕ, 0 < m ∧ f^[m] x = x

/-- The periodic core of a self-map on a finite decidable type. -/
def periodicPointsFinset {α : Type*} [DecidableEq α] [Fintype α] (f : α → α) :
    Finset α := by
  classical
  exact Finset.univ.filter (fun x => PeriodicPoint f x)

@[simp] lemma mem_periodicPointsFinset {α : Type*} [DecidableEq α] [Fintype α]
    {f : α → α} {x : α} :
    x ∈ periodicPointsFinset f ↔ PeriodicPoint f x := by
  simp [periodicPointsFinset]

lemma periodicPoint_of_iterate_eq {α : Type*} {f : α → α} {x : α} {i j : ℕ}
    (hij : i < j) (hij_eq : f^[i] x = f^[j] x) :
    PeriodicPoint f (f^[i] x) := by
  refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
  have hji : j - i + i = j := Nat.sub_add_cancel (Nat.le_of_lt hij)
  calc
    f^[j - i] (f^[i] x) = f^[j - i + i] x := by
      rw [Function.iterate_add_apply]
    _ = f^[j] x := by rw [hji]
    _ = f^[i] x := hij_eq.symm

lemma exists_periodicPoint_on_orbit {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∃ i : ℕ, PeriodicPoint f (f^[i] x) := by
  classical
  let t : Fin (Fintype.card α + 1) → α := fun i => f^[i.1] x
  have hcard : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by
    simp
  obtain ⟨a, b, hab_ne, hab_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt t hcard
  have hval_ne : a.1 ≠ b.1 := by
    intro h
    exact hab_ne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval_ne with hab_lt | hba_lt
  · exact ⟨a.1, periodicPoint_of_iterate_eq hab_lt hab_eq⟩
  · exact ⟨b.1, periodicPoint_of_iterate_eq hba_lt hab_eq.symm⟩

lemma periodicPointsFinset_nonempty {α : Type*} [DecidableEq α] [Fintype α]
    [Nonempty α] (f : α → α) :
    (periodicPointsFinset f).Nonempty := by
  classical
  obtain ⟨x⟩ := ‹Nonempty α›
  rcases exists_periodicPoint_on_orbit f x with ⟨i, hi⟩
  exact ⟨f^[i] x, by simpa using hi⟩

lemma periodicPointsFinset_nonempty_fin {n : ℕ} (hn : 0 < n) (f : Fin n → Fin n) :
    (periodicPointsFinset f).Nonempty := by
  classical
  have hnonempty : Nonempty (Fin n) := by
    exact Fintype.card_pos_iff.mp (by simpa [Fintype.card_fin] using hn)
  exact periodicPointsFinset_nonempty f

lemma PeriodicPoint.map {α : Type*} {f : α → α} {x : α}
    (hx : PeriodicPoint f x) :
    PeriodicPoint f (f x) := by
  rcases hx with ⟨m, hmpos, hm⟩
  refine ⟨m, hmpos, ?_⟩
  calc
    f^[m] (f x) = f^[m + 1] x := by
      rw [Function.iterate_succ_apply]
    _ = f (f^[m] x) := by
      rw [Function.iterate_succ_apply']
    _ = f x := by rw [hm]

lemma PeriodicPoint.iterate {α : Type*} {f : α → α} {x : α}
    (hx : PeriodicPoint f x) :
    ∀ m : ℕ, PeriodicPoint f (f^[m] x)
  | 0 => by simpa using hx
  | m + 1 => by
      simpa [Function.iterate_succ_apply'] using (hx.iterate m).map

lemma PeriodicPoint.period_mul {α : Type*} {f : α → α} {x : α}
    {m : ℕ} (_hmpos : 0 < m) (hm : f^[m] x = x) (t : ℕ) :
    f^[m * t] x = x := by
  rw [Function.iterate_mul]
  exact Function.iterate_fixed hm t

lemma PeriodicPoint.exists_preimage {α : Type*} {f : α → α} {y : α}
    (hy : PeriodicPoint f y) :
    ∃ x : α, PeriodicPoint f x ∧ f x = y := by
  rcases hy with ⟨m, hmpos, hm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  refine ⟨f^[d] y, PeriodicPoint.iterate (⟨d + 1, Nat.succ_pos d, hm⟩ :
    PeriodicPoint f y) d, ?_⟩
  simpa [Function.iterate_succ_apply'] using hm

/-- The self-map induced by `f` on its periodic core. -/
def periodicCoreStep {α : Type*} {f : α → α} :
    {x : α // PeriodicPoint f x} → {x : α // PeriodicPoint f x} :=
  fun x => ⟨f x.1, x.2.map⟩

lemma periodicCoreStep_surjective {α : Type*} {f : α → α} :
    Function.Surjective (periodicCoreStep (f := f)) := by
  intro y
  rcases y.2.exists_preimage with ⟨x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, by ext; exact hxy⟩

lemma periodicCoreStep_bijective {α : Type*} {f : α → α}
    [Finite {x : α // PeriodicPoint f x}] :
    Function.Bijective (periodicCoreStep (f := f)) := by
  exact ⟨(Finite.injective_iff_surjective).mpr periodicCoreStep_surjective,
    periodicCoreStep_surjective⟩

/-- The restriction of a finite self-map to its periodic core is a permutation. -/
def periodicCorePerm {α : Type*} (f : α → α)
    [Finite {x : α // PeriodicPoint f x}] :
    Equiv.Perm {x : α // PeriodicPoint f x} :=
  Equiv.ofBijective (periodicCoreStep (f := f)) periodicCoreStep_bijective

@[simp] lemma periodicCorePerm_apply {α : Type*} (f : α → α)
    [Finite {x : α // PeriodicPoint f x}] (x : {x : α // PeriodicPoint f x}) :
    (periodicCorePerm f x : α) = f x.1 := by
  rfl

lemma periodicPoint_of_connected {n : ℕ} {f : Fin n → Fin n}
    (hconn : MappingConnected f) {x y : Fin n}
    (_hx : PeriodicPoint f x) (hy : PeriodicPoint f y) :
    ∃ a : ℕ, f^[a] x = y := by
  rcases hconn x y with ⟨i, j, hij⟩
  rcases hy with ⟨p, hppos, hp⟩
  let t : ℕ := p * j - j
  refine ⟨i + t, ?_⟩
  have hj_le : j ≤ p * j := by
    have hp1 : 1 ≤ p := Nat.succ_le_of_lt hppos
    calc
      j = 1 * j := by rw [one_mul]
      _ ≤ p * j := Nat.mul_le_mul_right j hp1
  have ht_add : t + j = p * j := Nat.sub_add_cancel hj_le
  have hper : f^[p * j] y = y :=
    PeriodicPoint.period_mul hppos hp j
  calc
    f^[i + t] x = f^[t + i] x := by rw [Nat.add_comm]
    _ = f^[t] (f^[i] x) := by
      rw [Function.iterate_add_apply]
    _ = f^[t] (f^[j] y) := by rw [hij]
    _ = f^[t + j] y := by
      rw [Function.iterate_add_apply]
    _ = f^[p * j] y := by rw [ht_add]
    _ = y := hper

lemma reaches_periodicPoints_step_of_iterate {n : ℕ} (f : Fin n → Fin n) :
    ∀ m : ℕ, ∀ x : Fin n,
      PeriodicPoint f (f^[m] x) →
        ForestCountNS.Reaches (periodicPointsFinset f)
          (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1) x
  | 0, x, hx => by
      exact ForestCountNS.reaches_of_mem
        (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1)
        (by simpa using hx)
  | m + 1, x, hx => by
      by_cases hxP : x ∈ periodicPointsFinset f
      · exact ForestCountNS.reaches_of_mem
          (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1) hxP
      · have hnext : PeriodicPoint f (f^[m] (f x)) := by
          simpa [Function.iterate_succ_apply] using hx
        rcases reaches_periodicPoints_step_of_iterate f m (f x) hnext with ⟨r, hr⟩
        refine ⟨r + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        rw [ForestCountNS.step_of_notMem
          (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1) hxP]
        exact hr

lemma reaches_periodicPoints_step {n : ℕ} (f : Fin n → Fin n) (x : Fin n) :
    ForestCountNS.Reaches (periodicPointsFinset f)
      (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1) x := by
  rcases exists_periodicPoint_on_orbit f x with ⟨m, hm⟩
  exact reaches_periodicPoints_step_of_iterate f m x hm

lemma reaches_step_of_iterate_mem {n : ℕ} (P : Finset (Fin n)) (f : Fin n → Fin n) :
    ∀ m : ℕ, ∀ x : Fin n,
      f^[m] x ∈ P →
        ForestCountNS.Reaches P
          (fun y : ForestCountNS.NonRoot P => f y.1) x
  | 0, x, hx => by
      exact ForestCountNS.reaches_of_mem
        (fun y : ForestCountNS.NonRoot P => f y.1) hx
  | m + 1, x, hx => by
      by_cases hxP : x ∈ P
      · exact ForestCountNS.reaches_of_mem
          (fun y : ForestCountNS.NonRoot P => f y.1) hxP
      · have hnext : f^[m] (f x) ∈ P := by
          simpa [Function.iterate_succ_apply] using hx
        rcases reaches_step_of_iterate_mem P f m (f x) hnext with ⟨r, hr⟩
        refine ⟨r + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        rw [ForestCountNS.step_of_notMem
          (fun y : ForestCountNS.NonRoot P => f y.1) hxP]
        exact hr

/-- Every finite mapping determines a rooted forest into its periodic core. -/
def forestToPeriodicCore {n : ℕ} (f : Fin n → Fin n) :
    ForestCountNS.RootedForests (periodicPointsFinset f) :=
  ⟨(fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1),
    reaches_periodicPoints_step f⟩

/-- Reconstruct a mapping from a permutation on the prescribed core and a forest rooted there. -/
def mapOfCoreForest {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P)
    (F : ForestCountNS.RootedForests P) : Fin n → Fin n :=
  fun x =>
    if hx : x ∈ P then
      (σ ⟨x, hx⟩ : Fin n)
    else
      F.1 ⟨x, hx⟩

@[simp] lemma mapOfCoreForest_of_mem {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∈ P) :
    mapOfCoreForest P σ F x = (σ ⟨x, hx⟩ : Fin n) := by
  simp [mapOfCoreForest, hx]

@[simp] lemma mapOfCoreForest_of_notMem {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∉ P) :
    mapOfCoreForest P σ F x = F.1 ⟨x, hx⟩ := by
  simp [mapOfCoreForest, hx]

lemma mapOfCoreForest_maps_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∈ P) :
    mapOfCoreForest P σ F x ∈ P := by
  rw [mapOfCoreForest_of_mem σ F hx]
  exact (σ ⟨x, hx⟩).2

lemma mapOfCoreForest_iterate_mem_of_mem {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∈ P) :
    ∀ m : ℕ, (mapOfCoreForest P σ F)^[m] x ∈ P
  | 0 => by simpa using hx
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      exact mapOfCoreForest_maps_core σ F
        (mapOfCoreForest_iterate_mem_of_mem σ F hx m)

lemma mapOfCoreForest_iterate_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    (x : P) :
    ∀ m : ℕ, (mapOfCoreForest P σ F)^[m] x.1 = (σ^[m] x : Fin n)
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      rw [mapOfCoreForest_iterate_core σ F x m]
      rw [mapOfCoreForest_of_mem σ F (σ^[m] x).2]
      rw [Function.iterate_succ_apply']

lemma periodicPoint_of_mem_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∈ P) :
    PeriodicPoint (mapOfCoreForest P σ F) x := by
  classical
  let xP : P := ⟨x, hx⟩
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  calc
    (mapOfCoreForest P σ F)^[orderOf σ] x =
        (σ^[orderOf σ] xP : Fin n) := by
          simpa [xP] using mapOfCoreForest_iterate_core σ F xP (orderOf σ)
    _ = x := by
      have hpow : σ ^ orderOf σ = 1 := pow_orderOf_eq_one σ
      have hfun : σ^[orderOf σ] xP = xP := by
        rw [← Equiv.Perm.coe_pow, hpow]
        rfl
      change ((σ^[orderOf σ] xP : P) : Fin n) = (xP : Fin n)
      exact congrArg Subtype.val hfun

lemma mapOfCoreForest_eq_step_of_notMem {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∉ P) :
    mapOfCoreForest P σ F x = ForestCountNS.step P F.1 x := by
  rw [mapOfCoreForest_of_notMem σ F hx]
  rw [ForestCountNS.step_of_notMem F.1 hx]

lemma mapOfCoreForest_iterate_eq_step_before_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    (x : Fin n) :
    ∀ m : ℕ,
      (∀ i < m, (ForestCountNS.step P F.1)^[i] x ∉ P) →
        (mapOfCoreForest P σ F)^[m] x = (ForestCountNS.step P F.1)^[m] x
  | 0, _ => rfl
  | m + 1, hbefore => by
      have hbefore_m :
          ∀ i < m, (ForestCountNS.step P F.1)^[i] x ∉ P := by
        intro i hi
        exact hbefore i (Nat.lt_trans hi (Nat.lt_succ_self m))
      have ih := mapOfCoreForest_iterate_eq_step_before_core σ F x m hbefore_m
      have hstep_not : (ForestCountNS.step P F.1)^[m] x ∉ P :=
        hbefore m (Nat.lt_succ_self m)
      calc
        (mapOfCoreForest P σ F)^[m + 1] x =
            mapOfCoreForest P σ F ((mapOfCoreForest P σ F)^[m] x) := by
              rw [Function.iterate_succ_apply']
        _ = mapOfCoreForest P σ F ((ForestCountNS.step P F.1)^[m] x) := by
              rw [ih]
        _ = ForestCountNS.step P F.1 ((ForestCountNS.step P F.1)^[m] x) := by
              exact mapOfCoreForest_eq_step_of_notMem σ F hstep_not
        _ = (ForestCountNS.step P F.1)^[m + 1] x := by
              rw [Function.iterate_succ_apply']

lemma mapOfCoreForest_eventually_mem_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    (x : Fin n) :
    ∃ m : ℕ, (mapOfCoreForest P σ F)^[m] x ∈ P := by
  classical
  rcases F.2 x with ⟨m, hm⟩
  let p : ℕ → Prop := fun r => (ForestCountNS.step P F.1)^[r] x ∈ P
  have hp : ∃ r, p r := ⟨m, hm⟩
  let r := Nat.find hp
  have hbefore : ∀ i < r, (ForestCountNS.step P F.1)^[i] x ∉ P := by
    intro i hi
    exact Nat.find_min hp hi
  have hiter :
      (mapOfCoreForest P σ F)^[r] x = (ForestCountNS.step P F.1)^[r] x :=
    mapOfCoreForest_iterate_eq_step_before_core σ F x r hbefore
  refine ⟨r, ?_⟩
  simpa [hiter, p, r] using Nat.find_spec hp

lemma mapOfCoreForest_iterate_mem_of_mem_le {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} {r s : ℕ} (hr : (mapOfCoreForest P σ F)^[r] x ∈ P)
    (hrs : r ≤ s) :
    (mapOfCoreForest P σ F)^[s] x ∈ P := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  rw [Nat.add_comm]
  rw [Function.iterate_add_apply]
  exact mapOfCoreForest_iterate_mem_of_mem σ F hr d

lemma not_periodicPoint_of_notMem_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∉ P) :
    ¬ PeriodicPoint (mapOfCoreForest P σ F) x := by
  intro hper
  rcases hper with ⟨m, hmpos, hm⟩
  rcases mapOfCoreForest_eventually_mem_core σ F x with ⟨r, hr⟩
  by_cases hr0 : r = 0
  · exact hx (by simpa [hr0] using hr)
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hle : r ≤ m * r := by
      have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
      calc
        r = 1 * r := by rw [one_mul]
        _ ≤ m * r := Nat.mul_le_mul_right r hm1
    have hmem_late :
        (mapOfCoreForest P σ F)^[m * r] x ∈ P :=
      mapOfCoreForest_iterate_mem_of_mem_le σ F hr hle
    have hfixed :
        (mapOfCoreForest P σ F)^[m * r] x = x :=
      PeriodicPoint.period_mul hmpos hm r
    exact hx (by simpa [hfixed] using hmem_late)

theorem periodicPoints_mapOfCoreForest {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P) :
    periodicPointsFinset (mapOfCoreForest P σ F) = P := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxP
    exact not_periodicPoint_of_notMem_core σ F hxP (by simpa using hx)
  · intro hx
    exact (mem_periodicPointsFinset).mpr (periodicPoint_of_mem_core σ F hx)

/-- Mappings whose periodic core is exactly `P` and whose restriction to `P` is `σ`. -/
abbrev MapsWithFixedCore {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P) : Type :=
  {f : Fin n → Fin n //
    periodicPointsFinset f = P ∧
      ∀ x : P, f x.1 = (σ x : Fin n)}

def forestOfFixedCoreMap {n : ℕ} {P : Finset (Fin n)} {σ : Equiv.Perm P}
    (M : MapsWithFixedCore P σ) :
    ForestCountNS.RootedForests P :=
  ⟨(fun y : ForestCountNS.NonRoot P => M.1 y.1), by
    intro x
    rcases exists_periodicPoint_on_orbit M.1 x with ⟨m, hm⟩
    have hmem : M.1^[m] x ∈ P := by
      have hmemCore : M.1^[m] x ∈ periodicPointsFinset M.1 := by
        simpa using hm
      have hprop :
          (M.1^[m] x ∈ periodicPointsFinset M.1) = (M.1^[m] x ∈ P) :=
        congrArg (fun S : Finset (Fin n) => M.1^[m] x ∈ S) M.2.1
      exact Eq.mp hprop hmemCore
    exact reaches_step_of_iterate_mem P M.1 m x hmem⟩

def fixedCoreMapOfForest {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P)
    (F : ForestCountNS.RootedForests P) :
    MapsWithFixedCore P σ :=
  ⟨mapOfCoreForest P σ F, periodicPoints_mapOfCoreForest P σ F, by
    intro x
    exact mapOfCoreForest_of_mem σ F x.2⟩

/-- Fixed-core mappings are equivalent to rooted forests with the same root set. -/
def fixedCoreForestEquiv {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P) :
    MapsWithFixedCore P σ ≃ ForestCountNS.RootedForests P where
  toFun := forestOfFixedCoreMap
  invFun := fixedCoreMapOfForest P σ
  left_inv M := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ P
    · have hrestr := M.2.2 ⟨x, hx⟩
      simp [fixedCoreMapOfForest, mapOfCoreForest_of_mem σ (forestOfFixedCoreMap M) hx, hrestr]
    · change mapOfCoreForest P σ (forestOfFixedCoreMap M) x = M.1 x
      rw [mapOfCoreForest_of_notMem σ (forestOfFixedCoreMap M) hx]
      rfl
  right_inv F := by
    apply Subtype.ext
    funext x
    change mapOfCoreForest P σ F x.1 = F.1 x
    rw [mapOfCoreForest_of_notMem σ F x.2]

/-- A permutation is a single directed cycle, with the singleton case included. -/
def PermSingleCycle {α : Type*} (σ : Equiv.Perm α) : Prop :=
  ∀ x y : α, ∃ m : ℕ, σ^[m] x = y

instance instFintypePermSingleCycle {α : Type*} [DecidableEq α] [Fintype α] :
    Fintype {σ : Equiv.Perm α // PermSingleCycle σ} := by
  classical
  infer_instance

lemma fixedCoreMap_iterate_core {n : ℕ} {P : Finset (Fin n)} {σ : Equiv.Perm P}
    (M : MapsWithFixedCore P σ) (x : P) :
    ∀ m : ℕ, M.1^[m] x.1 = (σ^[m] x : Fin n)
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      rw [fixedCoreMap_iterate_core M x m]
      have hrestr := M.2.2 (σ^[m] x)
      rw [hrestr]
      rw [Function.iterate_succ_apply']

lemma fixedCoreMap_eventually_mem_core {n : ℕ} {P : Finset (Fin n)} {σ : Equiv.Perm P}
    (M : MapsWithFixedCore P σ) (x : Fin n) :
    ∃ m : ℕ, M.1^[m] x ∈ P := by
  rcases exists_periodicPoint_on_orbit M.1 x with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hmemCore : M.1^[m] x ∈ periodicPointsFinset M.1 := by
    simpa using hm
  have hprop :
      (M.1^[m] x ∈ periodicPointsFinset M.1) = (M.1^[m] x ∈ P) :=
    congrArg (fun S : Finset (Fin n) => M.1^[m] x ∈ S) M.2.1
  exact Eq.mp hprop hmemCore

theorem fixedCoreMap_connected_iff_singleCycle {n : ℕ} {P : Finset (Fin n)}
    {σ : Equiv.Perm P} (M : MapsWithFixedCore P σ) :
    MappingConnected M.1 ↔ PermSingleCycle σ := by
  constructor
  · intro hconn x y
    have hxper : PeriodicPoint M.1 x.1 := by
      have hmem : x.1 ∈ periodicPointsFinset M.1 := by
        have hprop :
            (x.1 ∈ P) = (x.1 ∈ periodicPointsFinset M.1) :=
          congrArg (fun S : Finset (Fin n) => x.1 ∈ S) M.2.1.symm
        exact Eq.mp hprop x.2
      simpa using hmem
    have hyper : PeriodicPoint M.1 y.1 := by
      have hmem : y.1 ∈ periodicPointsFinset M.1 := by
        have hprop :
            (y.1 ∈ P) = (y.1 ∈ periodicPointsFinset M.1) :=
          congrArg (fun S : Finset (Fin n) => y.1 ∈ S) M.2.1.symm
        exact Eq.mp hprop y.2
      simpa using hmem
    rcases periodicPoint_of_connected hconn hxper hyper with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    have hcore := fixedCoreMap_iterate_core M x a
    simpa [hcore] using ha
  · intro hsingle x y
    rcases fixedCoreMap_eventually_mem_core M x with ⟨i, hi⟩
    rcases fixedCoreMap_eventually_mem_core M y with ⟨j, hj⟩
    let xP : P := ⟨M.1^[i] x, hi⟩
    let yP : P := ⟨M.1^[j] y, hj⟩
    rcases hsingle xP yP with ⟨a, ha⟩
    refine ⟨i + a, j, ?_⟩
    calc
      M.1^[i + a] x = M.1^[a + i] x := by rw [Nat.add_comm]
      _ = M.1^[a] (M.1^[i] x) := by
            rw [Function.iterate_add_apply]
      _ = (σ^[a] xP : Fin n) := by
            exact fixedCoreMap_iterate_core M xP a
      _ = M.1^[j] y := by
            simpa [xP, yP] using congrArg Subtype.val ha

abbrev ConnectedMapsWithFixedCore {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P) :
    Type :=
  {M : MapsWithFixedCore P σ // MappingConnected M.1}

@[reducible] def connectedMapsWithFixedCoreFintype {n : ℕ}
    (P : Finset (Fin n)) (σ : Equiv.Perm P) :
    Fintype (ConnectedMapsWithFixedCore P σ) := by
  classical
  exact Subtype.fintype (fun M : MapsWithFixedCore P σ => MappingConnected M.1)

def connectedMapsWithFixedCoreEquivOfSingle {n : ℕ} {P : Finset (Fin n)}
    {σ : Equiv.Perm P} (hσ : PermSingleCycle σ) :
    ConnectedMapsWithFixedCore P σ ≃ MapsWithFixedCore P σ where
  toFun M := M.1
  invFun M := ⟨M, (fixedCoreMap_connected_iff_singleCycle M).mpr hσ⟩
  left_inv M := by
    apply Subtype.ext
    rfl
  right_inv M := rfl

abbrev ConnectedMap (n : ℕ) : Type :=
  {f : Fin n → Fin n // MappingConnected f}

@[reducible] def connectedMapFintype (n : ℕ) : Fintype (ConnectedMap n) := by
  classical
  exact Subtype.fintype (fun f : Fin n → Fin n => MappingConnected f)

def connectedCore {n : ℕ} (hn : 0 < n) (M : ConnectedMap n) :
    {P : Finset (Fin n) // P.Nonempty} :=
  ⟨periodicPointsFinset M.1, periodicPointsFinset_nonempty_fin hn M.1⟩

def periodicSubtypeEquivCore {n : ℕ} (P : Finset (Fin n)) {f : Fin n → Fin n}
    (hP : periodicPointsFinset f = P) :
    {x : Fin n // PeriodicPoint f x} ≃ P where
  toFun x := by
    refine ⟨x.1, ?_⟩
    have hx : x.1 ∈ periodicPointsFinset f := by
      simpa using (mem_periodicPointsFinset (f := f) (x := x.1)).mpr x.2
    simpa [hP] using hx
  invFun x := by
    refine ⟨x.1, ?_⟩
    have hx : x.1 ∈ periodicPointsFinset f := by
      simp [hP, x.2]
    simpa using (mem_periodicPointsFinset (f := f) (x := x.1)).mp hx
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

def corePermOfCoreEq {n : ℕ} (P : Finset (Fin n)) {f : Fin n → Fin n}
    (hP : periodicPointsFinset f = P) : Equiv.Perm P := by
  classical
  let e := periodicSubtypeEquivCore P hP
  exact (e.symm.trans (periodicCorePerm f)).trans e

@[simp] lemma corePermOfCoreEq_apply_val {n : ℕ} (P : Finset (Fin n))
    {f : Fin n → Fin n} (hP : periodicPointsFinset f = P) (x : P) :
    (corePermOfCoreEq P (f := f) hP x : Fin n) = f x.1 := by
  classical
  simp [corePermOfCoreEq, periodicSubtypeEquivCore]

def connectedCoreFiberPerm {n : ℕ} {hn : 0 < n}
    (P : {P : Finset (Fin n) // P.Nonempty})
    (M : {M : ConnectedMap n // connectedCore hn M = P}) :
    Equiv.Perm P.1 :=
  corePermOfCoreEq P.1 (f := M.1.1) (congrArg Subtype.val M.2)

def connectedCorePermFiberEquiv {n : ℕ} {hn : 0 < n}
    (P : {P : Finset (Fin n) // P.Nonempty}) (σ : Equiv.Perm P.1) :
    {M : {M : ConnectedMap n // connectedCore hn M = P} //
        connectedCoreFiberPerm P M = σ} ≃
      ConnectedMapsWithFixedCore P.1 σ where
  toFun M := by
    let hcore : periodicPointsFinset M.1.1.1 = P.1 := congrArg Subtype.val M.1.2
    refine ⟨⟨M.1.1.1, hcore, ?_⟩, M.1.1.2⟩
    intro x
    have hperm :=
      congrArg (fun τ : Equiv.Perm P.1 => (τ x : Fin n)) M.2
    change
      (corePermOfCoreEq P.1 (f := M.1.1.1) hcore x : Fin n) = (σ x : Fin n)
        at hperm
    exact (corePermOfCoreEq_apply_val P.1 (f := M.1.1.1) hcore x).symm.trans hperm
  invFun M := by
    let hfiber : connectedCore hn ⟨M.1.1, M.2⟩ = P := by
      apply Subtype.ext
      exact M.1.2.1
    refine ⟨⟨⟨M.1.1, M.2⟩, hfiber⟩, ?_⟩
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change
      (corePermOfCoreEq P.1 (f := M.1.1) (congrArg Subtype.val hfiber) x : Fin n) =
        (σ x : Fin n)
    exact (corePermOfCoreEq_apply_val P.1 (f := M.1.1)
      (congrArg Subtype.val hfiber) x).trans (M.1.2.2 x)
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

end

end AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS


