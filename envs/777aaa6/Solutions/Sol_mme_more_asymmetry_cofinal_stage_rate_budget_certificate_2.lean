-- Prove2me | solution 2 for mme_more_asymmetry_cofinal_stage_rate_budget_certificate
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:27:17.039339+00:00
-- url     : https://prove2.me/submissions/963d1cec-af7e-4e25-9168-8cfa5cfa6c10

import Definitions.Def_mme_recursive_yz_stage_certificate
import Mathlib.Topology.Instances.Real.Lemmas

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open MME MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

namespace AgentDMA
open MME.RecursiveYZ MME.RecursiveThinSplit MME.RecursiveXHash MME.CompleteSplit

def par : Fin 1 → Fin 3 → ℕ := fun _ => ![2, 2, 0]
def nn : Fin 1 → ℕ := fun _ => 6
def mm : ∀ r, Split 2 (par r) → ℕ := fun _ _ => 2

theorem htot : ∀ r, par r 0 + par r 1 + par r 2 = 2 * 2 := by intro r; rfl

/-- a split of `par r` is determined by its first coordinate -/
theorem split_ext (r : Fin 1) (a b : Split 2 (par r)) (h : (a.val 0).val = (b.val 0).val) :
    a = b := by
  obtain ⟨a, ha1, ha2⟩ := a
  obtain ⟨b, hb1, hb2⟩ := b
  have a2 := ha2 2
  have b2 := hb2 2
  simp only [par, Matrix.cons_val] at a2 b2
  apply Subtype.ext
  funext i
  apply Fin.ext
  simp only at h
  fin_cases i
  · exact h
  · simp only [Fin.mk_one, Fin.isValue]
    omega
  · simp only [Fin.reduceFinMk, Fin.isValue]
    omega

/-- the chosen (deliberately ungraded) complete words -/
def xv (i : Fin 3) (a0 : ℕ) : Fin 3 :=
  if i = 0 then (if a0 = 2 then 1 else 2)
  else if i = 1 then (if a0 = 2 then 1 else 0)
  else (if a0 = 0 then 2 else 1)

noncomputable def mu : Fin 3 → Cell 2 1 par → CompleteWord 1 → ℕ := fun i c w =>
  if w = (fun _ => xv i (c.2.val 0).val) then
    mm c.1 c.2 + mm c.1 (complement (htot c.1) c.2) else 0

def keep : Fin 2 → RecursiveYZ.Address 2 1 par nn → (Position nn → CompleteWord 1) → Prop :=
  fun _ _ _ => True

theorem cell_cases (c : Cell 2 1 par) :
    ((c.2.val 0).val = 0 ∧ (c.2.val 1).val = 2) ∨
    ((c.2.val 0).val = 1 ∧ (c.2.val 1).val = 1) ∨
    ((c.2.val 0).val = 2 ∧ (c.2.val 1).val = 0) := by
  obtain ⟨r, a, h1, h2⟩ := c
  have a2 := h2 2
  have a0 := h2 0
  simp only [par, Matrix.cons_val] at a2 a0
  simp only
  omega

theorem cell_grade2 (c : Cell 2 1 par) : (c.2.val 2).val = 0 := by
  obtain ⟨r, a, h1, h2⟩ := c
  have a2 := h2 2
  simp only [par, Matrix.cons_val] at a2
  simp only
  omega

theorem rev_eq_iff (w : CompleteWord 1) (x : Fin 3) :
    ((fun r => Fin.rev (w r)) = fun _ => x) ↔ (w = fun _ => Fin.rev x) := by
  constructor
  · intro h; funext r; have := congrFun h r; simp only at this; rw [← this, Fin.rev_rev]
  · intro h; funext r; rw [h]; simp

theorem hx10 (c : Cell 2 1 par) :
    Fin.rev (xv 0 (c.2.val 0).val) = xv 1 (c.2.val 0).val := by
  rcases cell_cases c with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ <;> simp [xv, h0] <;> try decide

theorem hx21 (c : Cell 2 1 par) (hc : (c.2.val 0).val = 0) :
    Fin.rev (xv 1 (c.2.val 0).val) = xv 2 (c.2.val 0).val := by
  simp [xv, hc]

theorem hx20 (c : Cell 2 1 par) (hc : (c.2.val 1).val = 0) :
    Fin.rev (xv 0 (c.2.val 0).val) = xv 2 (c.2.val 0).val := by
  rcases cell_cases c with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, _⟩
  · omega
  · omega
  · simp [xv, h0]

theorem boundary : BoundaryProfiles mu := by
  refine ⟨?_, ?_, ?_⟩
  · intro c _ w
    simp only [mu, rev_eq_iff, hx10]
  · intro c hc w
    simp only [mu, rev_eq_iff, hx21 c hc]
  · intro c hc w
    simp only [mu, rev_eq_iff, hx20 c hc]

theorem mass : ∀ i c, ∑ w, mu i c w = mm c.1 c.2 + mm c.1 (complement (htot c.1) c.2) := by
  intro i c
  simp only [mu]
  rw [Finset.sum_ite_eq']
  simp

/-- the chosen words always disagree with the grade in modes 1 and 2 -/
theorem xv_ne (i : Fin 2) (c : Cell 2 1 par) :
    (xv (yzMode i) (c.2.val 0).val).val ≠ (c.2.val (yzMode i)).val := by
  have hg2 := cell_grade2 c
  rcases cell_cases c with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
  · fin_cases i
    · simp [yzMode, xv, h0, h1]
    · simp [yzMode, xv, h0, hg2]

theorem unbroken_empty (i : Fin 2) (a : RecursiveYZ.Address 2 1 par nn) :
    unbrokenWords htot (yzMode i) a (mu (yzMode i)) = ∅ := by
  classical
  ext f
  simp only [unbrokenWords, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_and]
  intro hG hU
  let p : Position nn := ⟨0, (0 : Fin 6), 0⟩
  have hGp := hG p
  have hUp := hU (fullCell htot a p) (f p)
  have hpos : 0 < RecursiveYZ.count (fullCell htot a) f (fullCell htot a p) (f p) := by
    unfold RecursiveYZ.count
    apply Finset.card_pos.mpr
    exact ⟨p, by simp⟩
  rw [hUp] at hpos
  simp only [mu] at hpos
  split_ifs at hpos with hw
  · have h3 : (xv (yzMode i) ((fullCell htot a p).2.val 0).val).val =
        ((fullCell htot a p).2.val (yzMode i)).val := by
      rw [hw] at hGp; simpa using hGp
    exact xv_ne i _ h3
  · exact absurd hpos (lt_irrefl 0)

def sp : Fin 3 → Split 2 (par 0) := fun k =>
  ⟨![k, ⟨2 - k.val, by omega⟩, 0], by
    fin_cases k <;> refine ⟨by decide, ?_⟩ <;> intro i <;> fin_cases i <;> decide⟩

theorem sp_inj : Function.Injective sp := by
  intro a b h
  have := congrArg (fun s => (s.val 0)) h
  simpa [sp] using this

theorem sp_surj (a : Split 2 (par 0)) : ∃ k, sp k = a := by
  refine ⟨a.val 0, split_ext 0 _ _ ?_⟩
  simp [sp]

def target' : Finset (Fin 6 → Fin 3) :=
  Finset.univ.filter (fun w : Fin 6 → Fin 3 =>
    ∀ k, (Finset.univ.filter (fun t => w t = k)).card = 2)

theorem target'_card : target'.card = 90 := by
  unfold target'; decide

def emb (w : Fin 6 → Fin 3) : RecursiveYZ.Address 2 1 par nn := fun _ t => sp (w t)

theorem emb_inj : Function.Injective emb := by
  intro v w h
  funext t
  have := congrFun (congrFun h 0) t
  exact sp_inj this

theorem emb_mem (w : Fin 6 → Fin 3) (hw : w ∈ target') : emb w ∈ target (n := nn) mm := by
  classical
  simp only [target, Finset.mem_filter, Finset.mem_univ, true_and]
  intro r a
  have hr : r = 0 := Subsingleton.elim _ _
  subst hr
  obtain ⟨k, rfl⟩ := sp_surj a
  simp only [target', Finset.mem_filter, Finset.mem_univ, true_and] at hw
  unfold RecursiveThinSplit.count
  simp only [mm]
  refine Eq.trans ?_ (hw k)
  congr 1
  ext t
  simp only [emb, sp_inj.eq_iff]
  constructor
  · intro h
    have h' := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩
  · intro h
    have h' := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩

theorem target_card : 90 ≤ (target (n := nn) mm).card := by
  classical
  calc 90 = (target'.image emb).card := by
        rw [Finset.card_image_of_injective _ emb_inj, target'_card]
    _ ≤ (target (n := nn) mm).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        exact emb_mem w hw

def refw : RecursiveYZ.Address 2 1 par nn := emb (fun t => ⟨t.val % 3, Nat.mod_lt _ (by norm_num)⟩)

theorem refw_mem : refw ∈ target (n := nn) mm := by
  apply emb_mem
  unfold target'
  decide

theorem labels_free : ThreeAPFree ((({0, 1, 3, 4} : Finset ℕ)) : Set ℕ) := by
  rw [threeAPFree_iff_eq_right]
  intro a ha b hb c hc h
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb hc
  omega

noncomputable def pos6 : Fin (5 + 1) ≃ (r : Fin 1) × Fin (nn r) :=
  Fintype.equivOfCardEq (by decide)

noncomputable def pos12 : Fin 12 ≃ Position nn :=
  Fintype.equivOfCardEq (by decide)

noncomputable def hd : HashData where
  half := 2
  R := 1
  parent := par
  n := nn
  m := mm
  N := 5
  p := 11
  prime := by norm_num
  odd := ⟨5, rfl⟩
  grade_lt := by norm_num
  positions := pos6
  labels := {0, 1, 3, 4}
  labels_range := by decide
  labels_free := labels_free
  good := fun state => usable htot mm pos6
    (({0, 1, 3, 4} : Finset ℕ).image (fun a : ℕ ↦ (a : ZMod 11))) state 2
    (fun i ↦ mu (yzMode i)) keep

noncomputable def st : Stage hd where
  ell := 1
  L := 12
  repairScale := 2
  repairExponent := _
  total := htot
  half_eq := rfl
  positions := pos12
  mu := mu
  boundary := boundary
  mass := mass
  reference := refw
  reference_target := refw_mem
  keep := keep
  good_eq := fun _ => rfl
  capacity := Nat.lt_two_pow_self

theorem block0_inj : Function.Injective (RecursiveXHash.block (half := 2) (R := 1)
    (parent := par) (n := nn) 0) := by
  intro v w h
  funext r t
  have := congrFun (congrFun h r) t
  exact split_ext r _ _ (congrArg Fin.val this)

theorem unbroken_empty_st (i : Fin 2) (a : RecursiveXHash.Address hd.half hd.R hd.parent hd.n) :
    unbrokenWords st.total (yzMode i) a (st.mu (yzMode i)) = ∅ := unbroken_empty i a

theorem st_budget : st.Budget := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · change 8 * (RecursiveXHash.ambient (n := nn) mm).card ≤
      11 * ((RecursiveXHash.ambient (n := nn) mm).image (RecursiveXHash.block 0)).card
    rw [Finset.card_image_of_injective _ block0_inj]
    omega
  · intro i a _
    unfold typeHoles
    rw [unbroken_empty_st]
    simp
  · intro i a _ f hf _
    rw [unbroken_empty_st] at hf
    simp at hf

theorem hd_lower : (1 : ℝ) + 1 / 121 ≤ hd.lower := by
  have h1 : (90 : ℝ) ≤ ((target (n := nn) mm).card : ℝ) := by exact_mod_cast target_card
  have h2 : (({0, 1, 3, 4} : Finset ℕ).card : ℝ) = 4 := by norm_num
  change (1 : ℝ) + 1 / 121 ≤ ((target (n := nn) mm).card : ℝ) *
    (({0, 1, 3, 4} : Finset ℕ).card : ℝ) / (2 * ((11 : ℕ) : ℝ) ^ 2)
  rw [h2, show (2 * ((11 : ℕ) : ℝ) ^ 2) = 242 by norm_num]
  have h3 : (360 : ℝ) ≤ ((target (n := nn) mm).card : ℝ) * 4 := by linarith
  calc (1 : ℝ) + 1 / 121 ≤ 360 / 242 := by norm_num
    _ ≤ _ := div_le_div_of_nonneg_right h3 (by norm_num)

end AgentDMA

open AgentDMA in
theorem _root_.solution :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j)) (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ j, (A n j).Budget) ∧
        (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
          (D n).rate ((3952233 : ℝ) / 5000000) := by
  let X : ℕ := 2402 ^ 6
  let D : ℕ → Data := fun n =>
    { factors := 1
      hash := fun _ => hd
      repairCopies := 1
      repair_pos := Nat.one_pos
      a := 1
      b := 1
      c := X ^ (2 * n) * 121 ^ 2
      power := n }
  refine ⟨D, fun _ _ => st, 2402, fun _ => 0, by norm_num, tendsto_id, tendsto_const_nhds, ?_⟩
  refine Filter.Eventually.of_forall fun n => ⟨fun _ => st_budget, ?_⟩
  show ((2402 : ℝ) ^ 6) ^ n * (1 - 0) ≤
    ((∏ _j : Fin 1, hd.lower) / ((1 : ℕ) : ℝ) - 1) *
      (((1 * 1 * (X ^ (2 * n) * 121 ^ 2) : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, Nat.cast_one,
    div_one, sub_zero, mul_one, one_mul]
  have hl := hd_lower
  have hc1 : (1 : ℝ) ≤ ((X ^ (2 * n) * 121 ^ 2 : ℕ) : ℝ) := by
    have : 1 ≤ X ^ (2 * n) * 121 ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hpow : ((X ^ (2 * n) * 121 ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤
      ((X ^ (2 * n) * 121 ^ 2 : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hsqrt : ((X ^ (2 * n) * 121 ^ 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) = (X : ℝ) ^ n * 121 := by
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    push_cast
    ring
  rw [hsqrt] at hpow
  have hX : ((2402 : ℝ) ^ 6) ^ n = (X : ℝ) ^ n := by
    rw [show (X : ℝ) = (2402 : ℝ) ^ 6 by norm_num [X]]
  rw [hX]
  calc (X : ℝ) ^ n = (1 / 121) * ((X : ℝ) ^ n * 121) := by ring
    _ ≤ (hd.lower - 1) * ((X : ℝ) ^ n * 121) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    _ ≤ (hd.lower - 1) * (((X ^ (2 * n) * 121 ^ 2 : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) := by
        apply mul_le_mul_of_nonneg_left hpow; linarith

#print axioms solution
