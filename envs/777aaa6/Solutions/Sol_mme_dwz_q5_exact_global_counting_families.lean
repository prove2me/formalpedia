-- Prove2me | solution 1 for mme_dwz_q5_exact_global_counting_families
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T22:00:56.397868+00:00
-- url     : https://prove2.me/submissions/c76d819f-c6a9-47b9-b7fb-fc0d6c04b3b8

import Definitions.Def_mme_dwz_q5_exact_global_profile_data
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_dwz_fourth_ambient_mode_star_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Theorems.Thm_mme_dwz_boundary_compatible_assignment_card_of_useful_witness
import Mathlib.Data.Finset.Card

/- Checked source module: DWZQ5ExactDataCertificates. -/
section
open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace MME.DWZQ5ExactData

open MME.DWZFourthGlobalWitness

theorem scale_pos : 0 < scale := by decide

theorem component_pos : ∀ c, 0 < component c := by decide

theorem component_sum : ∑ c, component c = scale := by decide

theorem component_div_scale_eq_alpha (c : Fin 45) :
    (component c : ℚ) / scale = alpha c := by
  fin_cases c <;> norm_num [component, scale, alpha]

theorem coarseAddress_grade_sum : ∀ c, ∑ i, (coarseAddress c i).val = 8 := by
  decide

theorem coarseAddress_injective : Function.Injective coarseAddress := by
  decide

theorem component_marginal_count : ∀ (i : Fin 3) (g : Fin 9),
    (∑ c : Fin 45, if coarseAddress c i = g then component c else 0) =
      marginal i g := by
  decide

theorem marginal_sum : ∀ i, ∑ g, marginal i g = scale := by decide

theorem marginalXY_eq (g : Fin 9) : marginal 0 g = marginal 1 g := by rfl

theorem rawProfile_support : ∀ c a, 0 < (rawProfile c).count a →
    a.val ≤ (coarseAddress c 2).val ∧ (coarseAddress c 2).val ≤ a.val + 4 := by
  decide

theorem rawProfile_denominator (c : Fin 45) :
    (rawProfile c).denominator = rawDenominator c := rfl

theorem rawProfile_count (c : Fin 45) (a : Fin 5) :
    (rawProfile c).count a = rawCount c a := rfl

abbrev SupportedCell := {v : Fin 3 → Fin 9 // (∑ i, (v i).val) = 8}

theorem supportedCell_card : Fintype.card SupportedCell = 45 := by decide

def supportedLabel (c : Fin 45) : SupportedCell :=
  ⟨coarseAddress c, coarseAddress_grade_sum c⟩

theorem supportedLabel_bijective : Function.Bijective supportedLabel := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    exact coarseAddress_injective (congrArg Subtype.val h)
  · simp only [Fintype.card_fin, supportedCell_card]

noncomputable def supportedLabelEquiv : Fin 45 ≃ SupportedCell :=
  Equiv.ofBijective supportedLabel supportedLabel_bijective

theorem supportedLabelEquiv_val (c : Fin 45) :
    (supportedLabelEquiv c).val = coarseAddress c := rfl

end MME.DWZQ5ExactData
end

/- Checked source module: DWZExactProfileSynchronization. -/
section
open BigOperators MME.DWZRestrictedValue
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZExactProfileSynchronization

variable {C : Type*} [Fintype C]

/-- A common exact period; no profile is rounded or replaced. -/
def period (p : C → IntegerZSplitProfile 5) : ℕ :=
  ∏ c, (p c).denominator

theorem period_pos (p : C → IntegerZSplitProfile 5) : 0 < period p := by
  exact Finset.prod_pos (fun c _ ↦ (p c).denominator_pos)

theorem denominator_dvd_period (p : C → IntegerZSplitProfile 5) (c : C) :
    (p c).denominator ∣ period p := by
  classical
  exact Finset.dvd_prod_of_mem (fun d ↦ (p d).denominator) (Finset.mem_univ c)

def occurrences (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ) (c : C) : ℕ :=
  a c * (period p * t)

def multiplicity (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ) (c : C) : ℕ :=
  occurrences p a t c / (p c).denominator

theorem denominator_dvd_occurrences
    (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ) (c : C) :
    (p c).denominator ∣ occurrences p a t c := by
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (denominator_dvd_period p c) t) (a c)

theorem length_multiplicity
    (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ) (c : C) :
    (p c).length (multiplicity p a t c) = occurrences p a t c := by
  exact Nat.mul_div_cancel' (denominator_dvd_occurrences p a t c)

theorem sum_occurrences
    (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ) :
    ∑ c, occurrences p a t c = (∑ c, a c) * (period p * t) := by
  simp only [occurrences, Finset.sum_mul]

theorem total_length
    (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ) :
    ∑ c, (p c).length (multiplicity p a t c) = (∑ c, a c) * (period p * t) := by
  simp only [length_multiplicity, sum_occurrences]

theorem total_length_pos
    (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ)
    (ha : 0 < ∑ c, a c) (ht : 0 < t) :
    0 < ∑ c, (p c).length (multiplicity p a t c) := by
  rw [total_length]
  exact Nat.mul_pos ha (Nat.mul_pos (period_pos p) ht)

def zCounts (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ) : C → Fin 5 → ℕ :=
  fun c w ↦ (p c).count w * multiplicity p a t c

theorem zCounts_sum
    (p : C → IntegerZSplitProfile 5) (a : C → ℕ) (t : ℕ) (c : C) :
    ∑ w, zCounts p a t c w = occurrences p a t c := by
  simp only [zCounts, ← Finset.sum_mul, (p c).count_sum]
  exact length_multiplicity p a t c

/-- X and Y boundary split counts are the literal reflected Z counts;
nonboundary entries are unused by the boundary filters and are set to zero. -/
def reflectedMu (shape : C → Fin 3 → ℕ) (z : C → Fin 5 → ℕ) :
    Fin 3 → C → Fin 5 → ℕ
  | 0, c, w => if shape c 1 = 0 then z c (Fin.rev w) else 0
  | 1, c, w => if shape c 0 = 0 then z c (Fin.rev w) else 0
  | 2, c, w => z c w

omit [Fintype C] in
theorem reflectedMu_z (shape : C → Fin 3 → ℕ) (z : C → Fin 5 → ℕ)
    (c : C) (w : Fin 5) : reflectedMu shape z 2 c w = z c w := rfl

omit [Fintype C] in
theorem reflectedMu_x_boundary (shape : C → Fin 3 → ℕ) (z : C → Fin 5 → ℕ)
    (c : C) (hc : shape c 0 = 0) (w : Fin 5) :
    reflectedMu shape z 2 c w = reflectedMu shape z 1 c (Fin.rev w) := by
  simp only [reflectedMu, hc, if_true, Fin.rev_rev]

omit [Fintype C] in
theorem reflectedMu_y_boundary (shape : C → Fin 3 → ℕ) (z : C → Fin 5 → ℕ)
    (c : C) (hc : shape c 1 = 0) (w : Fin 5) :
    reflectedMu shape z 2 c w = reflectedMu shape z 0 c (Fin.rev w) := by
  simp only [reflectedMu, hc, if_true, Fin.rev_rev]

end MME.DWZExactProfileSynchronization
end

/- Checked source module: DWZQ5ExactParameters. -/
section
open BigOperators MME.DWZRestrictedValue
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZQ5ExactConstruction

open MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open MME.DWZExactProfileSynchronization

def D : ℕ := period rawProfile

def m (t : ℕ) : Fin 45 → ℕ := multiplicity rawProfile component t

def n (t : ℕ) (c : Fin 45) : ℕ := (rawProfile c).length (m t c)

def N (t : ℕ) : ℕ := ∑ c, n t c

def shape (c : Fin 45) (i : Fin 3) : ℕ := (coarseAddress c i).val

def mu (t : ℕ) : Fin 3 → Fin 45 → Fin 5 → ℕ :=
  reflectedMu shape (zCounts rawProfile component t)

theorem D_pos : 0 < D := period_pos rawProfile

theorem n_eq (t : ℕ) (c : Fin 45) : n t c = component c * (D * t) :=
  length_multiplicity rawProfile component t c

theorem N_eq (t : ℕ) : N t = scale * (D * t) := by
  unfold N
  simp only [n_eq, ← Finset.sum_mul, component_sum]

theorem N_pos (t : ℕ) (ht : 0 < t) : 0 < N t := by
  rw [N_eq]
  exact Nat.mul_pos scale_pos (Nat.mul_pos D_pos ht)

theorem n_pos (t : ℕ) (ht : 0 < t) (c : Fin 45) : 0 < n t c := by
  rw [n_eq]
  exact Nat.mul_pos (component_pos c) (Nat.mul_pos D_pos ht)

theorem mu_z (t : ℕ) (c : Fin 45) (a : Fin 5) :
    mu t 2 c a = (rawProfile c).count a * m t c := rfl

theorem mu_sum (t : ℕ) (c : Fin 45) : ∑ a, mu t 2 c a = n t c := by
  simp only [mu_z, ← Finset.sum_mul, (rawProfile c).count_sum]
  rfl

theorem mu_x_boundary (t : ℕ) (c : Fin 45) (hc : shape c 0 = 0) (a : Fin 5) :
    mu t 2 c a = mu t 1 c (Fin.rev a) :=
  reflectedMu_x_boundary shape (zCounts rawProfile component t) c hc a

theorem mu_y_boundary (t : ℕ) (c : Fin 45) (hc : shape c 1 = 0) (a : Fin 5) :
    mu t 2 c a = mu t 0 c (Fin.rev a) :=
  reflectedMu_y_boundary shape (zCounts rawProfile component t) c hc a

theorem mu_support (t : ℕ) (c : Fin 45) (a : Fin 5) (ha : 0 < mu t 2 c a) :
    a.val ≤ shape c 2 ∧ shape c 2 ≤ a.val + 4 := by
  exact rawProfile_support c a (Nat.pos_of_mul_pos_right ha)

theorem scaled_marginals (t : ℕ) (i : Fin 3) (g : Fin 9) :
    (∑ c : Fin 45, if coarseAddress c i = g then n t c else 0) =
      marginal i g * (D * t) := by
  rw [← component_marginal_count i g, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp only [n_eq, zero_mul]

theorem shape_supported (c : Fin 45) : shape c 0 + shape c 1 + shape c 2 = 8 := by
  simpa [shape, Fin.sum_univ_succ, Nat.add_assoc] using coarseAddress_grade_sum c

end MME.DWZQ5ExactConstruction
end

/- Checked source module: DWZExactIndexedFamilies. -/
section
open BigOperators MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MME.DWZExactIndexedFamilies

abbrev FourthCell := {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8}

def labelShape {k : ℕ} (sigma : Fin k ≃ FourthCell) : Fin k → Fin 3 → ℕ :=
  fun c i ↦ ((sigma c).val i).val

noncomputable def marginalOf {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (n : Fin k → ℕ) : Fin 3 → ℕ → ℕ :=
  fun i g ↦ ∑ c : {c : Fin k // shape c i = g}, n c.val

def ExactHistogram {N k : ℕ} (n : Fin k → ℕ) (w : Fin N → Fin k) : Prop :=
  ∀ c, Fintype.card {t : Fin N // w t = c} = n c

theorem histogram_pushforward {N k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (n : Fin k → ℕ) (w : Fin N → Fin k) (hw : ExactHistogram n w) :
    SameMarginal (marginalOf shape n) (fun i t ↦ shape (w t) i) := by
  classical
  intro i g
  let e := Equiv.sigmaSubtypeFiberEquivSubtype w
    (p := fun t ↦ shape (w t) i = g)
    (q := fun c ↦ shape c i = g) (fun _ ↦ Iff.rfl)
  have hc := Fintype.card_congr e
  have hw' : ∀ c, Fintype.card {t : Fin N // w t = c} = n c := hw
  simpa only [Fintype.card_sigma, hw', marginalOf] using hc.symm

theorem shape_injective {k : ℕ} (sigma : Fin k ≃ FourthCell) :
    Function.Injective (labelShape sigma) := by
  intro c d h
  apply sigma.injective
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun h i

theorem shape_supported {k : ℕ} (sigma : Fin k ≃ FourthCell) (c : Fin k) :
    labelShape sigma c 0 + labelShape sigma c 1 + labelShape sigma c 2 = 8 := by
  have h := (sigma c).property
  simpa [Fin.sum_univ_succ, labelShape, Nat.add_assoc] using h

theorem supported_address_has_word {N k : ℕ} (sigma : Fin k ≃ FourthCell)
    (a : CoarseAddress N) (ha : Supported 8 a) :
    ∃ w : Fin N → Fin k, (fun i t ↦ labelShape sigma (w t) i) = a := by
  have hbound (i : Fin 3) (t : Fin N) : a i t < 9 := by
    have h : a 0 t + a 1 t + a 2 t = 8 := ha t
    fin_cases i
    · change a 0 t < 9
      omega
    · change a 1 t < 9
      omega
    · change a 2 t < 9
      omega
  let v (t : Fin N) : FourthCell :=
    ⟨fun i ↦ ⟨a i t, hbound i t⟩, by
      simpa [Fin.sum_univ_succ, Nat.add_assoc] using ha t⟩
  refine ⟨fun t ↦ sigma.symm (v t), ?_⟩
  funext i t
  change ((sigma (sigma.symm (v t))).val i).val = a i t
  rw [sigma.apply_symm_apply]

theorem positions_of_histogram {N k : ℕ} (n : Fin k → ℕ) (w : Fin N → Fin k)
    (hw : ExactHistogram n w) :
    ∃ positions : Fin N ≃ Σ c, Fin (n c),
      ∀ c r, w (positions.symm ⟨c, r⟩) = c := by
  classical
  let fiber (c : Fin k) : {t : Fin N // w t = c} ≃ Fin (n c) :=
    Fintype.equivFinOfCardEq (hw c)
  let positions := (Equiv.sigmaFiberEquiv w).symm.trans (Equiv.sigmaCongrRight fiber)
  refine ⟨positions, ?_⟩
  intro c r
  exact (fiber c |>.symm r).property

/-- Complete finite enumeration of the full marginal ambient family, retaining exactly
the prescribed joint type as targets. No existence or rearrangement hypothesis is used. -/
theorem indexed_families_complete (N k : ℕ) (sigma : Fin k ≃ FourthCell)
    (n : Fin k → ℕ) (hn : ∑ c, n c = N) :
    ∃ (R : ℕ) (component : Fin R → Fin N → Fin k) (targets : Finset (Fin R)),
      Function.Injective component ∧
      Function.Injective (owner component (labelShape sigma)) ∧
      (∀ a, SameMarginal (marginalOf (labelShape sigma) n)
        (owner component (labelShape sigma) a)) ∧
      (∀ a, Supported 8 (owner component (labelShape sigma) a)) ∧
      (∀ a : CoarseAddress N, Supported 8 a →
        SameMarginal (marginalOf (labelShape sigma) n) a →
        ∃ b, owner component (labelShape sigma) b = a) ∧
      (∀ a, a ∈ targets ↔ ExactHistogram n (component a)) ∧
      (∀ w : Fin N → Fin k, ExactHistogram n w →
        ∃ a ∈ targets, component a = w) ∧
      targets.card = N.factorial / ∏ c, (n c).factorial ∧
      targets.Nonempty ∧
      ∃ positions : ∀ a : Fin R, a ∈ targets → (Fin N ≃ Σ c, Fin (n c)),
        ∀ a ha c r, component a ((positions a ha).symm ⟨c, r⟩) = c := by
  classical
  let Ambient := {w : Fin N → Fin k //
    SameMarginal (marginalOf (labelShape sigma) n)
      (fun i t ↦ labelShape sigma (w t) i)}
  let R := Fintype.card Ambient
  let e : Fin R ≃ Ambient := (Fintype.equivFin Ambient).symm
  let component : Fin R → Fin N → Fin k := fun a ↦ (e a).val
  let targets := Finset.univ.filter (fun a ↦ ExactHistogram n (component a))
  have hmem (a : Fin R) : a ∈ targets ↔ ExactHistogram n (component a) := by
    simp [targets]
  have hinj : Function.Injective component := by
    intro a b h
    apply e.injective
    exact Subtype.ext h
  have hcomplete (w : Fin N → Fin k) (hw : ExactHistogram n w) :
      ∃ a ∈ targets, component a = w := by
    let aw : Ambient := ⟨w, histogram_pushforward (labelShape sigma) n w hw⟩
    refine ⟨e.symm aw, ?_, ?_⟩
    · apply (hmem _).mpr
      simpa [component, aw] using hw
    · simp [component, aw]
  let targetEquiv : {a : Fin R // a ∈ targets} ≃
      {w : Fin N → Fin k // ExactHistogram n w} :=
    { toFun := fun a ↦ ⟨component a.val, (hmem a.val).mp a.property⟩
      invFun := fun w ↦
        ⟨e.symm ⟨w.val, histogram_pushforward (labelShape sigma) n w.val w.property⟩,
          by
            apply (hmem _).mpr
            simpa [component] using w.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply e.injective
        apply Subtype.ext
        simp [component]
      right_inv := by intro w; apply Subtype.ext; simp [component] }
  have hcard : targets.card = N.factorial / ∏ c, (n c).factorial := by
    have hc := Fintype.card_congr targetEquiv
    rw [Fintype.card_coe] at hc
    rw [hc]
    simpa only [ExactHistogram, ← Nat.card_eq_fintype_card, Nat.card_fin] using
      mme_fintype_prescribed_fiber_function_card (α := Fin N) n (by simpa using hn)
  have hnonempty : targets.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    simpa only [Nat.multinomial, hn] using Nat.multinomial_pos Finset.univ n
  refine ⟨R, component, targets, hinj, ?_, ?_, ?_, ?_, hmem, hcomplete,
    hcard, hnonempty, ?_⟩
  · intro a b h
    apply hinj
    funext t
    apply shape_injective sigma
    funext i
    exact congrFun (congrFun h i) t
  · intro a
    exact (e a).property
  · intro a t
    exact shape_supported sigma (component a t)
  · intro a ha hm
    obtain ⟨w, hw⟩ := supported_address_has_word sigma a ha
    let aw : Ambient := ⟨w, by rw [hw]; exact hm⟩
    refine ⟨e.symm aw, ?_⟩
    change (fun i t ↦ labelShape sigma (component (e.symm aw) t) i) = a
    simpa [component, aw] using hw
  · have hp : ∀ a : Fin R, ∀ ha : a ∈ targets,
        ∃ pos : Fin N ≃ Σ c, Fin (n c),
          ∀ c r, component a (pos.symm ⟨c, r⟩) = c := by
      intro a ha
      exact positions_of_histogram n (component a) ((hmem a).mp ha)
    choose positions hpositions using hp
    exact ⟨positions, hpositions⟩

theorem marginalOf_eq_zero_of_nine_le {k : ℕ} (sigma : Fin k ≃ FourthCell)
    (n : Fin k → ℕ) (i : Fin 3) (g : ℕ) (hg : 9 ≤ g) :
    marginalOf (labelShape sigma) n i g = 0 := by
  classical
  unfold marginalOf
  apply Finset.sum_eq_zero
  intro c _
  have hlt := ((sigma c.val).val i).isLt
  have heq := c.property
  change ((sigma c.val).val i).val = g at heq
  omega

/-- The index count of every ambient mode-star is the exact sum over all
admissible joint tables, not the smaller prescribed-joint-type star. -/
theorem indexed_ambient_mode_star_card (N k R : ℕ) (sigma : Fin k ≃ FourthCell)
    (n : Fin k → ℕ) (component : Fin R → Fin N → Fin k)
    (hinj : Function.Injective (owner component (labelShape sigma)))
    (hmarginal : ∀ a, SameMarginal (marginalOf (labelShape sigma) n)
      (owner component (labelShape sigma) a))
    (hcomplete : ∀ a : CoarseAddress N, Supported 8 a →
      SameMarginal (marginalOf (labelShape sigma) n) a →
      ∃ b, owner component (labelShape sigma) b = a)
    (mode : Fin 3) (a : Fin R) :
    let M := fun i (g : Fin 9) ↦ marginalOf (labelShape sigma) n i g.val
    let admissible : Finset (FourthCell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ s : {s : FourthCell // s.val i = g}, (h s.val).val) = M i g)
    (Finset.univ.filter (fun b ↦
      owner component (labelShape sigma) b mode =
        owner component (labelShape sigma) a mode)).card =
      ∑ h ∈ admissible, ∏ g : Fin 9, (M mode g).factorial /
        ∏ s : {s : FourthCell // s.val mode = g}, ((h s.val).val).factorial := by
  classical
  let M := fun i (g : Fin 9) ↦ marginalOf (labelShape sigma) n i g.val
  let x : Fin N → Fin 9 := fun t ↦ (sigma (component a t)).val mode
  let Star := {b : Fin R // owner component (labelShape sigma) b mode =
    owner component (labelShape sigma) a mode}
  let RawStar := {v : Fin 3 → Fin N → Fin 9 //
    (∀ t, (∑ i, (v i t).val) = 8) ∧
    (∀ i g, Fintype.card {t : Fin N // v i t = g} = M i g) ∧ v mode = x}
  have hfinite_marginal (b : Fin R) (i : Fin 3) (g : Fin 9) :
      Fintype.card {t : Fin N // (sigma (component b t)).val i = g} = M i g := by
    simpa only [owner, labelShape, Fin.val_inj] using hmarginal b i g.val
  let encode : Star → RawStar := fun b ↦
    ⟨fun i t ↦ (sigma (component b.val t)).val i,
      ⟨fun t ↦ (sigma (component b.val t)).property,
        hfinite_marginal b.val, by
          funext t
          apply Fin.ext
          exact congrFun b.property t⟩⟩
  have hencode_inj : Function.Injective encode := by
    intro b c h
    apply Subtype.ext
    apply hinj
    funext i t
    exact congrArg Fin.val (congrFun (congrFun (congrArg Subtype.val h) i) t)
  have hencode_surj : Function.Surjective encode := by
    intro v
    let va : CoarseAddress N := fun i t ↦ (v.val i t).val
    have hsupport : Supported 8 va := by
      intro t
      simpa [Fin.sum_univ_succ, va, Nat.add_assoc] using v.property.1 t
    have hnat_marginal : SameMarginal (marginalOf (labelShape sigma) n) va := by
      intro i g
      by_cases hg : g < 9
      · calc
          Fintype.card {t : Fin N // va i t = g} =
              Fintype.card {t : Fin N // v.val i t = ⟨g, hg⟩} :=
            Fintype.card_congr (Equiv.subtypeEquivRight (fun t ↦
              ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩))
          _ = _ := v.property.2.1 i ⟨g, hg⟩
      · have hge : 9 ≤ g := Nat.le_of_not_gt hg
        rw [marginalOf_eq_zero_of_nine_le sigma n i g hge]
        haveI : IsEmpty {t : Fin N // va i t = g} := ⟨by
          intro t
          have hlt := (v.val i t.val).isLt
          have heq := t.property
          change (v.val i t.val).val = g at heq
          omega⟩
        exact Fintype.card_of_isEmpty
    obtain ⟨b, hb⟩ := hcomplete va hsupport hnat_marginal
    have hbStar : owner component (labelShape sigma) b mode =
        owner component (labelShape sigma) a mode := by
      rw [hb]
      funext t
      exact congrArg Fin.val (congrFun v.property.2.2 t)
    refine ⟨⟨b, hbStar⟩, ?_⟩
    apply Subtype.ext
    funext i t
    apply Fin.ext
    exact congrFun (congrFun hb i) t
  have hcard : (Finset.univ.filter (fun b ↦
      owner component (labelShape sigma) b mode =
        owner component (labelShape sigma) a mode)).card = Nat.card RawStar := by
    have hc := Fintype.card_congr (Equiv.ofBijective encode ⟨hencode_inj, hencode_surj⟩)
    simpa only [Nat.card_eq_fintype_card, Star, Fintype.card_subtype] using hc
  change _ = _
  rw [hcard]
  exact mme_dwz_fourth_ambient_mode_star_card N M mode x (hfinite_marginal a mode)

/-- Publication-facing bundle; all data used in the statement are explicit. -/
theorem complete_indexed_families (N k : ℕ)
    (sigma : Fin k ≃ {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8})
    (n : Fin k → ℕ) (hn : ∑ c, n c = N) :
    let shape : Fin k → Fin 3 → ℕ := fun c i ↦ ((sigma c).val i).val
    let marginal : Fin 3 → ℕ → ℕ :=
      fun i g ↦ ∑ c : {c : Fin k // shape c i = g}, n c.val
    let M := fun i (g : Fin 9) ↦ marginal i g.val
    let Cell := {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8}
    let admissible : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ s : {s : Cell // s.val i = g}, (h s.val).val) = M i g)
    ∃ (R : ℕ) (component : Fin R → Fin N → Fin k) (targets : Finset (Fin R)),
      Function.Injective component ∧
      Function.Injective (owner component shape) ∧
      (∀ a, SameMarginal marginal (owner component shape a)) ∧
      (∀ a, Supported 8 (owner component shape a)) ∧
      (∀ a : CoarseAddress N, Supported 8 a → SameMarginal marginal a →
        ∃ b, owner component shape b = a) ∧
      (∀ a, a ∈ targets ↔
        ∀ c, Fintype.card {t : Fin N // component a t = c} = n c) ∧
      (∀ w : Fin N → Fin k, (∀ c, Fintype.card {t : Fin N // w t = c} = n c) →
        ∃ a ∈ targets, component a = w) ∧
      targets.card = N.factorial / ∏ c, (n c).factorial ∧
      targets.Nonempty ∧
      (∃ positions : ∀ a : Fin R, a ∈ targets → (Fin N ≃ Σ c, Fin (n c)),
        ∀ a ha c r, component a ((positions a ha).symm ⟨c, r⟩) = c) ∧
      (∀ (mode : Fin 3) (a : Fin R),
        (Finset.univ.filter (fun b ↦
          owner component shape b mode = owner component shape a mode)).card =
          ∑ h ∈ admissible, ∏ g : Fin 9, (M mode g).factorial /
            ∏ s : {s : Cell // s.val mode = g}, ((h s.val).val).factorial) := by
  classical
  dsimp only
  obtain ⟨R, component, targets, hcomponent, howner, hmarginal, hsupported,
    hcomplete, hmem, hwords, hcard, hnonempty, hpositions⟩ :=
      indexed_families_complete N k sigma n hn
  refine ⟨R, component, targets, hcomponent, howner, hmarginal, hsupported,
    hcomplete, hmem, hwords, hcard, hnonempty, hpositions, ?_⟩
  intro mode a
  exact indexed_ambient_mode_star_card N k R sigma n component howner hmarginal
    hcomplete mode a

end MME.DWZExactIndexedFamilies
end

/- Checked source module: DWZActualFineZCompatibility. -/
section
open BigOperators MME.CompleteSplit MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZActualFineZCompatibility

def totalTag (v : CompleteWord 3) : Fin 9 :=
  ⟨∑ r, (v r).val, by
    have h0 := (v 0).isLt
    have h1 := (v 1).isLt
    have h2 := (v 2).isLt
    have h3 := (v 3).isLt
    change (∑ r : Fin 4, (v r).val) < 9
    rw [Fin.sum_univ_four]
    omega⟩

def fineLabel {N : ℕ} (f : FineWord 3 N) (t : Fin N) : Fin 9 × Fin 5 :=
  (totalTag (f t), fourthLeftTag (f t))

def boundary {k : ℕ} (shape : Fin k → Fin 3 → ℕ) (c : Fin k) : Prop :=
  shape c 0 = 0 ∨ shape c 1 = 0

noncomputable def fineMass {k : ℕ} (coarse : Fin k → Fin 9)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (i : Fin 9 × Fin 5) : ℕ :=
  ∑ c : {c : Fin k // coarse c = i.1}, mu 2 c.val i.2

noncomputable def collapse {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (c : Fin k) : Fin k ⊕ Fin 9 :=
  if boundary shape c then Sum.inl c else Sum.inr (coarse c)

noncomputable def pooledMass {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ) :
    (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ
  | (Sum.inl c, (g,l)) => if boundary shape c ∧ coarse c = g then mu 2 c l else 0
  | (Sum.inr g', (g,l)) => if g' = g then fineMass coarse mu (g,l) -
      ∑ c ∈ Finset.univ.filter (fun c ↦ boundary shape c ∧ coarse c = g), mu 2 c l
    else 0

noncomputable def compatibilityCount {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ) : ℕ :=
  (∏ i : Fin 9 × Fin 5, (fineMass coarse mu i).factorial /
    ∏ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
      (pooledMass shape coarse mu di.val).factorial) *
  (∏ d : Fin k ⊕ Fin 9, (∑ i, pooledMass shape coarse mu (d,i)).factorial /
    ∏ c : {c : Fin k // collapse shape coarse c = d}, (n c.val).factorial)

def assignmentCompatible {N k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (f : FineWord 3 N) (g : Fin N → Fin k) : Prop :=
  (∀ c, Fintype.card {t : Fin N // g t = c} = n c) ∧
  (∀ t, ∑ r, (f t r).val = shape (g t) 2) ∧
  ∀ c, boundary shape c → ∀ l,
    Fintype.card {t : Fin N // g t = c ∧ fourthLeftTag (f t) = l} = mu 2 c l

theorem sum_joint_pred {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq C] (g : A → C) (Q : C → Prop) [DecidablePred Q]
    (P : A → Prop) [DecidablePred P] :
    (∑ c : {c : C // Q c}, Fintype.card {a : A // g a = c.val ∧ P a}) =
      Fintype.card {a : A // Q (g a) ∧ P a} := by
  classical
  let e : (Σ c : {c : C // Q c}, {a : A // g a = c.val ∧ P a}) ≃
      {a : A // Q (g a) ∧ P a} := {
    toFun := fun x ↦ ⟨x.2.val, x.2.property.1.symm ▸ x.1.property, x.2.property.2⟩
    invFun := fun a ↦ ⟨⟨g a.val, a.property.1⟩, ⟨a.val, rfl, a.property.2⟩⟩
    left_inv := by rintro ⟨⟨c,hc⟩,⟨a,ha,hp⟩⟩; cases ha; rfl
    right_inv := fun _ ↦ rfl }
  simpa only [Fintype.card_sigma] using Fintype.card_congr e

theorem graded_coarse_eq {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (j : Fin R) (f : FineWord 3 N) (hg : Graded component shape j 2 f) (t : Fin N) :
    coarse (component j t) = (fineLabel f t).1 := by
  apply Fin.ext
  exact (hshape _).trans (hg t).symm

theorem useful_fine_histogram {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (j : Fin R) (f : FineWord 3 N)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f)
    (i : Fin 9 × Fin 5) :
    Fintype.card {t : Fin N // fineLabel f t = i} = fineMass coarse mu i := by
  classical
  calc
    _ = Fintype.card {t : Fin N // coarse (component j t) = i.1 ∧
        fourthLeftTag (f t) = i.2} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro t
      rw [graded_coarse_eq component shape coarse hshape j f hg t]
      exact Prod.ext_iff
    _ = ∑ c : {c : Fin k // coarse c = i.1},
        Fintype.card {t : Fin N // component j t = c.val ∧ fourthLeftTag (f t) = i.2} :=
      (sum_joint_pred (component j) (fun c ↦ coarse c = i.1)
        (fun t ↦ fourthLeftTag (f t) = i.2)).symm
    _ = _ := Finset.sum_congr rfl (fun c _ ↦ hp c.val i.2)

theorem aggregate_of_useful {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (j b : Fin R) (f : FineWord 3 N)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f)
    (hb : Graded component shape b 2 f) (g : Fin 9) (l : Fin 5) :
    Fintype.card {t : Fin N // shape (component b t) 2 = g.val ∧
      fourthLeftTag (f t) = l} = fineMass coarse mu (g,l) := by
  rw [← useful_fine_histogram component shape coarse hshape mu j f hg hp (g,l)]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  rw [← hb t]
  change (totalTag (f t)).val = g.val ∧ fourthLeftTag (f t) = l ↔ _
  rw [← Fin.ext_iff]
  change (totalTag (f t) = g ∧ fourthLeftTag (f t) = l) ↔
    (totalTag (f t), fourthLeftTag (f t)) = (g,l)
  exact ⟨fun h ↦ Prod.ext h.1 h.2, fun h ↦ ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

set_option maxHeartbeats 150000 in
theorem assignment_count_of_useful {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (j : Fin R) (f : FineWord 3 N)
    (hn : ∀ c, Fintype.card {t : Fin N // component j t = c} = n c)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f) :
    Nat.card {g : Fin N → Fin k // assignmentCompatible shape mu n f g} =
      compatibilityCount shape coarse mu n := by
  classical
  have hf := useful_fine_histogram component shape coarse hshape mu j f hg hp
  have hc := mme_dwz_boundary_compatible_assignment_card_of_useful_witness
    (fineLabel f) coarse (boundary shape) (component j)
    (graded_coarse_eq component shape coarse hshape j f hg)
  dsimp only at hc
  have hpred (g : Fin N → Fin k) :
      assignmentCompatible shape mu n f g ↔
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) ∧
      (∀ t, coarse (g t) = (fineLabel f t).1) ∧
      ∀ c, boundary shape c → ∀ l,
        Fintype.card {t : Fin N // g t = c ∧ (fineLabel f t).2 = l} = mu 2 c l := by
    unfold assignmentCompatible
    apply and_congr_right
    intro _
    apply and_congr_left
    intro _
    apply forall_congr'
    intro t
    rw [Fin.ext_iff, hshape]
    exact eq_comm
  have hp' (c : Fin k) (l : Fin 5) :
      Fintype.card {t : Fin N // component j t = c ∧ (fineLabel f t).2 = l} = mu 2 c l := hp c l
  simp only [hn, hp', hf] at hc
  calc
    _ = Nat.card {g : Fin N → Fin k //
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) ∧
      (∀ t, coarse (g t) = (fineLabel f t).1) ∧
      ∀ c, boundary shape c → ∀ l,
        Fintype.card {t : Fin N // g t = c ∧ (fineLabel f t).2 = l} = mu 2 c l} :=
      Nat.card_congr (Equiv.subtypeEquivRight hpred)
    _ = _ := by
      refine hc.trans ?_
      unfold compatibilityCount collapse
      apply congrArg₂ Nat.mul
      · apply Finset.prod_congr rfl
        intro i _
        apply congrArg (fun d : ℕ ↦ (fineMass coarse mu i).factorial / d)
        apply Finset.prod_congr
        · ext di
          simp only [Finset.mem_univ]
        · intro di _
          apply congrArg Nat.factorial
          rcases di with ⟨⟨d,g,l⟩,hi⟩
          cases d <;> rfl
      · apply Finset.prod_congr rfl
        intro d _
        apply congrArg₂ Nat.div
        · apply congrArg Nat.factorial
          apply Finset.sum_congr rfl
          rintro ⟨g,l⟩ _
          cases d <;> rfl
        · apply Finset.prod_congr
          · ext c
            simp only [Finset.mem_univ]
          · intro c _
            rfl

end MME.DWZActualFineZCompatibility
end

/- Checked source module: DWZActualFineZCompatibilityIndexed. -/
section
open BigOperators MME.CompleteSplit MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZActualFineZCompatibility

theorem profile_component_count {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (j : Fin R) (f : FineWord 3 N)
    (hp : Profile component fourthLeftTag mu j 2 f) (c : Fin k) :
    Fintype.card {t : Fin N // component j t = c} = ∑ l, mu 2 c l := by
  classical
  let e : (Σ l : Fin 5, {t : Fin N // component j t = c ∧ fourthLeftTag (f t) = l}) ≃
      {t : Fin N // component j t = c} := {
    toFun := fun x ↦ ⟨x.2.val, x.2.property.1⟩
    invFun := fun t ↦ ⟨fourthLeftTag (f t.val), ⟨t.val,t.property,rfl⟩⟩
    left_inv := by rintro ⟨l,⟨t,ht,hl⟩⟩; cases hl; rfl
    right_inv := fun _ ↦ rfl }
  have hc := (Fintype.card_congr e).symm
  have hp' (l : Fin 5) :
      Fintype.card {t : Fin N // component j t = c ∧ fourthLeftTag (f t) = l} = mu 2 c l :=
    hp c l
  simpa only [Fintype.card_sigma, hp'] using hc

theorem assignment_iff_indexed {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (b : Fin R) (f : FineWord 3 N)
    (hn : ∀ c, Fintype.card {t : Fin N // component b t = c} = n c) :
    assignmentCompatible shape mu n f (component b) ↔
      ZCompatible component shape fourthLeftTag mu b f :=
  ⟨fun h ↦ ⟨h.2.1,h.2.2⟩, fun h ↦ ⟨hn,h.1,h.2⟩⟩

noncomputable def compatibleTargetEquiv {N k R : ℕ}
    (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R)) (f : FineWord 3 N)
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g) :
    {b : Fin R // b ∈ targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)} ≃
      {g : Fin N → Fin k // assignmentCompatible shape mu n f g} := by
  classical
  let F : {b : Fin R // b ∈ targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)} →
      {g : Fin N → Fin k // assignmentCompatible shape mu n f g} := fun b ↦
    ⟨component b.val, (assignment_iff_indexed component shape mu n b.val f
      (hn b.val (Finset.mem_filter.mp b.property).1)).mpr (Finset.mem_filter.mp b.property).2⟩
  apply Equiv.ofBijective F
  constructor
  · intro b b' he
    apply Subtype.ext
    exact hinj (Finset.mem_filter.mp b.property).1 (Finset.mem_filter.mp b'.property).1
      (congrArg Subtype.val he)
  · intro g
    obtain ⟨b,hb,hbg⟩ := hcomplete g.val g.property.1
    have hbc : ZCompatible component shape fourthLeftTag mu b f :=
      (assignment_iff_indexed component shape mu n b f (hn b hb)).mp (hbg.symm ▸ g.property)
    refine ⟨⟨b,Finset.mem_filter.mpr ⟨hb,hbc⟩⟩,?_⟩
    exact Subtype.ext hbg

theorem indexed_compatible_count {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R))
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g)
    (j : Fin R) (hj : j ∈ targets) (f : FineWord 3 N)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f) :
    (targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)).card =
      compatibilityCount shape coarse mu n := by
  classical
  have hc := Nat.card_congr (compatibleTargetEquiv component shape mu n targets f hn hinj hcomplete)
  rw [assignment_count_of_useful component shape coarse hshape mu n j f (hn j hj) hg hp] at hc
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc

theorem indexed_compatible_excluding_owner_count {N k R : ℕ}
    (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R))
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g)
    (j : Fin R) (hj : j ∈ targets) (f : FineWord 3 N)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f) :
    (targets.filter (fun b ↦ b ≠ j ∧ ZCompatible component shape fourthLeftTag mu b f)).card =
      compatibilityCount shape coarse mu n - 1 := by
  classical
  have hjc : ZCompatible component shape fourthLeftTag mu j f :=
    ⟨hg,fun c _ l ↦ hp c l⟩
  have he : targets.filter (fun b ↦ b ≠ j ∧ ZCompatible component shape fourthLeftTag mu b f) =
      (targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)).erase j := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [he, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hj,hjc⟩),
    indexed_compatible_count component shape coarse hshape mu n targets hn hinj hcomplete j hj f hg hp]

theorem uniform_hzCard {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R))
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g) :
    ∀ j ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape j 2 f ∧ Profile component fourthLeftTag mu j 2 f →
      (targets.filter (fun b ↦ b ≠ j ∧ ZCompatible component shape fourthLeftTag mu b f)).card ≤
        compatibilityCount shape coarse mu n - 1 := by
  intro j hj f hf
  exact (indexed_compatible_excluding_owner_count component shape coarse hshape mu n
    targets hn hinj hcomplete j hj f hf.1 hf.2).le

end MME.DWZActualFineZCompatibility
end

/- Checked source module: DWZActualFineZCompatibilityExists. -/
section
open BigOperators MME.CompleteSplit MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZActualFineZCompatibility

theorem exists_prescribed_assignment {A L : Type*} [Fintype A] [DecidableEq A]
    [Fintype L] [DecidableEq L] (counts : L → ℕ)
    (hsum : (∑ l, counts l) = Fintype.card A) :
    ∃ g : A → L, ∀ l, Fintype.card {a : A // g a = l} = counts l := by
  classical
  have hc := mme_fintype_prescribed_fiber_function_card (α := A) counts hsum
  have hpos : 0 < Fintype.card
      {g : A → L // ∀ l, Fintype.card {a : A // g a = l} = counts l} := by
    rw [hc, ← hsum]
    exact Nat.multinomial_pos Finset.univ counts
  obtain ⟨g⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨g.val,g.property⟩

theorem useful_fine_exists {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (j : Fin R) (hn : ∀ c, Fintype.card {t : Fin N // component j t = c} = n c)
    (hrows : ∀ c, (∑ l, mu 2 c l) = n c)
    (hreal : ∀ c l, 0 < mu 2 c l → ∃ v : CompleteWord 3,
      (∑ r, (v r).val) = shape c 2 ∧ fourthLeftTag v = l) :
    ∃ f : FineWord 3 N, Graded component shape j 2 f ∧
      Profile component fourthLeftTag mu j 2 f := by
  classical
  have hassign (c : Fin k) : ∃ g : {t : Fin N // component j t = c} → Fin 5,
      ∀ l, Fintype.card {t // g t = l} = mu 2 c l := by
    have hsum : (∑ l, mu 2 c l) = Fintype.card {t : Fin N // component j t = c} :=
      (hrows c).trans (hn c).symm
    obtain ⟨g,hg⟩ := exists_prescribed_assignment
      (A := {t : Fin N // component j t = c}) (mu 2 c) hsum
    exact ⟨g,hg⟩
  let localTag := fun c ↦ Classical.choose (hassign c)
  let tag : Fin N → Fin 5 := fun t ↦ localTag (component j t) ⟨t,rfl⟩
  have htag (c : Fin k) (t : {t : Fin N // component j t = c}) : tag t.val = localTag c t := by
    rcases t with ⟨t,ht⟩
    cases ht
    rfl
  have hcounts (c : Fin k) (l : Fin 5) :
      Fintype.card {t : Fin N // component j t = c ∧ tag t = l} = mu 2 c l := by
    let e : {t : Fin N // component j t = c ∧ tag t = l} ≃
        {t : {t : Fin N // component j t = c} // localTag c t = l} := {
      toFun := fun t ↦ ⟨⟨t.val,t.property.1⟩,
        (htag c ⟨t.val,t.property.1⟩).symm.trans t.property.2⟩
      invFun := fun t ↦ ⟨t.val.val,t.val.property,(htag c t.val).trans t.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    exact (Fintype.card_congr e).trans (Classical.choose_spec (hassign c) l)
  have hpos (t : Fin N) : 0 < mu 2 (component j t) (tag t) := by
    rw [← hcounts]
    exact Fintype.card_pos_iff.mpr ⟨⟨t,rfl,rfl⟩⟩
  have hv (t : Fin N) := hreal (component j t) (tag t) (hpos t)
  let f : FineWord 3 N := fun t ↦ Classical.choose (hv t)
  refine ⟨f,fun t ↦ (Classical.choose_spec (hv t)).1,?_⟩
  intro c l
  calc
    _ = Fintype.card {t : Fin N // component j t = c ∧ tag t = l} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro t
      rw [(Classical.choose_spec (hv t)).2]
    _ = _ := hcounts c l

end MME.DWZActualFineZCompatibility
end

/- Checked source module: DWZQ5ExactDataSplitRealization. -/
section
open BigOperators MME.CompleteSplit MME.DWZSimultaneous
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace MME.DWZQ5ExactData

theorem fourth_split_realization : ∀ (K : Fin 9) (a : Fin 5),
    a.val ≤ K.val ∧ K.val ≤ a.val + 4 →
    ∃ v : CompleteWord 3,
      (∑ r, (v r).val) = K.val ∧ fourthLeftTag v = a := by
  decide

end MME.DWZQ5ExactData
end

/- Checked source module: DWZQ5ConcreteCounting. -/
section
open BigOperators MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZQ5ExactConstruction

open MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open MME.DWZExactIndexedFamilies MME.DWZActualFineZCompatibility

theorem labelShape_eq : labelShape supportedLabelEquiv = shape := rfl

noncomputable def M (t : ℕ) : Fin 3 → ℕ → ℕ := marginalOf shape (n t)

noncomputable def tables (t : ℕ) : Finset (FourthCell → Fin (N t + 1)) :=
  Finset.univ.filter (fun h ↦ ∀ i : Fin 3, ∀ g : Fin 9,
    (∑ s : {s : FourthCell // s.val i = g}, (h s.val).val) = M t i g.val)

noncomputable def degree (t : ℕ) (mode : Fin 3) : ℕ :=
  ∑ h ∈ tables t, ∏ g : Fin 9, (M t mode g.val).factorial /
    ∏ s : {s : FourthCell // s.val mode = g}, ((h s.val).val).factorial

noncomputable def CZ (t : ℕ) : ℕ :=
  compatibilityCount shape (fun c ↦ coarseAddress c 2) (mu t) (n t)

theorem M_eq (t : ℕ) (i : Fin 3) (g : Fin 9) :
    M t i g.val = marginal i g * (D * t) := by
  classical
  unfold M marginalOf
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : Fin 45 ↦ shape c i = g.val))
    (by intro c; simp) (n t), Finset.sum_filter]
  simpa only [shape, Fin.val_inj] using scaled_marginals t i g

/-- All finite objects needed by the simultaneous q=5 construction are built
from the literal candidate data. The ambient family contains all marginal types. -/
theorem complete_counting_families (t : ℕ) (ht : 0 < t) :
    0 < N t ∧
    (∃ (R : ℕ) (word : Fin R → Fin (N t) → Fin 45) (targets : Finset (Fin R)),
      Function.Injective word ∧
      Function.Injective (owner word shape) ∧
      (∀ a, SameMarginal (M t) (owner word shape a)) ∧
      (∀ a, Supported 8 (owner word shape a)) ∧
      (∀ a : CoarseAddress (N t), Supported 8 a → SameMarginal (M t) a →
        ∃ b, owner word shape b = a) ∧
      (∀ a, a ∈ targets ↔ ExactHistogram (n t) (word a)) ∧
      (∀ w : Fin (N t) → Fin 45, ExactHistogram (n t) w →
        ∃ a ∈ targets, word a = w) ∧
      targets.card = (N t).factorial / ∏ c, (n t c).factorial ∧
      targets.Nonempty ∧
      (∃ positions : ∀ a : Fin R, a ∈ targets → (Fin (N t) ≃ Σ c, Fin (n t c)),
        ∀ a ha c r, word a ((positions a ha).symm ⟨c, r⟩) = c) ∧
      (∀ (mode : Fin 3) (a : Fin R),
        (Finset.univ.filter (fun b ↦ owner word shape b mode =
          owner word shape a mode)).card = degree t mode) ∧
      (∀ a ∈ targets, ∀ f : FineWord 3 (N t),
        Graded word shape a 2 f → Profile word fourthLeftTag (mu t) a 2 f →
        (targets.filter (fun b ↦ ZCompatible word shape fourthLeftTag (mu t) b f)).card = CZ t ∧
        (targets.filter (fun b ↦ b ≠ a ∧ ZCompatible word shape fourthLeftTag (mu t) b f)).card = CZ t - 1 ∧
        (∀ (g : Fin 9) (l : Fin 5),
          Fintype.card {x : Fin (N t) // fineLabel f x = (g,l)} =
            fineMass (fun c ↦ coarseAddress c 2) (mu t) (g,l)) ∧
        (∀ b, ZCompatible word shape fourthLeftTag (mu t) b f →
          ∀ (g : Fin 9) (l : Fin 5),
            Fintype.card {x : Fin (N t) // shape (word b x) 2 = g.val ∧
              fourthLeftTag (f x) = l} =
                fineMass (fun c ↦ coarseAddress c 2) (mu t) (g,l))) ∧
      (∀ a ∈ targets, ∃ f : FineWord 3 (N t),
        Graded word shape a 2 f ∧ Profile word fourthLeftTag (mu t) a 2 f)) := by
  classical
  refine ⟨N_pos t ht, ?_⟩
  obtain ⟨R, word, targets, hword, howner, hmarginal, hsupported,
    hcomplete, hmem, hwords, hcard, hnonempty, hpositions⟩ :=
      indexed_families_complete (N t) 45 supportedLabelEquiv (n t) rfl
  change Function.Injective (owner word shape) at howner
  change ∀ a, SameMarginal (M t) (owner word shape a) at hmarginal
  change ∀ a, Supported 8 (owner word shape a) at hsupported
  change ∀ a : CoarseAddress (N t), Supported 8 a → SameMarginal (M t) a →
    ∃ b, owner word shape b = a at hcomplete
  refine ⟨R, word, targets, hword, howner, hmarginal, hsupported,
    hcomplete, hmem, hwords, hcard, hnonempty, hpositions, ?_, ?_, ?_⟩
  · intro mode a
    exact indexed_ambient_mode_star_card (N t) 45 R supportedLabelEquiv (n t)
      word howner hmarginal hcomplete mode a
  · intro a ha f hg hp
    have hn : ∀ b ∈ targets, ∀ c,
        Fintype.card {x : Fin (N t) // word b x = c} = n t c :=
      fun b hb ↦ (hmem b).mp hb
    have hi : Set.InjOn word (targets : Set (Fin R)) := hword.injOn
    refine ⟨indexed_compatible_count word shape (fun c ↦ coarseAddress c 2)
      (fun _ ↦ rfl) (mu t) (n t) targets hn hi hwords a ha f hg hp,
      indexed_compatible_excluding_owner_count word shape (fun c ↦ coarseAddress c 2)
      (fun _ ↦ rfl) (mu t) (n t) targets hn hi hwords a ha f hg hp, ?_, ?_⟩
    · intro g l
      exact useful_fine_histogram word shape (fun c ↦ coarseAddress c 2)
        (fun _ ↦ rfl) (mu t) a f hg hp (g,l)
    · intro b hb g l
      exact aggregate_of_useful word shape (fun c ↦ coarseAddress c 2)
        (fun _ ↦ rfl) (mu t) a b f hg hp hb.1 g l
  · intro a ha
    apply useful_fine_exists word shape (mu t) (n t) a ((hmem a).mp ha) (mu_sum t)
    intro c l hl
    exact fourth_split_realization (coarseAddress c 2) l (mu_support t c l hl)

end MME.DWZQ5ExactConstruction
end

open BigOperators MME.DWZSimultaneous MME.CompleteSplit
  MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 150000

attribute [local irreducible] MME.DWZQ5ExactData.rawProfile
  MME.DWZQ5ExactData.rawCount MME.DWZQ5ExactData.rawDenominator
  MME.DWZQ5ExactData.component MME.DWZQ5ExactData.scale
  MME.DWZQ5ExactData.marginal MME.DWZFourthGlobalWitness.coarseAddress

attribute [local irreducible] MME.DWZActualFineZCompatibility.compatibilityCount

theorem solution (t : ℕ) (ht : 0 < t) :
    let D := ∏ c : Fin 45, (rawProfile c).denominator
    let m := fun c : Fin 45 ↦ component c * (D * t) / (rawProfile c).denominator
    let n := fun c : Fin 45 ↦ (rawProfile c).length (m c)
    let N := ∑ c : Fin 45, n c
    let shape : Fin 45 → Fin 3 → ℕ := fun c i ↦ (coarseAddress c i).val
    let z := fun c (l : Fin 5) ↦ (rawProfile c).count l * m c
    let mu : Fin 3 → Fin 45 → Fin 5 → ℕ := fun
      | 0, c, l => if shape c 1 = 0 then z c (Fin.rev l) else 0
      | 1, c, l => if shape c 0 = 0 then z c (Fin.rev l) else 0
      | 2, c, l => z c l
    let M : Fin 3 → ℕ → ℕ :=
      fun i g ↦ ∑ c : {c : Fin 45 // shape c i = g}, n c.val
    let Cell := {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8}
    let tables : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ s : {s : Cell // s.val i = g}, (h s.val).val) = M i g.val)
    let degree := fun mode : Fin 3 ↦
      ∑ h ∈ tables, ∏ g : Fin 9, (M mode g.val).factorial /
        ∏ s : {s : Cell // s.val mode = g}, ((h s.val).val).factorial
    let coarse := fun c : Fin 45 ↦ coarseAddress c 2
    let boundary := fun c : Fin 45 ↦ shape c 0 = 0 ∨ shape c 1 = 0
    let F := fun i : Fin 9 × Fin 5 ↦
      ∑ c : {c : Fin 45 // coarse c = i.1}, mu 2 c.val i.2
    let pooled : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ := fun
      | (Sum.inl c, (g,l)) => if boundary c ∧ coarse c = g then mu 2 c l else 0
      | (Sum.inr g', (g,l)) => if g' = g then F (g,l) -
          ∑ c ∈ Finset.univ.filter (fun c ↦ boundary c ∧ coarse c = g), mu 2 c l
        else 0
    let collapse := fun c : Fin 45 ↦ if boundary c then Sum.inl c else Sum.inr (coarse c)
    let W :=
      (∏ i : Fin 9 × Fin 5, (F i).factorial /
        ∏ di : {di : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
          (pooled di.val).factorial) *
      (∏ d : Fin 45 ⊕ Fin 9, (∑ i, pooled (d,i)).factorial /
        ∏ c : {c : Fin 45 // collapse c = d}, (n c.val).factorial)
    0 < D ∧
    N = scale * (D * t) ∧
    (∀ c : Fin 45, n c = component c * (D * t)) ∧
    (∀ c : Fin 45, 0 < n c) ∧
    (∀ (i : Fin 3) (g : Fin 9), M i g.val = marginal i g * (D * t)) ∧
    0 < N ∧
    (∃ (R : ℕ) (word : Fin R → Fin N → Fin 45) (targets : Finset (Fin R)),
      Function.Injective word ∧
      Function.Injective (owner word shape) ∧
      (∀ a, SameMarginal M (owner word shape a)) ∧
      (∀ a, Supported 8 (owner word shape a)) ∧
      (∀ a : CoarseAddress N, Supported 8 a → SameMarginal M a →
        ∃ b, owner word shape b = a) ∧
      (∀ a, a ∈ targets ↔
        ∀ c, Fintype.card {x : Fin N // word a x = c} = n c) ∧
      (∀ w : Fin N → Fin 45, (∀ c, Fintype.card {x : Fin N // w x = c} = n c) →
        ∃ a ∈ targets, word a = w) ∧
      targets.card = N.factorial / ∏ c, (n c).factorial ∧
      targets.Nonempty ∧
      (∃ positions : ∀ a : Fin R, a ∈ targets → (Fin N ≃ Σ c, Fin (n c)),
        ∀ a ha c r, word a ((positions a ha).symm ⟨c, r⟩) = c) ∧
      (∀ (mode : Fin 3) (a : Fin R),
        (Finset.univ.filter (fun b ↦ owner word shape b mode =
          owner word shape a mode)).card = degree mode) ∧
      (∀ a ∈ targets, ∀ f : FineWord 3 N,
        Graded word shape a 2 f → Profile word fourthLeftTag mu a 2 f →
        (targets.filter (fun b ↦ ZCompatible word shape fourthLeftTag mu b f)).card = W ∧
        (targets.filter (fun b ↦ b ≠ a ∧ ZCompatible word shape fourthLeftTag mu b f)).card = W - 1 ∧
        (∀ b, ZCompatible word shape fourthLeftTag mu b f →
          ∀ (g : Fin 9) (l : Fin 5),
            Fintype.card {x : Fin N // shape (word b x) 2 = g.val ∧
              fourthLeftTag (f x) = l} = F (g,l))) ∧
      (∀ a ∈ targets, ∃ f : FineWord 3 N,
        Graded word shape a 2 f ∧ Profile word fourthLeftTag mu a 2 f)) := by
  classical
  intro D m n N shape z mu M Cell tables degree coarse boundary F pooled collapse W
  refine ⟨MME.DWZQ5ExactConstruction.D_pos,
    MME.DWZQ5ExactConstruction.N_eq t,
    MME.DWZQ5ExactConstruction.n_eq t,
    MME.DWZQ5ExactConstruction.n_pos t ht,
    MME.DWZQ5ExactConstruction.M_eq t,
    MME.DWZQ5ExactConstruction.N_pos t ht, ?_⟩
  obtain ⟨_, R, word, targets, hword, howner, hmarginal, hsupported,
    hcomplete, hmem, hwords, hcard, hnonempty, hpositions, hdegree, hcompatible,
    huseful⟩ := MME.DWZQ5ExactConstruction.complete_counting_families t ht
  refine ⟨R, word, targets, hword, howner, hmarginal, hsupported,
    hcomplete, hmem, hwords, hcard, hnonempty, hpositions, hdegree, ?_, huseful⟩
  intro a ha f hg hp
  obtain ⟨hcount, hother, _, haggregate⟩ := hcompatible a ha f hg hp
  have hW : MME.DWZQ5ExactConstruction.CZ t = W := by
    have hmu : MME.DWZQ5ExactConstruction.mu t = mu := by
      funext i c l
      fin_cases i <;> rfl
    unfold MME.DWZQ5ExactConstruction.CZ
    rw [hmu]
    change MME.DWZActualFineZCompatibility.compatibilityCount shape coarse mu n = W
    have hF (i : Fin 9 × Fin 5) :
        MME.DWZActualFineZCompatibility.fineMass coarse mu i = F i := by
      unfold MME.DWZActualFineZCompatibility.fineMass
      dsimp only [F]
    have hpool (i : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5)) :
        MME.DWZActualFineZCompatibility.pooledMass shape coarse mu i = pooled i := by
      rcases i with ⟨d,g,l⟩
      cases d with
      | inl c =>
        simp only [MME.DWZActualFineZCompatibility.pooledMass, pooled,
          MME.DWZActualFineZCompatibility.boundary, boundary]
        split_ifs <;> rfl
      | inr g' =>
        simp only [MME.DWZActualFineZCompatibility.pooledMass, pooled,
          MME.DWZActualFineZCompatibility.boundary, boundary]
        split_ifs
        · apply congrArg₂ Nat.sub
          · exact hF (g,l)
          · apply Finset.sum_congr
            · ext c
              simp only [Finset.mem_filter, Finset.mem_univ]
            · intro c _
              rfl
        · rfl
    have hcollapse (c : Fin 45) :
        MME.DWZActualFineZCompatibility.collapse shape coarse c = collapse c := by
      by_cases hb : boundary c
      · simp only [MME.DWZActualFineZCompatibility.collapse,
          MME.DWZActualFineZCompatibility.boundary, collapse, boundary] at *
        rw [if_pos hb, if_pos hb]
      · simp only [MME.DWZActualFineZCompatibility.collapse,
          MME.DWZActualFineZCompatibility.boundary, collapse, boundary] at *
        rw [if_neg hb, if_neg hb]
    unfold MME.DWZActualFineZCompatibility.compatibilityCount
    dsimp only [W]
    apply congrArg₂ Nat.mul
    · apply Finset.prod_congr rfl
      intro i _
      apply congrArg₂ Nat.div
      · exact congrArg Nat.factorial (hF i)
      · apply Finset.prod_congr
        · ext di
          simp only [Finset.mem_univ]
        · intro di _
          exact congrArg Nat.factorial (hpool di.val)
    · apply Finset.prod_congr rfl
      intro d _
      apply congrArg₂ Nat.div
      · apply congrArg Nat.factorial
        apply Finset.sum_congr rfl
        intro i _
        exact hpool (d,i)
      · let e : {c : Fin 45 // MME.DWZActualFineZCompatibility.collapse shape coarse c = d} ≃
            {c : Fin 45 // collapse c = d} :=
          Equiv.subtypeEquivRight (fun c ↦ by rw [hcollapse c])
        exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)
  exact ⟨hcount.trans hW, hother.trans (congrArg (fun w : ℕ ↦ w - 1) hW), haggregate⟩
