-- Prove2me | solution 1 for mme_dwz_fourth_exact_indexed_families
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T21:28:42.33421+00:00
-- url     : https://prove2.me/submissions/deba96b7-f116-414b-be58-66a7eb507366

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_dwz_fourth_ambient_mode_star_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FinCases

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

theorem solution (N k : ℕ)
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
  exact MME.DWZExactIndexedFamilies.complete_indexed_families N k sigma n hn

