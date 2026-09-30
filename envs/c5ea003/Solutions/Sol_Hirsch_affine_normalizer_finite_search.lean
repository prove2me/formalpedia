-- Prove2me | solution 1 for Hirsch.affine_normalizer_finite_search
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-22T19:28:59.048779+00:00
-- url     : https://prove2.me/submissions/56cc888e-a904-4dff-8695-c0be8e26804d

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.NormalizerSearch

variable {d : ℕ}

abbrev Slope (d : ℕ) := (Fin d → ℝ) →ₗ[ℝ] ℝ

def denominator (u : Fin d → ℝ) (D : Slope d) (x : Fin d → ℝ) : ℝ :=
  1+D (x-u)

def value (s : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ) (D : Slope d)
    (x : Fin d → ℝ) : ℝ := s x / denominator u D x

def Positive (C : Finset (Fin d → ℝ)) (u : Fin d → ℝ) (D : Slope d) : Prop :=
  ∀ x ∈ C, 0 < denominator u D x

def contrast (s : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ)
    (p : (Fin d → ℝ) × (Fin d → ℝ)) : Fin d → ℝ :=
  s p.1 • (p.2-u)-s p.2 • (p.1-u)

def Equations (s : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ)
    (B : Finset ((Fin d → ℝ) × (Fin d → ℝ))) (D : Slope d) : Prop :=
  ∀ p ∈ B, D (contrast s u p)=s p.2-s p.1

noncomputable def bases (C : Finset (Fin d → ℝ)) :
    Finset (Finset ((Fin d → ℝ) × (Fin d → ℝ))) := by
  classical
  exact (C.product C).powerset.filter (fun B => B.card ≤ d)

/-- Every finite family of linear tests has at most ambient dimension many
original tests with exactly the same common kernel. The tests are selected,
not provided as an independent-basis hypothesis. -/
theorem compress_tests {ι : Type*} (T : Finset ι) (w : ι → (Fin d → ℝ)) :
    ∃ B : Finset ι, B ⊆ T ∧ B.card ≤ d ∧
      ∀ L : Slope d, (∀ i ∈ B, L (w i)=0) → ∀ i ∈ T, L (w i)=0 := by
  classical
  let f : T → (Fin d → ℝ) := fun i => w i.val
  have hempty : LinearIndepOn ℝ f (∅ : Set T) := by simp
  obtain ⟨S,hSsub,hbase,hspan,hS⟩ :=
    exists_linearIndepOn_extension hempty (Set.empty_subset (Set.univ : Set T))
  let J : Finset T := Finset.univ.filter (fun i => i ∈ S)
  let emb : J → S := fun i => ⟨i.val,(Finset.mem_filter.mp i.property).2⟩
  have hemb : Function.Injective emb := by
    intro i j he
    exact Subtype.ext (congrArg (fun t : S => t.val) he)
  have hSind : LinearIndependent ℝ (fun i : S => f i.val) := hS
  have hJind : LinearIndependent ℝ (fun i : J => f i.val) := hSind.comp emb hemb
  have hJcard : J.card ≤ d := by
    have h := hJind.fintype_card_le_finrank
    simpa only [Fintype.card_coe,Module.finrank_pi,Module.finrank_self,
      Fintype.card_fin] using h
  let B := J.image (fun i : T => i.val)
  have hBT : B ⊆ T := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact j.property
  have hBc : B.card ≤ d := Finset.card_image_le.trans hJcard
  refine ⟨B,hBT,hBc,?_⟩
  intro L hL
  have hle : Submodule.span ℝ (f '' S) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro z ⟨i,hi,rfl⟩
    change L (w i.val)=0
    apply hL
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  intro i hi
  let j : T := ⟨i,hi⟩
  exact hle (hspan ⟨j,Set.mem_univ _,rfl⟩)

/-- Ratio coincidences are AFFINE LINEAR equations in the normalized slope.
Positivity is necessary: zero denominators must not be accepted as ties. -/
lemma tie_iff (s : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ) (D : Slope d)
    (x y : Fin d → ℝ) (hx : 0 < denominator u D x)
    (hy : 0 < denominator u D y) :
    value s u D x=value s u D y ↔
      D (contrast s u (x,y))=s y-s x := by
  unfold value
  rw [div_eq_div_iff (ne_of_gt hx) (ne_of_gt hy)]
  simp only [denominator,contrast,map_sub,map_smul,smul_eq_mul]
  constructor <;> intro h <;> nlinarith

/-- The full coincidence pattern of ANY positive denominator is preserved by
at most d of its original pair equations. Other feasible solutions may merge
additional values, which can only help the spectrum bound. -/
theorem compress_ties (C : Finset (Fin d → ℝ)) (s : (Fin d → ℝ) → ℝ)
    (u : Fin d → ℝ) (D₀ : Slope d) (h₀ : Positive C u D₀) :
    ∃ B ∈ bases C, Equations s u B D₀ ∧
      ∀ D : Slope d, Positive C u D → Equations s u B D →
        ∀ x ∈ C, ∀ y ∈ C, value s u D₀ x=value s u D₀ y →
          value s u D x=value s u D y := by
  classical
  let T := (C.product C).filter (fun p => value s u D₀ p.1=value s u D₀ p.2)
  obtain ⟨B,hBT,hBc,hker⟩ := compress_tests T (contrast s u)
  have hBE : B ⊆ C.product C := hBT.trans (Finset.filter_subset _ _)
  have hbase : B ∈ bases C := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hBE,hBc⟩
  have heq₀ : Equations s u B D₀ := by
    intro p hp
    obtain ⟨hpE,htie⟩ := Finset.mem_filter.mp (hBT hp)
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hpE
    exact (tie_iff s u D₀ p.1 p.2 (h₀ _ hx) (h₀ _ hy)).mp htie
  refine ⟨B,hbase,heq₀,?_⟩
  intro D hD hB x hx y hy htie
  apply (tie_iff s u D x y (hD x hx) (hD y hy)).mpr
  have hL : ∀ p ∈ B, (D-D₀) (contrast s u p)=0 := by
    intro p hp
    change D (contrast s u p)-D₀ (contrast s u p)=0
    rw [hB p hp,heq₀ p hp,sub_self]
  have hxy : (x,y) ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hx,hy⟩,htie⟩
  have hz := hker (D-D₀) hL (x,y) hxy
  change D (contrast s u (x,y))-D₀ (contrast s u (x,y))=0 at hz
  rw [sub_eq_zero.mp hz]
  exact (tie_iff s u D₀ x y (h₀ x hx) (h₀ y hy)).mp htie

/-- Coarsening a finite value partition cannot increase its number of values. -/
lemma image_card_of_ties {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (C : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ x ∈ C, ∀ y ∈ C, f x=f y → g x=g y) :
    (C.image g).card ≤ (C.image f).card := by
  classical
  let S := C.image f
  let T := C.image g
  have hrep : ∀ a : S, ∃ x ∈ C, f x=a.val := by
    intro a
    exact Finset.mem_image.mp a.property
  choose r hrC hrf using hrep
  let F : S → T := fun a => ⟨g (r a),Finset.mem_image.mpr ⟨r a,hrC a,rfl⟩⟩
  have hsurj : Function.Surjective F := by
    intro b
    obtain ⟨x,hx,hgx⟩ := Finset.mem_image.mp b.property
    let a : S := ⟨f x,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
    refine ⟨a,?_⟩
    apply Subtype.ext
    change g (r a)=b.val
    exact (h (r a) (hrC a) x hx (hrf a)).trans hgx
  have hc := Fintype.card_le_of_surjective F hsurj
  simpa only [Fintype.card_coe] using hc

/-- Anchoring at one actual point loses no affine denominator. Its normalized
ratios differ by one positive common scalar, so every coincidence is retained. -/
lemma anchor (C : Finset (Fin d → ℝ)) (s : (Fin d → ℝ) → ℝ)
    (u : Fin d → ℝ) (hu : u ∈ C) (a : ℝ) (D : Slope d)
    (hpos : ∀ x ∈ C, 0 < a+D x) :
    ∃ E : Slope d, Positive C u E ∧
      ∀ x ∈ C, ∀ y ∈ C,
        s x/(a+D x)=s y/(a+D y) → value s u E x=value s u E y := by
  let t := a+D u
  have ht : 0 < t := hpos u hu
  let E : Slope d := t⁻¹ • D
  have hq : ∀ x, denominator u E x=(a+D x)/t := by
    intro x
    change 1+t⁻¹*D (x-u)=(a+D x)/t
    rw [map_sub]
    field_simp [ne_of_gt ht]
    <;> dsimp [t] <;> ring
  have hE : Positive C u E := by
    intro x hx
    rw [hq]
    exact div_pos (hpos x hx) ht
  have hv : ∀ x ∈ C, value s u E x=t*(s x/(a+D x)) := by
    intro x hx
    unfold value
    rw [hq]
    field_simp [ne_of_gt ht,ne_of_gt (hpos x hx)]
    <;> ring
  refine ⟨E,hE,?_⟩
  intro x hx y hy he
  rw [hv x hx,hv y hy,he]

/-- Choose one witness for every feasible finite linear system, and the zero
slope otherwise. This is a finite mathematical construction, not an oracle
for a small spectrum and not a polynomial-time complexity claim. -/
theorem catalogue (C : Finset (Fin d → ℝ)) (s : (Fin d → ℝ) → ℝ)
    (u : Fin d → ℝ) (hu : u ∈ C) :
    ∃ pick : bases C → Slope d,
      (∀ B, Positive C u (pick B)) ∧
      (∀ B, (∃ D : Slope d, Positive C u D ∧ Equations s u B.val D) →
        Equations s u B.val (pick B)) ∧
      (∀ a : ℝ, ∀ D : Slope d, (∀ x ∈ C, 0 < a+D x) →
        ∃ B : bases C,
          (∀ x ∈ C, ∀ y ∈ C, s x/(a+D x)=s y/(a+D y) →
            value s u (pick B) x=value s u (pick B) y) ∧
          (C.image (value s u (pick B))).card ≤
            (C.image (fun x => s x/(a+D x))).card) ∧
      ∃ B : bases C, ∀ a : ℝ, ∀ D : Slope d,
        (∀ x ∈ C, 0 < a+D x) →
          (C.image (value s u (pick B))).card ≤
            (C.image (fun x => s x/(a+D x))).card := by
  classical
  have hchoice : ∀ B : bases C, ∃ D : Slope d, Positive C u D ∧
      ((∃ E : Slope d, Positive C u E ∧ Equations s u B.val E) →
        Equations s u B.val D) := by
    intro B
    by_cases hf : ∃ E : Slope d, Positive C u E ∧ Equations s u B.val E
    · obtain ⟨E,hE,hEq⟩ := hf
      exact ⟨E,hE,fun _ => hEq⟩
    · refine ⟨0,?_,fun h => (hf h).elim⟩
      intro x hx
      simp [denominator]
  choose pick hpositive hsolve using hchoice
  have hcover : ∀ a : ℝ, ∀ D : Slope d, (∀ x ∈ C, 0 < a+D x) →
      ∃ B : bases C,
        (∀ x ∈ C, ∀ y ∈ C, s x/(a+D x)=s y/(a+D y) →
          value s u (pick B) x=value s u (pick B) y) ∧
        (C.image (value s u (pick B))).card ≤
          (C.image (fun x => s x/(a+D x))).card := by
    intro a D hD
    obtain ⟨E,hE,hanchor⟩ := anchor C s u hu a D hD
    obtain ⟨B,hB,hBE,hkeep⟩ := compress_ties C s u E hE
    let B' : bases C := ⟨B,hB⟩
    have hsol : Equations s u B (pick B') := hsolve B' ⟨E,hE,hBE⟩
    have hties : ∀ x ∈ C, ∀ y ∈ C, s x/(a+D x)=s y/(a+D y) →
        value s u (pick B') x=value s u (pick B') y := by
      intro x hx y hy he
      exact hkeep (pick B') (hpositive B') hsol x hx y hy (hanchor x hx y hy he)
    exact ⟨B',hties,image_card_of_ties C _ _ hties⟩
  have hempty : (∅ : Finset ((Fin d → ℝ) × (Fin d → ℝ))) ∈ bases C := by
    simp [bases]
  let emptyBase : bases C := ⟨∅,hempty⟩
  obtain ⟨B,hBu,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (bases C))
    (fun B => (C.image (value s u (pick B))).card) ⟨emptyBase,Finset.mem_univ _⟩
  refine ⟨pick,hpositive,hsolve,hcover,B,?_⟩
  intro a D hD
  obtain ⟨R,hRtie,hRcard⟩ := hcover a D hD
  exact (hmin R (Finset.mem_univ _)).trans hRcard

end Hirsch.NormalizerSearch

/-- Complete finite linear search for the best positive affine normalization.
Only C, its anchor, and scalar numerator data are inputs. -/
theorem solution (d : ℕ) (C : Finset (Fin d → ℝ))
    (s : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ) (hu : u ∈ C) :
    let F := (C.product C).powerset.filter (fun B => B.card ≤ d)
    ∃ pick : F → ((Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ B, ∀ x ∈ C, 0 < 1+pick B (x-u)) ∧
      (∀ B, (∃ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < 1+D (x-u)) ∧
          ∀ p ∈ B.val, D (s p.1 • (p.2-u)-s p.2 • (p.1-u))=s p.2-s p.1) →
        ∀ p ∈ B.val, pick B (s p.1 • (p.2-u)-s p.2 • (p.1-u))=s p.2-s p.1) ∧
      (∀ a : ℝ, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < a+D x) → ∃ B : F,
          (∀ x ∈ C, ∀ y ∈ C, s x/(a+D x)=s y/(a+D y) →
            s x/(1+pick B (x-u))=s y/(1+pick B (y-u))) ∧
          (C.image (fun x => s x/(1+pick B (x-u)))).card ≤
            (C.image (fun x => s x/(a+D x))).card) ∧
      ∃ B : F, ∀ a : ℝ, ∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        (∀ x ∈ C, 0 < a+D x) →
          (C.image (fun x => s x/(1+pick B (x-u)))).card ≤
            (C.image (fun x => s x/(a+D x))).card := by
  classical
  exact Hirsch.NormalizerSearch.catalogue C s u hu

#print axioms Hirsch.NormalizerSearch.compress_tests
#print axioms Hirsch.NormalizerSearch.compress_ties
#print axioms Hirsch.NormalizerSearch.image_card_of_ties
#print axioms Hirsch.NormalizerSearch.anchor
#print axioms Hirsch.NormalizerSearch.catalogue
#print axioms solution
