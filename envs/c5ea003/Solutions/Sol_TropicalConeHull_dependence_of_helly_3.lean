-- Prove2me | solution 3 for TropicalConeHull.dependence_of_helly
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:57:10.795174+00:00
-- url     : https://prove2.me/submissions/97821b73-562d-40c6-8767-07c2605b6a4a

import Mathlib
import Definitions.Def_Tropical_TropicalConvexity_ConeHullOptimization

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Tropical/TropicalConvexity/ConeHullOptimization.lean ====
/-!
# Tropical cone hulls, Carathéodory number `d`, and max-plus residuation

This file complements the tropical Helly theory with the two other pillars of
tropical convexity: the **Carathéodory number** of tropical cones in `ℝ^d`
(which is `d`, one better than the affine normalized bound `d + 1`), and the
**optimization side**: the residuation (Galois) correspondence for max-plus
linear systems, giving the greatest subsolution of `A ⊗ x ≤ b` together with a
complete solvability criterion for `A ⊗ x = b`.

## Main results

* `TropicalConeHull.tropical_caratheodory_cone` — Carathéodory number `d`.
* `TropicalConeHull.caratheodory_cone_sharp` — the bound `d` cannot be improved.
* `TropicalConeHull.colorful_caratheodory` — colourful Carathéodory theorem.
* `TropicalConeHull.dependence_of_helly` — the converse implication
  "tropical Helly ⇒ tropical Cramer dependence", so that the Helly theorem of
  `HellyNumber.lean` and the dependence theorem behind it are *equivalent*.
* `TropicalResiduation.mulVec_le_iff_le_resid` — the residuation Galois
  connection for max-plus linear inequalities.
* `TropicalResiduation.tropical_solvable_iff` — `A ⊗ x = b` is solvable iff the
  canonical candidate `resid A b` solves it (Cuninghame-Green's principal
  solution): an `O(mn)` decision procedure for max-plus linear systems.
-/

open Finset

namespace TropicalConeHull

variable {d : ℕ} {ι : Type*}

-- [dropped: platform already declares tropConeHull]
/-- Every generator lies in the hull of the singleton it spans. -/
theorem mem_tropConeHull_self [DecidableEq ι] (p : ι → Fin d → ℝ) (k : ι) :
    p k ∈ tropConeHull p {k} := by
  refine ⟨fun _ => 0, ⟨k, by simp⟩, fun i => ?_⟩
  simp

/-- **Tropical Carathéodory theorem for cones (Carathéodory number `d`).**
Every point of the tropical cone hull of a finite family in `ℝ^d` already lies
in the hull of at most `d` of the generators — one generator per coordinate. -/
theorem tropical_caratheodory_cone (hd : 0 < d) (p : ι → Fin d → ℝ)
    (F : Finset ι) (z : Fin d → ℝ) (hz : z ∈ tropConeHull p F) :
    ∃ G ⊆ F, G.card ≤ d ∧ z ∈ tropConeHull p G := by
  classical
  obtain ⟨lam, hF, hzeq⟩ := hz
  have hchoice : ∀ i : Fin d, ∃ k ∈ F,
      F.sup' hF (fun k => lam k + p k i) = lam k + p k i :=
    fun i => Finset.exists_mem_eq_sup' hF _
  choose kk hkkF hkk using hchoice
  have hdne : (univ : Finset (Fin d)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]; exact hd
  refine ⟨univ.image kk, ?_, ?_, lam, (hdne.image kk), fun i => ?_⟩
  · intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    exact hkkF i
  · exact le_trans Finset.card_image_le (by simp)
  · refine le_antisymm ?_ ?_
    · rw [hzeq i, hkk i]
      exact Finset.le_sup' (fun k => lam k + p k i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · rw [hzeq i]
      refine Finset.sup'_le _ _ (fun k hk => ?_)
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.le_sup' (fun k => lam k + p k i) (hkkF j)

/-- **Sharpness of the tropical Carathéodory number.**  The `d` "tropical unit
vectors" of `ℝ^d` span a point of their cone hull that lies in the hull of no
proper subfamily.  Hence the Carathéodory number of tropical cones in `ℝ^d` is
exactly `d`. -/
theorem caratheodory_cone_sharp (hd : 0 < d) :
    ∃ (p : Fin d → Fin d → ℝ) (z : Fin d → ℝ),
      z ∈ tropConeHull p univ ∧
      ∀ G : Finset (Fin d), G.card < d → z ∉ tropConeHull p G := by
  classical
  refine ⟨fun k i => if i = k then 0 else -1, fun _ => 0, ⟨fun _ => 0, ?_, fun i => ?_⟩, ?_⟩
  · exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  · refine le_antisymm ?_ ?_
    · have : (0 : ℝ) + (if i = i then (0:ℝ) else -1) ≤
          univ.sup' ⟨⟨0, hd⟩, Finset.mem_univ _⟩
            (fun k => (0:ℝ) + if i = k then (0:ℝ) else -1) :=
        Finset.le_sup' (fun k => (0:ℝ) + if i = k then (0:ℝ) else -1) (Finset.mem_univ i)
      simpa using this
    · refine Finset.sup'_le _ _ (fun k _ => ?_)
      by_cases h : i = k <;> simp [h]
  · rintro G hG ⟨lam, hGne, hz⟩
    -- some coordinate `i₀` is missing from `G`
    have hex : ∃ i₀ : Fin d, i₀ ∉ G := by
      by_contra hcon
      push_neg at hcon
      rw [Finset.eq_univ_of_forall hcon, Finset.card_univ, Fintype.card_fin] at hG
      exact lt_irrefl d hG
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨kstar, hkstar, hks⟩ := Finset.exists_mem_eq_sup' hGne
      (fun k => lam k + if i₀ = k then (0:ℝ) else -1)
    have hne : i₀ ≠ kstar := fun hcon => hi₀ (hcon ▸ hkstar)
    have h1 : lam kstar = 1 := by
      have := hz i₀
      rw [hks] at this
      simp only [hne, if_false] at this
      linarith
    have h2 : lam kstar + (if kstar = kstar then (0:ℝ) else -1)
        ≤ G.sup' hGne (fun k => lam k + if kstar = k then (0:ℝ) else -1) :=
      Finset.le_sup' (fun k => lam k + if kstar = k then (0:ℝ) else -1) hkstar
    have h3 : (if kstar = kstar then (0:ℝ) else -1) = 0 := by simp
    have h4 : G.sup' hGne (fun k => lam k + if kstar = k then (0:ℝ) else -1) = 0 :=
      (hz kstar).symm
    rw [h1, h3, add_zero, h4] at h2
    linarith

/-- **Tropical colourful Carathéodory theorem.**  If a point `z` lies in the
tropical cone hull of each of `d` "colour classes" of points of `ℝ^d`, then it
lies in the hull of a *rainbow* selection — one generator taken from each class.
The selection is explicit: from class `c` take a generator attaining the maximum
in coordinate `c`. -/
theorem colorful_caratheodory (hd : 0 < d) (p : Fin d → ι → Fin d → ℝ)
    (F : Fin d → Finset ι) (z : Fin d → ℝ)
    (hz : ∀ c, z ∈ tropConeHull (p c) (F c)) :
    ∃ (sel : Fin d → ι) (w : Fin d → ℝ), (∀ c, sel c ∈ F c) ∧
      ∀ i, z i = (univ : Finset (Fin d)).sup'
        ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun c => w c + p c (sel c) i) := by
  classical
  choose lam hFne hzeq using hz
  have hchoice : ∀ c : Fin d, ∃ k ∈ F c,
      (F c).sup' (hFne c) (fun k => lam c k + p c k c) = lam c k + p c k c :=
    fun c => Finset.exists_mem_eq_sup' (hFne c) _
  choose sel hselF hsel using hchoice
  refine ⟨sel, fun c => lam c (sel c), hselF, fun i => ?_⟩
  refine le_antisymm ?_ (Finset.sup'_le _ _ (fun c _ => ?_))
  · -- coordinate `i` is covered by the generator chosen for colour `i`
    have h1 : z i = lam i (sel i) + p i (sel i) i := by rw [hzeq i i, hsel i]
    rw [h1]
    exact Finset.le_sup' (fun c => lam c (sel c) + p c (sel c) i) (Finset.mem_univ i)
  · -- every chosen generator is dominated by `z`
    rw [hzeq c i]
    exact Finset.le_sup' (fun k => lam c k + p c k i) (hselF c)

/-! ## The tropical Helly property is *equivalent* to tropical dependence

`HellyNumber.lean` proves the implication "Cramer dependence ⇒ tropical Helly".
Here we close the loop: the Helly property, taken as a hypothesis, forces
`d + 1` points of `ℝ^d` to be tropically dependent.  So the two statements are
two faces of the same phenomenon. -/

-- [dropped: platform already declares IsTropCone]
private lemma sup'_max_comm (F : Finset ι) (hF : F.Nonempty) (f g : ι → ℝ) (s t : ℝ) :
    max (s + F.sup' hF f) (t + F.sup' hF g)
      = F.sup' hF (fun k => max (s + f k) (t + g k)) := by
  refine le_antisymm (max_le ?_ ?_) (Finset.sup'_le _ _ (fun k _ => ?_))
  · obtain ⟨k, hkF, hk⟩ := Finset.exists_mem_eq_sup' hF f
    rw [hk]
    exact le_trans (le_max_left (s + f k) (t + g k))
      (Finset.le_sup' (fun k => max (s + f k) (t + g k)) hkF)
  · obtain ⟨k, hkF, hk⟩ := Finset.exists_mem_eq_sup' hF g
    rw [hk]
    exact le_trans (le_max_right (s + f k) (t + g k))
      (Finset.le_sup' (fun k => max (s + f k) (t + g k)) hkF)
  · exact max_le_max (by gcongr; exact Finset.le_sup' f (by assumption))
      (by gcongr; exact Finset.le_sup' g (by assumption))

/-- The tropical cone hull of a nonempty finite family really is a tropical cone. -/
theorem tropConeHull_isTropCone (p : ι → Fin d → ℝ) {F : Finset ι} (hF : F.Nonempty) :
    IsTropCone (tropConeHull p F) := by
  rintro x ⟨lam, hF1, hx⟩ y ⟨mu, hF2, hy⟩ s t
  have hx' : ∀ i, x i = F.sup' hF (fun k => lam k + p k i) := hx
  have hy' : ∀ i, y i = F.sup' hF (fun k => mu k + p k i) := hy
  refine ⟨fun k => max (s + lam k) (t + mu k), hF, fun i => ?_⟩
  show max (s + x i) (t + y i)
    = F.sup' hF (fun k => max (s + lam k) (t + mu k) + p k i)
  rw [hx' i, hy' i, sup'_max_comm F hF _ _ s t]
  refine Finset.sup'_congr hF rfl (fun k _ => ?_)
  rw [← max_add_add_right]
  ring_nf

/-- Every generator of a family lies in the hull of that family. -/
theorem mem_tropConeHull_of_mem (hd : 0 < d) (p : ι → Fin d → ℝ) {F : Finset ι}
    {k₀ : ι} (hk₀ : k₀ ∈ F) : p k₀ ∈ tropConeHull p F := by
  classical
  have hdne : (univ : Finset (Fin d)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]; exact hd
  refine ⟨fun j => if j = k₀ then 0 else
      (univ.inf' hdne (fun i => p k₀ i)) - (univ.sup' hdne (fun i => p j i)),
    ⟨k₀, hk₀⟩, fun i => ?_⟩
  refine le_antisymm ?_ (Finset.sup'_le _ _ (fun j _ => ?_))
  · have := Finset.le_sup'
      (fun j => (if j = k₀ then (0:ℝ) else
        (univ.inf' hdne (fun i => p k₀ i)) - (univ.sup' hdne (fun i => p j i))) + p j i) hk₀
    simpa using this
  · by_cases hj : j = k₀
    · simp [hj]
    · simp only [hj, if_false]
      have h1 : univ.inf' hdne (fun i => p k₀ i) ≤ p k₀ i :=
        Finset.inf'_le (fun i => p k₀ i) (Finset.mem_univ i)
      have h2 : p j i ≤ univ.sup' hdne (fun i => p j i) :=
        Finset.le_sup' (fun i => p j i) (Finset.mem_univ i)
      linarith

/-- **Tropical Helly implies tropical dependence.**  If in dimension `d` every
family of `d + 1` tropical cones whose `d`-element subfamilies intersect has a
common point, then any `d + 1` points of `ℝ^d` are tropically dependent.
Combined with `TropicalDependence.trop_dependence_fin` (which yields the Helly
theorem in `HellyNumber.lean`), tropical Helly and tropical dependence are
equivalent statements. -/
theorem dependence_of_helly (hd : 0 < d)
    (helly : ∀ C : Fin (d + 1) → Set (Fin d → ℝ), (∀ k, IsTropCone (C k)) →
      (∀ I : Finset (Fin (d + 1)), I.card ≤ d → ∃ x, ∀ k ∈ I, x ∈ C k) →
      ∃ x, ∀ k, x ∈ C k)
    (p : Fin (d + 1) → Fin d → ℝ) :
    ∃ lam : Fin (d + 1) → ℝ, ∀ (i : Fin d) (k : Fin (d + 1)),
      ∃ j, j ≠ k ∧ lam k + p k i ≤ lam j + p j i := by
  classical
  have hdne : (univ : Finset (Fin d)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, Fintype.card_fin]; exact hd
  have herase : ∀ k : Fin (d + 1), ((univ : Finset (Fin (d + 1))).erase k).Nonempty := by
    intro k
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  -- the family of hulls of all but one generator
  obtain ⟨z, hz⟩ := helly (fun k => tropConeHull p (univ.erase k))
    (fun k => tropConeHull_isTropCone p (herase k))
    (by
      intro I hI
      -- some index `k₀` is missing from `I`; the point `p k₀` works
      have hex : ∃ k₀ : Fin (d + 1), k₀ ∉ I := by
        by_contra hcon
        push_neg at hcon
        rw [Finset.eq_univ_of_forall hcon, Finset.card_univ, Fintype.card_fin] at hI
        omega
      obtain ⟨k₀, hk₀⟩ := hex
      refine ⟨p k₀, fun k hk => mem_tropConeHull_of_mem hd p ?_⟩
      exact Finset.mem_erase.mpr ⟨fun hcon => hk₀ (hcon ▸ hk), Finset.mem_univ _⟩)
  -- residuation: the greatest weights with `lam j + p j ≤ z`
  refine ⟨fun j => univ.inf' hdne (fun i => z i - p j i), fun i k => ?_⟩
  have hle : ∀ (j : Fin (d + 1)) (i : Fin d),
      (univ.inf' hdne (fun i => z i - p j i)) + p j i ≤ z i := by
    intro j i
    have : univ.inf' hdne (fun i => z i - p j i) ≤ z i - p j i :=
      Finset.inf'_le (fun i => z i - p j i) (Finset.mem_univ i)
    linarith
  -- `z` is generated by the indices different from `k`, with the residuated weights
  have hkey : ∀ k : Fin (d + 1), ∀ i,
      z i = ((univ : Finset (Fin (d + 1))).erase k).sup' (herase k)
        (fun j => (univ.inf' hdne (fun i => z i - p j i)) + p j i) := by
    intro k i
    obtain ⟨mu, hFmu, hmu⟩ := hz k
    refine le_antisymm ?_ (Finset.sup'_le _ _ (fun j _ => hle j i))
    have hmule : ∀ j ∈ (univ : Finset (Fin (d + 1))).erase k,
        mu j ≤ univ.inf' hdne (fun i => z i - p j i) := by
      intro j hj
      refine Finset.le_inf' _ _ (fun i' _ => ?_)
      have : mu j + p j i' ≤ z i' := by
        rw [hmu i']
        exact Finset.le_sup' (fun j => mu j + p j i') hj
      linarith
    rw [hmu i]
    refine Finset.sup'_le _ _ (fun j hj => ?_)
    have h1 : mu j + p j i ≤ (univ.inf' hdne (fun i => z i - p j i)) + p j i := by
      have := hmule j hj; linarith
    exact le_trans h1 (Finset.le_sup'
      (fun j => (univ.inf' hdne (fun i => z i - p j i)) + p j i) hj)
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' (herase k)
    (fun j => (univ.inf' hdne (fun i => z i - p j i)) + p j i)
  refine ⟨j, (Finset.mem_erase.mp hj).1, ?_⟩
  rw [← hjeq, ← hkey k i]
  exact hle k i

end TropicalConeHull

namespace TropicalResiduation

variable {m n : ℕ}

-- [dropped: platform already declares mulVec]
-- [dropped: platform already declares resid]
/-- **Residuation (Galois connection).**  `A ⊗ x ≤ b` holds if and only if
`x ≤ A ♯ b` coordinatewise.  Thus `A ♯ b` is the greatest subsolution. -/
theorem mulVec_le_iff_le_resid (A : Fin (m + 1) → Fin (n + 1) → ℝ)
    (b : Fin (m + 1) → ℝ) (x : Fin (n + 1) → ℝ) :
    (∀ i, mulVec A x i ≤ b i) ↔ (∀ j, x j ≤ resid A b j) := by
  constructor
  · intro h j
    refine Finset.le_inf' _ _ (fun i _ => ?_)
    have h1 : A i j + x j ≤ mulVec A x i :=
      Finset.le_sup' (fun j => A i j + x j) (Finset.mem_univ j)
    have := h i
    linarith
  · intro h i
    refine Finset.sup'_le _ _ (fun j _ => ?_)
    have h1 : resid A b j ≤ b i - A i j :=
      Finset.inf'_le (fun i => b i - A i j) (Finset.mem_univ i)
    have := h j
    linarith

/-- `A ♯ b` is itself a subsolution. -/
theorem resid_mem (A : Fin (m + 1) → Fin (n + 1) → ℝ) (b : Fin (m + 1) → ℝ) :
    ∀ i, mulVec A (resid A b) i ≤ b i :=
  (mulVec_le_iff_le_resid A b (resid A b)).mpr (fun _ => le_rfl)

/-- The max-plus product is monotone in the vector argument. -/
theorem mulVec_mono (A : Fin (m + 1) → Fin (n + 1) → ℝ) {x y : Fin (n + 1) → ℝ}
    (hxy : ∀ j, x j ≤ y j) (i : Fin (m + 1)) : mulVec A x i ≤ mulVec A y i := by
  refine Finset.sup'_le _ _ (fun j _ => ?_)
  refine le_trans (by linarith [hxy j] : A i j + x j ≤ A i j + y j) ?_
  exact Finset.le_sup' (fun j => A i j + y j) (Finset.mem_univ j)

/-- **Cuninghame-Green principal solution.**  The max-plus linear system
`A ⊗ x = b` is solvable if and only if the canonical candidate `A ♯ b` solves
it.  This turns solvability into a single `O(mn)` evaluation. -/
theorem tropical_solvable_iff (A : Fin (m + 1) → Fin (n + 1) → ℝ)
    (b : Fin (m + 1) → ℝ) :
    (∃ x, ∀ i, mulVec A x i = b i) ↔ ∀ i, mulVec A (resid A b) i = b i := by
  constructor
  · rintro ⟨x, hx⟩ i
    refine le_antisymm (resid_mem A b i) ?_
    have hle : ∀ j, x j ≤ resid A b j :=
      (mulVec_le_iff_le_resid A b x).mp (fun i => le_of_eq (hx i))
    have := mulVec_mono A hle i
    rw [hx i] at this
    exact this
  · intro h
    exact ⟨resid A b, h⟩

/-- A quantitative complement: the residual `A ⊗ (A ♯ b)` is the best max-plus
approximation of `b` from below, so the "defect" is monotone in `b`. -/
theorem resid_defect_monotone (A : Fin (m + 1) → Fin (n + 1) → ℝ)
    (b c : Fin (m + 1) → ℝ) (hbc : ∀ i, b i ≤ c i) (i : Fin (m + 1)) :
    mulVec A (resid A b) i ≤ mulVec A (resid A c) i := by
  refine mulVec_mono A (fun j => ?_) i
  refine Finset.le_inf' _ _ (fun k _ => ?_)
  have : resid A b j ≤ b k - A k j :=
    Finset.inf'_le (fun i => b i - A i j) (Finset.mem_univ k)
  have := hbc k
  linarith

end TropicalResiduation
section
open Finset
open TropicalConeHull
variable {d : ℕ} {ι : Type*}

theorem solution (hd : 0 < d)
    (helly : ∀ C : Fin (d + 1) → Set (Fin d → ℝ), (∀ k, IsTropCone (C k)) →
      (∀ I : Finset (Fin (d + 1)), I.card ≤ d → ∃ x, ∀ k ∈ I, x ∈ C k) →
      ∃ x, ∀ k, x ∈ C k)
    (p : Fin (d + 1) → Fin d → ℝ) :
    ∃ lam : Fin (d + 1) → ℝ, ∀ (i : Fin d) (k : Fin (d + 1)),
      ∃ j, j ≠ k ∧ lam k + p k i ≤ lam j + p j i :=
  TropicalConeHull.dependence_of_helly hd helly p

end
