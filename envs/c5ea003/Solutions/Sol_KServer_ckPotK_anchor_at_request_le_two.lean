-- Prove2me | solution 1 for KServer.ckPotK_anchor_at_request_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-07T17:24:52.756719+00:00
-- url     : https://prove2.me/submissions/ee5764ea-52a3-44b1-b899-da46729f7b2a

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_resolves

/-!
The anchor statement for the Coester--Koutsoupias potential, for one and two servers.
It is proved here from the two structural properties of
the work function after a request — that it is `1`-Lipschitz for the matching distance and
that it resolves the request (some server may be assumed to sit on it).
-/

open KServer

namespace AnchorSmallK

variable {k : ℕ} {M : Type} [MetricSpace M]

/-- The work function of the instance, evaluated in the antipodal extension. -/
noncomputable def extW (k : ℕ) (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (C₀ : Config k M) (σ : List M)
    (X : Config k (M ⊕ M)) : ℝ :=
  @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
    (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) X

/-- The unordered work function does not depend on the labelling of its argument. -/
theorem workFnU_perm (C₀ : Config k M) (σ : List M) (X : Config k M)
    (π : Equiv.Perm (Fin k)) : workFnU C₀ σ (X ∘ π) = workFnU C₀ σ X := by
  have h : ∀ (Y : Config k M) (ρ : Equiv.Perm (Fin k)),
      workFnU C₀ σ (Y ∘ ρ) ≤ workFnU C₀ σ Y := by
    intro Y ρ
    refine le_ciInf fun τ => ?_
    refine le_trans (ciInf_le (Finite.bddBelow_range _) (ρ⁻¹ * τ)) (le_of_eq ?_)
    congr 1
    funext j
    simp [Equiv.Perm.coe_mul]
  refine le_antisymm (h X π) ?_
  have h2 := h (X ∘ π) π⁻¹
  have hX : (X ∘ (π : Fin k → Fin k)) ∘ (π⁻¹ : Equiv.Perm (Fin k)) = X := by
    funext j; simp
  rwa [hX] at h2

/-- Moving one server changes the configuration by exactly its own distance. -/
theorem moveCost_update (X : Config k M) (i : Fin k) (p : M) :
    moveCost (Function.update X i p) X = dist p (X i) := by
  classical
  rw [moveCost, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Function.update_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

section Extension

variable {Δ : ℝ} {hΔ0 : 0 < Δ} {hΔ : ∀ x y : M, dist x y ≤ Δ}

theorem extW_lipschitz (hk : 1 ≤ k) (C₀ : Config k M) (σ : List M)
    (X Y : Config k (M ⊕ M)) :
    extW k M Δ hΔ0 hΔ C₀ σ X
      ≤ extW k M Δ hΔ0 hΔ C₀ σ Y
        + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) Y X :=
  @workFnU_lipschitz k hk (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
    (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) X Y

theorem extW_perm (C₀ : Config k M) (σ : List M) (X : Config k (M ⊕ M))
    (π : Equiv.Perm (Fin k)) :
    extW k M Δ hΔ0 hΔ C₀ σ (X ∘ π) = extW k M Δ hΔ0 hΔ C₀ σ X :=
  @workFnU_perm k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
    (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) X π

/-- Parking a server on the request never costs more than its distance to the request. -/
theorem extW_snoc_le_update (hk : 1 ≤ k) (C₀ : Config k M) (l : List M) (r : M)
    (X : Config k (M ⊕ M)) (i : Fin k) :
    extW k M Δ hΔ0 hΔ C₀ (l ++ [r]) X
      ≤ extW k M Δ hΔ0 hΔ C₀ (l ++ [r]) (Function.update X i (Sum.inl r))
        + @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist (X i) (Sum.inl r) := by
  have h := extW_lipschitz (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) hk C₀ (l ++ [r]) X
    (Function.update X i (Sum.inl r))
  rwa [@moveCost_update k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) X i (Sum.inl r),
    @dist_comm (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toPseudoMetricSpace] at h

/-- After a request, some server may be assumed to sit on it, at no extra cost. -/
theorem exists_extW_snoc_tight (hk : 1 ≤ k) (C₀ : Config k M) (l : List M) (r : M)
    (X : Config k (M ⊕ M)) :
    ∃ i : Fin k, extW k M Δ hΔ0 hΔ C₀ (l ++ [r]) X
      = extW k M Δ hΔ0 hΔ C₀ (l ++ [r]) (Function.update X i (Sum.inl r))
        + @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist (Sum.inl r) (X i) := by
  have h := @workFnU_resolves k hk (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
    (fun i => Sum.inl (C₀ i)) (l.map Sum.inl) (Sum.inl r) X
  have hlist : (l.map Sum.inl) ++ [(Sum.inl r : M ⊕ M)] = (l ++ [r]).map Sum.inl := by
    simp
  rw [hlist] at h
  exact h

end Extension


section Distances

variable {Δ : ℝ} {hΔ0 : 0 < Δ} {hΔ : ∀ x y : M, dist x y ≤ Δ}

@[simp] theorem ext_dist_inl_inl (a b : M) :
    @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist (Sum.inl a) (Sum.inl b)
      = dist a b := rfl

@[simp] theorem ext_dist_inr_inr (a b : M) :
    @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist (Sum.inr a) (Sum.inr b)
      = dist a b := rfl

@[simp] theorem ext_dist_inl_inr (a b : M) :
    @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist (Sum.inl a) (Sum.inr b)
      = 2 * Δ - dist a b := rfl

@[simp] theorem ext_dist_inr_inl (a b : M) :
    @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist (Sum.inr a) (Sum.inl b)
      = 2 * Δ - dist a b := rfl

end Distances

/-- The four-case arithmetic at the heart of the two-server argument. -/
theorem two_server_arith {hp hq bp bq br s t D : ℝ}
    (ha : br ≤ bq + t) (hb : br ≤ bp + s) (hc : br ≤ hp + 2 * D - s)
    (hd : br ≤ hq + 2 * D - t) :
    min (hp + bp + br + 2 * D) (hq + bq + br + 2 * D)
      ≤ min (hq + s) (hp + t) + min (hq + (2 * D - s)) (bp + t) + (bq + (2 * D - t)) := by
  rcases le_total (hq + s) (hp + t) with h1 | h1 <;>
    rcases le_total (hq + (2 * D - s)) (bp + t) with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]
    exact le_trans (min_le_right _ _) (by linarith)
  · rw [min_eq_left h1, min_eq_right h2]
    exact le_trans (min_le_right _ _) (by linarith)
  · rw [min_eq_right h1, min_eq_left h2]
    exact le_trans (min_le_right _ _) (by linarith)
  · rw [min_eq_right h1, min_eq_right h2]
    exact le_trans (min_le_left _ _) (by linarith)

section TwoServers

variable {Δ : ℝ} {hΔ0 : 0 < Δ} {hΔ : ∀ x y : M, dist x y ≤ Δ}

/-- The value of the work function at a two-server configuration, through the function
obtained by parking one server on the request. -/
theorem extW_two_eq (C₀ : Config 2 M) (l : List M) (r : M) (a b : M ⊕ M) :
    extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![a, b]
      = min (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, b]
              + @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist a (Sum.inl r))
            (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, a]
              + @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist b (Sum.inl r)) := by
  classical
  have hup0 : Function.update (![a, b] : Config 2 (M ⊕ M)) 0 (Sum.inl r) = ![Sum.inl r, b] := by
    funext j; fin_cases j <;> simp
  have hup1 : Function.update (![a, b] : Config 2 (M ⊕ M)) 1 (Sum.inl r) = ![a, Sum.inl r] := by
    funext j; fin_cases j <;> simp
  have hswap : (![a, Sum.inl r] : Config 2 (M ⊕ M))
      = (![Sum.inl r, a] : Config 2 (M ⊕ M)) ∘ (Equiv.swap 0 1) := by
    funext j; fin_cases j <;> simp
  have hsym : extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![a, Sum.inl r]
      = extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, a] := by
    rw [hswap]; exact extW_perm (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) _ _ _ _
  refine le_antisymm (le_min ?_ ?_) ?_
  · have h := extW_snoc_le_update (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) one_le_two C₀ l r ![a, b] 0
    rwa [hup0, show (![a, b] : Config 2 (M ⊕ M)) 0 = a from rfl] at h
  · have h := extW_snoc_le_update (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) one_le_two C₀ l r ![a, b] 1
    rwa [hup1, hsym, show (![a, b] : Config 2 (M ⊕ M)) 1 = b from rfl] at h
  · obtain ⟨i, hi⟩ :=
      exists_extW_snoc_tight (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) one_le_two C₀ l r ![a, b]
    have hlt := i.isLt
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h
    · have hi0 : i = 0 := Fin.ext (by simpa using h)
      subst hi0
      rw [hup0, show (![a, b] : Config 2 (M ⊕ M)) 0 = a from rfl,
        @dist_comm (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toPseudoMetricSpace] at hi
      exact le_trans (min_le_left _ _) (le_of_eq hi.symm)
    · have hi1 : i = 1 := Fin.ext (by simpa using h)
      subst hi1
      rw [hup1, hsym, show (![a, b] : Config 2 (M ⊕ M)) 1 = b from rfl,
        @dist_comm (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toPseudoMetricSpace] at hi
      exact le_trans (min_le_right _ _) (le_of_eq hi.symm)

/-- The function obtained by parking one server on the request is `1`-Lipschitz. -/
theorem extW_two_lipschitz (C₀ : Config 2 M) (l : List M) (r : M) (a b : M ⊕ M) :
    extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, a]
      ≤ extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, b]
        + @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist b a := by
  have h := extW_lipschitz (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) one_le_two C₀ (l ++ [r])
    ![Sum.inl r, a] ![Sum.inl r, b]
  have hm : @moveCost 2 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      ![Sum.inl r, b] ![Sum.inl r, a]
      = @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist b a := by
    simp [moveCost, Fin.sum_univ_two]
  rwa [hm] at h

/-- The anchored potential of a two-server instance. -/
theorem ckPotAtK_two (C₀ : Config 2 M) (σ : List M) (x : Fin 2 → M) :
    ckPotAtK 2 M Δ hΔ0 hΔ C₀ σ x
      = extW 2 M Δ hΔ0 hΔ C₀ σ ![Sum.inl (x 0), Sum.inl (x 1)]
        + extW 2 M Δ hΔ0 hΔ C₀ σ ![Sum.inr (x 0), Sum.inl (x 1)]
        + extW 2 M Δ hΔ0 hΔ C₀ σ ![Sum.inr (x 1), Sum.inr (x 1)] := by
  have h0 : (fun j => Sum.inl (x j) : Config 2 (M ⊕ M)) = ![Sum.inl (x 0), Sum.inl (x 1)] := by
    funext j; fin_cases j <;> rfl
  have h1 : ckConfigK x 0 = (![Sum.inr (x 0), Sum.inl (x 1)] : Config 2 (M ⊕ M)) := by
    funext j; fin_cases j <;> simp [ckConfigK]
  have h2 : ckConfigK x 1 = (![Sum.inr (x 1), Sum.inr (x 1)] : Config 2 (M ⊕ M)) := by
    funext j; fin_cases j <;> simp [ckConfigK]
  show extW 2 M Δ hΔ0 hΔ C₀ σ (fun j => Sum.inl (x j))
      + ∑ i : Fin 2, extW 2 M Δ hΔ0 hΔ C₀ σ (ckConfigK x i) = _
  rw [Fin.sum_univ_two, h0, h1, h2]
  ring

/-- The potential at an anchor tuple whose last coordinate is the request. -/
theorem ckPotAtK_two_anchor (C₀ : Config 2 M) (l : List M) (r : M) (z : M) :
    ckPotAtK 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![z, r]
      = extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inl z]
        + extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr z]
        + extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr r] + 2 * Δ := by
  have hx0 : (![z, r] : Fin 2 → M) 0 = z := rfl
  have hx1 : (![z, r] : Fin 2 → M) 1 = r := rfl
  rw [ckPotAtK_two (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ), hx0, hx1]
  have e1 := extW_two_eq (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inl z) (Sum.inl r)
  have e2 := extW_two_eq (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inr z) (Sum.inl r)
  have e3 := extW_two_eq (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inr r) (Sum.inr r)
  have l1 := extW_two_lipschitz (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inl z) (Sum.inl r)
  have l2 := extW_two_lipschitz (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inr z) (Sum.inl r)
  simp only [ext_dist_inl_inl, ext_dist_inr_inl, ext_dist_inl_inr, ext_dist_inr_inr,
    dist_self, add_zero, sub_zero] at e1 e2 e3 l1 l2
  rw [e1, e2, e3, min_eq_right (by linarith [l1, dist_comm z r]),
    min_eq_right (by linarith [l2, dist_comm z r]), min_self]
  ring

/-- **The two-server case**: for every anchor tuple there is one with the request as last
coordinate whose potential is no larger. -/
theorem exists_anchor_le_two (C₀ : Config 2 M) (l : List M) (r : M) (y : Fin 2 → M) :
    ∃ z : M, ckPotAtK 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![z, r]
      ≤ ckPotAtK 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) y := by
  have e1 := extW_two_eq (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inl (y 0)) (Sum.inl (y 1))
  have e2 := extW_two_eq (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inr (y 0)) (Sum.inl (y 1))
  have e3 := extW_two_eq (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inr (y 1)) (Sum.inr (y 1))
  have la := extW_two_lipschitz (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r
    (Sum.inr r) (Sum.inr (y 1))
  have lb := extW_two_lipschitz (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r
    (Sum.inr r) (Sum.inr (y 0))
  have lc := extW_two_lipschitz (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r
    (Sum.inr r) (Sum.inl (y 0))
  have ld := extW_two_lipschitz (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r
    (Sum.inr r) (Sum.inl (y 1))
  simp only [ext_dist_inl_inl, ext_dist_inr_inl, ext_dist_inl_inr, ext_dist_inr_inr,
    add_zero] at e1 e2 e3 la lb lc ld
  have key := two_server_arith (D := Δ) (s := dist (y 0) r) (t := dist (y 1) r)
    (hp := extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inl (y 0)])
    (hq := extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inl (y 1)])
    (bp := extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr (y 0)])
    (bq := extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr (y 1)])
    (br := extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr r])
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hrhs : ckPotAtK 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) y
      = min (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inl (y 1)] + dist (y 0) r)
            (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inl (y 0)] + dist (y 1) r)
        + min (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inl (y 1)]
                + (2 * Δ - dist (y 0) r))
              (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr (y 0)] + dist (y 1) r)
        + (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr (y 1)]
            + (2 * Δ - dist (y 1) r)) := by
    rw [ckPotAtK_two (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ), e1, e2, e3, min_self]
  rw [hrhs]
  rcases le_total
      (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inl (y 0)]
        + extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr (y 0)]
        + extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr r] + 2 * Δ)
      (extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inl (y 1)]
        + extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr (y 1)]
        + extW 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r, Sum.inr r] + 2 * Δ) with h | h
  · refine ⟨y 0, ?_⟩
    rw [ckPotAtK_two_anchor (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ)]
    rw [min_eq_left h] at key
    linarith [key]
  · refine ⟨y 1, ?_⟩
    rw [ckPotAtK_two_anchor (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ)]
    rw [min_eq_right h] at key
    linarith [key]

end TwoServers

section OneServer

variable {Δ : ℝ} {hΔ0 : 0 < Δ} {hΔ : ∀ x y : M, dist x y ≤ Δ}

/-- With a single server the work function after a request is rigid. -/
theorem extW_one_eq (C₀ : Config 1 M) (l : List M) (r : M) (a : M ⊕ M) :
    extW 1 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![a]
      = extW 1 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r]
        + @dist (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toDist a (Sum.inl r) := by
  classical
  have hup : Function.update (![a] : Config 1 (M ⊕ M)) 0 (Sum.inl r) = ![Sum.inl r] := by
    funext j; fin_cases j; simp
  refine le_antisymm ?_ ?_
  · have h := extW_snoc_le_update (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) (le_refl 1) C₀ l r ![a] 0
    rwa [hup, show (![a] : Config 1 (M ⊕ M)) 0 = a from rfl] at h
  · obtain ⟨i, hi⟩ :=
      exists_extW_snoc_tight (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) (le_refl 1) C₀ l r ![a]
    have hi0 : i = 0 := Fin.ext (by omega)
    subst hi0
    rw [hup, show (![a] : Config 1 (M ⊕ M)) 0 = a from rfl,
      @dist_comm (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ).toPseudoMetricSpace] at hi
    exact le_of_eq hi.symm

/-- The anchored potential of a one-server instance. -/
theorem ckPotAtK_one (C₀ : Config 1 M) (σ : List M) (x : Fin 1 → M) :
    ckPotAtK 1 M Δ hΔ0 hΔ C₀ σ x
      = extW 1 M Δ hΔ0 hΔ C₀ σ ![Sum.inl (x 0)]
        + extW 1 M Δ hΔ0 hΔ C₀ σ ![Sum.inr (x 0)] := by
  have h0 : (fun j => Sum.inl (x j) : Config 1 (M ⊕ M)) = ![Sum.inl (x 0)] := by
    funext j; fin_cases j; rfl
  have h1 : ckConfigK x 0 = (![Sum.inr (x 0)] : Config 1 (M ⊕ M)) := by
    funext j; fin_cases j; simp [ckConfigK]
  show extW 1 M Δ hΔ0 hΔ C₀ σ (fun j => Sum.inl (x j))
      + ∑ i : Fin 1, extW 1 M Δ hΔ0 hΔ C₀ σ (ckConfigK x i) = _
  rw [Fin.sum_univ_one, h0, h1]

/-- **The one-server case**: the potential after the request does not depend on the
anchor at all. -/
theorem ckPotAtK_one_const (C₀ : Config 1 M) (l : List M) (r : M) (x : Fin 1 → M) :
    ckPotAtK 1 M Δ hΔ0 hΔ C₀ (l ++ [r]) x
      = 2 * extW 1 M Δ hΔ0 hΔ C₀ (l ++ [r]) ![Sum.inl r] + 2 * Δ := by
  rw [ckPotAtK_one (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ),
    extW_one_eq (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inl (x 0)),
    extW_one_eq (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r (Sum.inr (x 0))]
  simp only [ext_dist_inl_inl, ext_dist_inr_inl]
  ring

end OneServer

end AnchorSmallK

open AnchorSmallK in
theorem solution (k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M) :
    ∃ x : Fin k → M, x ⟨k - 1, by omega⟩ = r ∧
      ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) x = ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r]) := by
  haveI : Nonempty M := ⟨r⟩
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · -- one server: every anchor attains the minimum
    obtain ⟨y, hy⟩ := exists_ckPotK_eq 1 M Δ hΔ0 hΔ C₀ (l ++ [r])
    refine ⟨![r], rfl, ?_⟩
    rw [hy, ckPotAtK_one_const (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ),
      ckPotAtK_one_const (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ)]
  · -- two servers
    obtain ⟨y, hy⟩ := exists_ckPotK_eq 2 M Δ hΔ0 hΔ C₀ (l ++ [r])
    obtain ⟨z, hz⟩ := exists_anchor_le_two (Δ := Δ) (hΔ0 := hΔ0) (hΔ := hΔ) C₀ l r y
    refine ⟨![z, r], rfl, le_antisymm ?_ (ckPotK_le 2 M Δ hΔ0 hΔ C₀ (l ++ [r]) _)⟩
    rw [hy]
    exact hz
