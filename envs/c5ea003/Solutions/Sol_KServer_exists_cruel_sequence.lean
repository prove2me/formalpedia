-- Prove2me | solution 1 for KServer.exists_cruel_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T02:22:28.601528+00:00
-- url     : https://prove2.me/submissions/b2ce6488-c186-4d62-bd4a-2978dff22c0e

import Mathlib
import Definitions.Def_KServer_model

open KServer

/-! ### Generic auxiliaries -/

/-- The cost of an online algorithm splits at the last request. -/
private theorem cost_concat {k : ℕ} {M : Type} [MetricSpace M]
    (X : OnlineAlgorithm k M) (l : List M) (r : M) :
    X.cost (l ++ [r]) = X.cost l + moveCost (X.conf l) (X.conf (l ++ [r])) := by
  unfold OnlineAlgorithm.cost
  have hlen : (l ++ [r]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

/-- Consecutive pairs of `l ++ [r]`: those of `l`, plus the pair joining the old last
element to `r`. -/
private theorem zip_tail_concat {α : Type} (l : List α) (r : α) :
    (l ++ [r]).zip (l ++ [r]).tail
      = l.zip l.tail ++ (l.getLast?.map (fun x => (x, r))).toList := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t' => simpa using ih

/-- A lazy step moves exactly one server, so its cost is that server's travel. -/
private theorem moveCost_update {k : ℕ} {M : Type} [MetricSpace M]
    (f : Fin k → M) (i : Fin k) (r : M) :
    moveCost f (Function.update f i r) = dist (f i) r := by
  unfold moveCost
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Function.update_of_ne hj]) (by simp)]
  simp

/-- Peel the `i`-th value off an image over `univ`. -/
private theorem image_eq_insert {k : ℕ} {M : Type} [DecidableEq M]
    (f : Fin k → M) (i : Fin k) :
    Finset.image f Finset.univ = insert (f i) (Finset.image f (Finset.univ.erase i)) := by
  conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
  rw [Finset.image_insert]

private theorem image_update_eq_insert {k : ℕ} {M : Type} [DecidableEq M]
    (f : Fin k → M) (i : Fin k) (r : M) :
    Finset.image (Function.update f i r) Finset.univ
      = insert r (Finset.image f (Finset.univ.erase i)) := by
  rw [image_eq_insert (Function.update f i r) i, Function.update_self]
  congr 1
  refine Finset.image_congr ?_
  intro j hj
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hj
  exact Function.update_of_ne hj.2 _ _

/-- Serving a *fresh* point never shrinks the set of occupied points. -/
private theorem card_image_update_ge {k : ℕ} {M : Type} [DecidableEq M]
    (f : Fin k → M) (i : Fin k) (r : M) (hr : r ∉ Finset.image f Finset.univ) :
    (Finset.image f Finset.univ).card
      ≤ (Finset.image (Function.update f i r) Finset.univ).card := by
  have hsub : Finset.image f (Finset.univ.erase i) ⊆ Finset.image f Finset.univ :=
    Finset.image_subset_image (Finset.erase_subset _ _)
  have hrS : r ∉ Finset.image f (Finset.univ.erase i) := fun h => hr (hsub h)
  rw [image_update_eq_insert, Finset.card_insert_of_notMem hrS]
  calc (Finset.image f Finset.univ).card
      = (insert (f i) (Finset.image f (Finset.univ.erase i))).card := by
        rw [← image_eq_insert]
    _ ≤ (Finset.image f (Finset.univ.erase i)).card + 1 := Finset.card_insert_le _ _


/-- If two servers share a point, serving a fresh point with one of them strictly
increases the set of occupied points. -/
private theorem card_image_update_lt {k : ℕ} {M : Type} [DecidableEq M]
    (f : Fin k → M) (i j : Fin k) (r : M) (hr : r ∉ Finset.image f Finset.univ)
    (hij : j ≠ i) (hfj : f j = f i) :
    (Finset.image f Finset.univ).card
      < (Finset.image (Function.update f i r) Finset.univ).card := by
  have hsub : Finset.image f (Finset.univ.erase i) ⊆ Finset.image f Finset.univ :=
    Finset.image_subset_image (Finset.erase_subset _ _)
  have hrS : r ∉ Finset.image f (Finset.univ.erase i) := fun h => hr (hsub h)
  have hmem : f i ∈ Finset.image f (Finset.univ.erase i) :=
    Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩, hfj⟩
  rw [image_update_eq_insert, Finset.card_insert_of_notMem hrS,
    image_eq_insert f i, Finset.insert_eq_self.mpr hmem]
  omega


/-! ### The cruel adversary -/

theorem solution (k : ℕ) (M : Type) [MetricSpace M]
    (P : Finset M) (hP : P.card = k + 1) (B : OnlineAlgorithm k M)
    (hlazy : ∀ (l : List M) (r : M), ∃ i : Fin k,
      B.conf (l ++ [r]) = Function.update (B.conf l) i r) :
    ∃ E : ℝ, ∀ n : ℕ, ∃ σ : List M,
      σ.length = n ∧
      (∀ r ∈ σ, r ∈ P) ∧
      (∀ p ∈ σ.zip σ.tail, p.1 ≠ p.2) ∧
      ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum ≤ B.cost σ + E := by
  classical
  obtain ⟨p₀, hp₀⟩ : P.Nonempty := Finset.card_pos.mp (by omega)
  -- the diameter of the chosen `k+1` points
  set Δ : ℝ := (P ×ˢ P).sup' ⟨(p₀, p₀), Finset.mem_product.mpr ⟨hp₀, hp₀⟩⟩
      (fun q => dist q.1 q.2) with hΔdef
  have hΔ : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ Δ := by
    intro p hp q hq
    have hpq : (p, q) ∈ P ×ˢ P := Finset.mem_product.mpr ⟨hp, hq⟩
    rw [hΔdef]
    exact Finset.le_sup' (fun q : M × M => dist q.1 q.2) hpq
  have hΔ0 : (0:ℝ) ≤ Δ := by simpa using hΔ p₀ hp₀ p₀ hp₀
  -- the set of points occupied by the servers
  set occ : List M → Finset M := fun l => Finset.image (B.conf l) Finset.univ with hoccdef
  have hocc : ∀ l : List M, occ l = Finset.image (B.conf l) Finset.univ := fun l => by
    rw [hoccdef]
  have hocc_card : ∀ l : List M, (occ l).card ≤ k := by
    intro l
    rw [hocc]
    calc (Finset.image (B.conf l) Finset.univ).card
        ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
  have hUne : ∀ l : List M, (P \ occ l).Nonempty := by
    intro l
    rw [← Finset.card_pos]
    have h1 := hocc_card l
    have h2 := Finset.le_card_sdiff (occ l) P
    omega
  -- the current request (an irrelevant default on the empty list)
  set lastD : List M → M := fun l => l.getLast?.getD p₀ with hlastDdef
  have hlastD_concat : ∀ (l : List M) (r : M), lastD (l ++ [r]) = r := by
    intro l r; rw [hlastDdef]; simp
  have hgetLast : ∀ l : List M, l ≠ [] → l.getLast? = some (lastD l) := by
    intro l hl
    cases h : l.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hl
    | some y => rw [hlastDdef]; simp [h]
  -- the adversary: the uncovered point of `P` closest to the current request
  have hchoice : ∀ l : List M, ∃ y ∈ P \ occ l,
      ∀ z ∈ P \ occ l, dist (lastD l) y ≤ dist (lastD l) z :=
    fun l => Finset.exists_min_image _ (fun p => dist (lastD l) p) (hUne l)
  choose nxt hnxt_mem hnxt_min using hchoice
  have hnxt_P : ∀ l, nxt l ∈ P := fun l => (Finset.mem_sdiff.mp (hnxt_mem l)).1
  have hnxt_unocc : ∀ l, nxt l ∉ occ l := fun l => (Finset.mem_sdiff.mp (hnxt_mem l)).2
  -- a served request is occupied
  have hserved : ∀ (l : List M) (r : M), r ∈ occ (l ++ [r]) := by
    intro l r
    obtain ⟨i, hi⟩ := B.serves l r
    rw [hocc]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  -- the potential: servers still outside `P`, plus the number of coincidences
  set Psi : List M → ℕ := fun l =>
    (Finset.univ.filter (fun i => B.conf l i ∉ P)).card + (k - (occ l).card) with hPsidef
  -- THE STEP INEQUALITY
  have hstep : ∀ (l : List M) (i : Fin k),
      B.conf (l ++ [nxt l]) = Function.update (B.conf l) i (nxt l) →
      dist (nxt l) (nxt (l ++ [nxt l])) + Δ * (Psi (l ++ [nxt l]) : ℝ)
        ≤ dist (B.conf l i) (nxt l) + Δ * (Psi l : ℝ) := by
    intro l i hconf'
    have hrP : nxt l ∈ P := hnxt_P l
    have hrocc : nxt l ∉ occ l := hnxt_unocc l
    have hroccI : nxt l ∉ Finset.image (B.conf l) Finset.univ := by rwa [hocc] at hrocc
    have hoccl' : occ (l ++ [nxt l])
        = Finset.image (Function.update (B.conf l) i (nxt l)) Finset.univ := by
      rw [hocc, hconf']
    -- component 1 of the potential never grows
    have hfilt_sub : (Finset.univ.filter (fun j => B.conf (l ++ [nxt l]) j ∉ P))
        ⊆ (Finset.univ.filter (fun j => B.conf l j ∉ P)) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_cases hji : j = i
      · subst hji; rw [hconf', Function.update_self] at hj; exact absurd hrP hj
      · rwa [hconf', Function.update_of_ne hji] at hj
    have hfilt_le := Finset.card_le_card hfilt_sub
    -- component 2 of the potential never grows
    have hocc_ge : (occ l).card ≤ (occ (l ++ [nxt l])).card := by
      rw [hoccl', hocc]
      exact card_image_update_ge (B.conf l) i (nxt l) hroccI
    by_cases hcase : B.conf l i ∈ P ∧ B.conf l i ∉ occ (l ++ [nxt l])
    · -- the vacated point is a legal next request, and is exactly what the step paid for
      have hxmem : B.conf l i ∈ P \ occ (l ++ [nxt l]) := Finset.mem_sdiff.mpr hcase
      have h1 := hnxt_min (l ++ [nxt l]) (B.conf l i) hxmem
      rw [hlastD_concat l (nxt l)] at h1
      have h2 : dist (nxt l) (B.conf l i) = dist (B.conf l i) (nxt l) := dist_comm _ _
      have hPsi_le : Psi (l ++ [nxt l]) ≤ Psi l := by
        have h3 := hocc_card (l ++ [nxt l])
        simp only [hPsidef]
        omega
      have h4 : Δ * (Psi (l ++ [nxt l]) : ℝ) ≤ Δ * (Psi l : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hPsi_le) hΔ0
      linarith
    · -- one of the two exceptional steps: the potential drops, and `Δ` pays for the request
      have hdrop : Psi (l ++ [nxt l]) + 1 ≤ Psi l := by
        rw [not_and_or, not_not] at hcase
        have h3 := hocc_card (l ++ [nxt l])
        rcases hcase with hxP | hxocc
        · -- the moving server had never moved before: it enters `P` for good
          have hstrict : (Finset.univ.filter (fun j => B.conf (l ++ [nxt l]) j ∉ P)).card
              < (Finset.univ.filter (fun j => B.conf l j ∉ P)).card := by
            refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hfilt_sub).mpr ?_)
            refine ⟨i, by simp [hxP], ?_⟩
            simp [hconf', hrP]
          simp only [hPsidef]
          omega
        · -- two servers shared the vacated point: a coincidence is destroyed
          obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (by rwa [hocc] at hxocc)
          have hji : j ≠ i := by
            intro h
            subst h
            rw [hconf', Function.update_self] at hj
            exact hroccI (hj ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
          have hfj : B.conf l j = B.conf l i := by
            rwa [hconf', Function.update_of_ne hji] at hj
          have hlt : (occ l).card < (occ (l ++ [nxt l])).card := by
            rw [hoccl', hocc]
            exact card_image_update_lt (B.conf l) i j (nxt l) hroccI hji hfj
          simp only [hPsidef]
          omega
      have h1 : dist (nxt l) (nxt (l ++ [nxt l])) ≤ Δ :=
        hΔ _ hrP _ (hnxt_P (l ++ [nxt l]))
      have h2 : Δ * (Psi (l ++ [nxt l]) : ℝ) + Δ ≤ Δ * (Psi l : ℝ) := by
        have : Δ * ((Psi (l ++ [nxt l]) : ℝ) + 1) ≤ Δ * (Psi l : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hdrop) hΔ0
        linarith [this]
      have h3 : (0:ℝ) ≤ dist (B.conf l i) (nxt l) := dist_nonneg
      linarith
  -- THE INDUCTION
  have key : ∀ n : ℕ, ∃ σ : List M, σ.length = n + 1 ∧ (∀ r ∈ σ, r ∈ P) ∧
      (∀ p ∈ σ.zip σ.tail, p.1 ≠ p.2) ∧ lastD σ ∈ occ σ ∧
      ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum
        + dist (lastD σ) (nxt σ) + Δ * (Psi σ : ℝ)
        ≤ B.cost σ + Δ * (Psi ([] : List M) : ℝ) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨i, hi⟩ := hlazy ([] : List M) (nxt [])
      have hnil : ([] : List M) ++ [nxt []] = [nxt []] := by simp
      have hs := hstep ([] : List M) i hi
      rw [hnil] at hs
      have hlast1 : lastD [nxt []] = nxt [] := by
        have h := hlastD_concat ([] : List M) (nxt []); rwa [hnil] at h
      have hocc1 : nxt [] ∈ occ [nxt []] := by
        have h := hserved ([] : List M) (nxt []); rwa [hnil] at h
      have hcost1 : B.cost [nxt []] = dist (B.conf [] i) (nxt []) := by
        have hc := cost_concat B ([] : List M) (nxt [])
        rw [hi, moveCost_update, hnil] at hc
        simpa [OnlineAlgorithm.cost] using hc
      refine ⟨[nxt []], by simp, ?_, by simp, by rw [hlast1]; exact hocc1, ?_⟩
      · intro r hr; simp at hr; subst hr; exact hnxt_P []
      · have hz : ((([nxt []] : List M).zip ([nxt []] : List M).tail).map
            (fun p => dist p.1 p.2)).sum = 0 := by simp
        rw [hlast1, hcost1, hz]
        linarith
    | succ n ih =>
      obtain ⟨σ, hlen, hmem, hpair, hlastocc, hineq⟩ := ih
      obtain ⟨i, hi⟩ := hlazy σ (nxt σ)
      have hσne : σ ≠ [] := by intro h; rw [h] at hlen; simp at hlen
      have hzip := zip_tail_concat σ (nxt σ)
      have hlastσ : σ.getLast? = some (lastD σ) := hgetLast σ hσne
      refine ⟨σ ++ [nxt σ], by simp [hlen], ?_, ?_, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with h | h
        · exact hmem r h
        · simp at h; subst h; exact hnxt_P σ
      · intro p hp
        rw [hzip, hlastσ] at hp
        simp only [Option.map_some, Option.toList_some, List.mem_append,
          List.mem_singleton] at hp
        rcases hp with h | h
        · exact hpair p h
        · subst h
          intro hcon
          have h2 : lastD σ = nxt σ := hcon
          rw [h2] at hlastocc
          exact hnxt_unocc σ hlastocc
      · rw [hlastD_concat σ (nxt σ)]; exact hserved σ (nxt σ)
      · have hs := hstep σ i hi
        have hcost : B.cost (σ ++ [nxt σ]) = B.cost σ + dist (B.conf σ i) (nxt σ) := by
          rw [cost_concat B σ (nxt σ), hi, moveCost_update]
        have hconsec : (((σ ++ [nxt σ]).zip (σ ++ [nxt σ]).tail).map
              (fun p => dist p.1 p.2)).sum
            = ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum
              + dist (lastD σ) (nxt σ) := by
          rw [hzip, hlastσ]; simp
        rw [hconsec, hcost, hlastD_concat σ (nxt σ)]
        linarith
  -- CONCLUSION
  refine ⟨Δ * (Psi ([] : List M) : ℝ), ?_⟩
  intro n
  cases n with
  | zero =>
    refine ⟨[], by simp, by simp, by simp, ?_⟩
    have : B.cost ([] : List M) = 0 := by simp [OnlineAlgorithm.cost]
    have hnn : (0:ℝ) ≤ Δ * (Psi ([] : List M) : ℝ) := by positivity
    simp only [List.zip_nil_left, List.map_nil, List.sum_nil]
    linarith
  | succ m =>
    obtain ⟨σ, hlen, hmem, hpair, -, hineq⟩ := key m
    refine ⟨σ, hlen, hmem, hpair, ?_⟩
    have h1 : (0:ℝ) ≤ dist (lastD σ) (nxt σ) := dist_nonneg
    have h2 : (0:ℝ) ≤ Δ * (Psi σ : ℝ) := by positivity
    linarith
