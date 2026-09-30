-- Prove2me | solution 1 for Hirsch.finite_coordinate_extreme_route_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-16T23:46:26.669482+00:00
-- url     : https://prove2.me/submissions/119b7820-4131-4c99-ac87-46ec35dc7249

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.CoordinateRoute

variable {V : Type*} [DecidableEq V]

/-- A finite walk whose entire visited sequence lies in the specified set. -/
structure Route (R : V → V → Prop) (S : Finset V) (u v : V) where
  length : ℕ
  point : ℕ → V
  first : point 0 = u
  last : point length = v
  mem : ∀ i, i ≤ length → point i ∈ S
  step : ∀ i, i < length → R (point i) (point (i+1))

namespace Route

variable {R : V → V → Prop} {S T : Finset V} {u v w : V}

def nil (hu : u ∈ S) : Route R S u u where
  length := 0
  point := fun _ => u
  first := rfl
  last := rfl
  mem := fun _ _ => hu
  step := by intro i hi; omega

def prepend (hu : u ∈ S) (h : R u v) (p : Route R S v w) : Route R S u w where
  length := p.length+1
  point := fun i => if i = 0 then u else p.point (i-1)
  first := by simp
  last := by simpa using p.last
  mem := by
    intro i hi
    by_cases hz : i = 0
    · simpa [hz] using hu
    · simpa [hz] using p.mem (i-1) (by omega)
  step := by
    intro i hi
    cases i with
    | zero => simpa [p.first] using h
    | succ i => simpa using p.step i (by omega)

def mono (p : Route R S u v) (hST : S ⊆ T) : Route R T u v where
  length := p.length
  point := p.point
  first := p.first
  last := p.last
  mem := fun i hi => hST (p.mem i hi)
  step := p.step

def reverse (p : Route R S u v) (hsym : ∀ a b, R a b → R b a) : Route R S v u where
  length := p.length
  point := fun i => p.point (p.length-i)
  first := by simpa using p.last
  last := by simpa using p.first
  mem := fun i _ => p.mem (p.length-i) (Nat.sub_le _ _)
  step := by
    intro i hi
    have h := hsym _ _ (p.step (p.length-(i+1)) (by omega))
    have he : p.length-(i+1)+1 = p.length-i := by omega
    simpa only [he] using h

def append (p : Route R S u v) (q : Route R S v w) : Route R S u w where
  length := p.length+q.length
  point := fun i => if i ≤ p.length then p.point i else q.point (i-p.length)
  first := by simpa using p.first
  last := by
    by_cases hz : q.length = 0
    · have hvw : v = w := q.first.symm.trans (by simpa [hz] using q.last)
      simpa [hz] using p.last.trans hvw
    · have hn : ¬ p.length+q.length ≤ p.length := by omega
      simpa [hn] using q.last
  mem := by
    intro i hi
    by_cases h : i ≤ p.length
    · simpa only [if_pos h] using p.mem i h
    · simpa only [if_neg h] using q.mem (i-p.length) (by omega)
  step := by
    intro i hi
    by_cases h : i < p.length
    · have h0 : i ≤ p.length := by omega
      have h1 : i+1 ≤ p.length := by omega
      simpa only [if_pos h0, if_pos h1] using p.step i h
    · by_cases he : i = p.length
      · subst i
        have hn : ¬ p.length+1 ≤ p.length := by omega
        have hq := q.step 0 (by omega)
        simpa [hn, p.last, q.first] using hq
      · have h0 : ¬ i ≤ p.length := by omega
        have h1 : ¬ i+1 ≤ p.length := by omega
        have hadd : i+1-p.length = (i-p.length)+1 := by omega
        simpa only [if_neg h0, if_neg h1, hadd] using q.step (i-p.length) (by omega)

end Route

/-- Integer progress builds a route to an attained minimum. No path is input. -/
theorem descend
    (R : V → V → Prop) (S : Finset V) (f : V → ℕ) (m : ℕ)
    (hmin : ∀ x ∈ S, m ≤ f x)
    (hstep : ∀ x ∈ S, m < f x → ∃ y ∈ S, R x y ∧ f y < f x)
    (x : V) (hx : x ∈ S) :
    ∃ z : V, ∃ p : Route R S x z, f z = m ∧ p.length+m ≤ f x := by
  have aux : ∀ k : ℕ, ∀ a : V, a ∈ S → f a = k →
      ∃ z : V, ∃ p : Route R S a z, f z = m ∧ p.length+m ≤ f a := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a ha hak
      by_cases he : f a = m
      · exact ⟨a, Route.nil ha, he, by simpa [Route.nil, he]⟩
      · have hma : m < f a := by have hh := hmin a ha; omega
        obtain ⟨b, hb, hab, hba⟩ := hstep a ha hma
        obtain ⟨z, p, hpz, hlen⟩ := ih (f b) (by omega) b hb rfl
        refine ⟨z, Route.prepend ha hab p, hpz, ?_⟩
        change p.length+1+m ≤ f a
        omega
  exact aux (f x) x hx rfl

/-- Reverse ranks turn the same construction into an ascent to a maximum. -/
theorem ascend
    (R : V → V → Prop) (S : Finset V) (f : V → ℕ) (M K : ℕ)
    (hmax : ∀ x ∈ S, f x ≤ M) (hMK : M ≤ K)
    (hstep : ∀ x ∈ S, f x < M → ∃ y ∈ S, R x y ∧ f x < f y)
    (x : V) (hx : x ∈ S) :
    ∃ z : V, ∃ p : Route R S x z, f z = M ∧ p.length+f x ≤ M := by
  have hl : ∀ a ∈ S, K-M ≤ K-f a := by
    intro a ha
    have hh := hmax a ha
    omega
  have hs : ∀ a ∈ S, K-M < K-f a →
      ∃ b ∈ S, R a b ∧ K-f b < K-f a := by
    intro a ha hn
    have haM := hmax a ha
    have haK : f a ≤ K := haM.trans hMK
    obtain ⟨b, hb, hab, hlt⟩ := hstep a ha (by omega)
    have hbM := hmax b hb
    refine ⟨b, hb, hab, ?_⟩
    omega
  obtain ⟨z, p, he, hlen⟩ := descend R S (fun a => K-f a) (K-M) hl hs x hx
  have hzM := hmax z (by rw [← p.last]; exact p.mem _ le_rfl)
  have hxM := hmax x hx
  refine ⟨z, p, ?_, ?_⟩ <;> omega

/-- The two-front face induction. Coordinates here are integer ranks. -/
theorem rank_routes
    (d : ℕ) (R : V → V → Prop) (hsym : ∀ a b, R a b → R b a)
    (c : V → Fin d → ℕ) (hinj : Function.Injective c) (K : Fin d → ℕ)
    (Face : Finset V → Prop)
    (hminface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c a j ≤ c x j) → Face (F.filter (fun x => c x j = c a j)))
    (hmaxface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c x j ≤ c a j) → Face (F.filter (fun x => c x j = c a j)))
    (hdown : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c y j < c x j → ∃ z ∈ F, R x z ∧ c z j < c x j)
    (hup : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c x j < c y j → ∃ z ∈ F, R x z ∧ c x j < c z j) :
    ∀ J : Finset (Fin d), ∀ F, Face F →
      (∀ x ∈ F, ∀ j, c x j ≤ K j) →
      (∀ j, j ∉ J → ∀ x ∈ F, ∀ y ∈ F, c x j = c y j) →
      ∀ u, u ∈ F → ∀ v, v ∈ F →
      ∃ p : Route R F u v, p.length ≤ ∑ j ∈ J, K j := by
  classical
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro F hF hK hfixed u hu v hv
    have huv : u = v := hinj (funext (fun j => hfixed j (by simp) u hu v hv))
    subst v
    exact ⟨Route.nil hu, by simp [Route.nil]⟩
  | @insert j J hj ih =>
    intro F hF hK hfixed u hu v hv
    have finish : ∀ (t : ℕ) (a b : V) (p : Route R F u a) (q : Route R F v b),
        c a j = t → c b j = t →
        Face (F.filter (fun x => c x j = t)) →
        p.length+q.length ≤ K j →
        ∃ r : Route R F u v, r.length ≤ ∑ i ∈ insert j J, K i := by
      intro t a b p q ha hb hface hcost
      let F' := F.filter (fun x => c x j = t)
      have hsub : F' ⊆ F := Finset.filter_subset _ _
      have hfa : a ∈ F' := Finset.mem_filter.mpr
        ⟨by rw [← p.last]; exact p.mem _ le_rfl, ha⟩
      have hfb : b ∈ F' := Finset.mem_filter.mpr
        ⟨by rw [← q.last]; exact q.mem _ le_rfl, hb⟩
      have hfix' : ∀ i, i ∉ J → ∀ x ∈ F', ∀ y ∈ F', c x i = c y i := by
        intro i hi x hx y hy
        by_cases he : i = j
        · subst i
          exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
        · exact hfixed i (by simp [he, hi]) x (hsub hx) y (hsub hy)
      obtain ⟨middle, hmiddle⟩ := ih F' hface
        (fun x hx i => hK x (hsub hx) i) hfix' a hfa b hfb
      let r := p.append ((middle.mono hsub).append (q.reverse hsym))
      refine ⟨r, ?_⟩
      have hsum : (∑ i ∈ insert j J, K i) = K j + ∑ i ∈ J, K i :=
        Finset.sum_insert hj
      rw [hsum]
      change p.length+(middle.length+q.length) ≤ K j + ∑ i ∈ J, K i
      omega
    by_cases hside : c u j+c v j ≤ K j
    · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image F (fun x => c x j) ⟨u, hu⟩
      have hs : ∀ x ∈ F, c a j < c x j → ∃ y ∈ F, R x y ∧ c y j < c x j :=
        fun x hx hh => hdown F hF j x hx a ha hh
      obtain ⟨a', p, hpa, hp⟩ := descend R F (fun x => c x j) (c a j) hmin hs u hu
      obtain ⟨b', q, hqa, hq⟩ := descend R F (fun x => c x j) (c a j) hmin hs v hv
      exact finish (c a j) a' b' p q hpa hqa (hminface F hF j a ha hmin) (by omega)
    · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image F (fun x => c x j) ⟨u, hu⟩
      have hs : ∀ x ∈ F, c x j < c a j → ∃ y ∈ F, R x y ∧ c x j < c y j :=
        fun x hx hh => hup F hF j x hx a ha hh
      obtain ⟨a', p, hpa, hp⟩ := ascend R F (fun x => c x j) (c a j) (K j)
        hmax (hK a ha j) hs u hu
      obtain ⟨b', q, hqa, hq⟩ := ascend R F (fun x => c x j) (c a j) (K j)
        hmax (hK a ha j) hs v hv
      have haK := hK a ha j
      exact finish (c a j) a' b' p q hpa hqa (hmaxface F hF j a ha hmax) (by omega)

/-- Rank of an actual real coordinate in its finite observed level set. -/
def levelRank (S : Finset ℝ) (x : ℝ) : ℕ := (S.filter (fun t => t < x)).card

lemma levelRank_mono (S : Finset ℝ) {x y : ℝ} (hxy : x ≤ y) :
    levelRank S x ≤ levelRank S y := by
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
    (Finset.mem_filter.mp hz).2.trans_le hxy⟩

lemma levelRank_strict (S : Finset ℝ) {x y : ℝ} (hx : x ∈ S) (hxy : x < y) :
    levelRank S x < levelRank S y := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      (Finset.mem_filter.mp hz).2.trans hxy⟩
  · intro he
    have hm : x ∈ S.filter (fun z => z < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← he] at hm
    exact (lt_irrefl x) (Finset.mem_filter.mp hm).2

lemma levelRank_lt_iff (S : Finset ℝ) {x y : ℝ} (hx : x ∈ S) :
    levelRank S x < levelRank S y ↔ x < y := by
  constructor
  · intro h
    by_contra hn
    have hh := levelRank_mono S (le_of_not_gt hn)
    omega
  · exact levelRank_strict S hx

lemma levelRank_eq_iff (S : Finset ℝ) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    levelRank S x = levelRank S y ↔ x = y := by
  constructor
  · intro he
    rcases lt_trichotomy x y with h | h | h
    · have hh := levelRank_strict S hx h
      omega
    · exact h
    · have hh := levelRank_strict S hy h
      omega
  · intro he
    rw [he]

lemma levelRank_bound (S : Finset ℝ) {x : ℝ} (hx : x ∈ S) :
    levelRank S x ≤ S.card-1 := by
  have h : levelRank S x < S.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hm : x ∈ S.filter (fun t => t < x) := by rw [he]; exact hx
    exact (lt_irrefl x) (Finset.mem_filter.mp hm).2
  omega

#print axioms descend
#print axioms ascend
#print axioms rank_routes
#print axioms levelRank_bound

end Hirsch.CoordinateRoute

/-- A finite-face coordinate routing theorem. The local hypotheses are one-step
improvement and extreme-face closure, never a pre-existing short route. -/
theorem solution
    (n d : ℕ) (R : Fin n → Fin n → Prop)
    (hsym : ∀ a b, R a b → R b a)
    (c : Fin n → Fin d → ℝ) (hinj : Function.Injective c)
    (Face : Finset (Fin n) → Prop)
    (hminface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c a j ≤ c x j) → Face (F.filter (fun x => c x j = c a j)))
    (hmaxface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c x j ≤ c a j) → Face (F.filter (fun x => c x j = c a j)))
    (hdown : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c y j < c x j → ∃ z ∈ F, R x z ∧ c z j < c x j)
    (hup : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c x j < c y j → ∃ z ∈ F, R x z ∧ c x j < c z j)
    (F : Finset (Fin n)) (hF : Face F)
    (u v : Fin n) (hu : u ∈ F) (hv : v ∈ F) :
    ∃ L : ℕ, L ≤ ∑ j : Fin d,
        ((Finset.univ.image (fun x : Fin n => c x j)).card-1) ∧
      ∃ p : ℕ → Fin n, p 0 = u ∧ p L = v ∧
        (∀ i, i ≤ L → p i ∈ F) ∧ (∀ i, i < L → R (p i) (p (i+1))) := by
  classical
  let levels : Fin d → Finset ℝ := fun j => Finset.univ.image (fun x : Fin n => c x j)
  let rank : Fin n → Fin d → ℕ := fun x j => Hirsch.CoordinateRoute.levelRank (levels j) (c x j)
  let K : Fin d → ℕ := fun j => (levels j).card-1
  have hmem : ∀ x j, c x j ∈ levels j :=
    fun x j => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hlt : ∀ x y j, rank x j < rank y j ↔ c x j < c y j :=
    fun x y j => Hirsch.CoordinateRoute.levelRank_lt_iff (levels j) (hmem x j)
  have heq : ∀ x y j, rank x j = rank y j ↔ c x j = c y j :=
    fun x y j => Hirsch.CoordinateRoute.levelRank_eq_iff (levels j) (hmem x j) (hmem y j)
  have hle : ∀ x y j, rank x j ≤ rank y j → c x j ≤ c y j := by
    intro x y j hh
    by_contra hn
    have hr := (hlt y x j).mpr (lt_of_not_ge hn)
    omega
  have hrinj : Function.Injective rank := by
    intro x y he
    apply hinj
    funext j
    exact (heq x y j).mp (congrFun he j)
  have hfilter : ∀ G : Finset (Fin n), ∀ j a,
      G.filter (fun x => rank x j = rank a j) = G.filter (fun x => c x j = c a j) := by
    intro G j a
    apply Finset.filter_congr
    intro x hx
    exact heq x a j
  have hm : ∀ G, Face G → ∀ j a, a ∈ G →
      (∀ x ∈ G, rank a j ≤ rank x j) → Face (G.filter (fun x => rank x j = rank a j)) := by
    intro G hG j a ha hh
    rw [hfilter]
    exact hminface G hG j a ha (fun x hx => hle a x j (hh x hx))
  have hM : ∀ G, Face G → ∀ j a, a ∈ G →
      (∀ x ∈ G, rank x j ≤ rank a j) → Face (G.filter (fun x => rank x j = rank a j)) := by
    intro G hG j a ha hh
    rw [hfilter]
    exact hmaxface G hG j a ha (fun x hx => hle x a j (hh x hx))
  have hd : ∀ G, Face G → ∀ j x, x ∈ G → ∀ y, y ∈ G →
      rank y j < rank x j → ∃ z ∈ G, R x z ∧ rank z j < rank x j := by
    intro G hG j x hx y hy hh
    obtain ⟨z, hz, hxz, hh'⟩ := hdown G hG j x hx y hy ((hlt y x j).mp hh)
    exact ⟨z, hz, hxz, (hlt z x j).mpr hh'⟩
  have hu' : ∀ G, Face G → ∀ j x, x ∈ G → ∀ y, y ∈ G →
      rank x j < rank y j → ∃ z ∈ G, R x z ∧ rank x j < rank z j := by
    intro G hG j x hx y hy hh
    obtain ⟨z, hz, hxz, hh'⟩ := hup G hG j x hx y hy ((hlt x y j).mp hh)
    exact ⟨z, hz, hxz, (hlt x z j).mpr hh'⟩
  obtain ⟨p, hp⟩ := Hirsch.CoordinateRoute.rank_routes d R hsym rank hrinj K Face hm hM hd hu'
    Finset.univ F hF
    (fun x hx j => Hirsch.CoordinateRoute.levelRank_bound (levels j) (hmem x j))
    (by intro j hj; exact False.elim (hj (Finset.mem_univ j))) u hu v hv
  refine ⟨p.length, ?_, p.point, p.first, p.last, p.mem, p.step⟩
  simpa only [K, levels] using hp

#print axioms solution
