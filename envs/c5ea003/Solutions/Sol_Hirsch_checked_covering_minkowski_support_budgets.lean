-- Prove2me | solution 1 for Hirsch.checked_covering_minkowski_support_budgets
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T00:34:06.436633+00:00
-- url     : https://prove2.me/submissions/52ab0db3-9f64-40fe-abff-fa1f3e2884fb

import Mathlib

open scoped BigOperators

namespace Hirsch.PositiveCircuitRank

/-- Support minimality among nonnegative null vectors controls every SIGNED
null vector on the same support. No full-rank assumption is used. -/
theorem signed_ray_of_minimal (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hAx : A x = 0) (hxne : x ≠ 0)
    (hmin : ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → A y = 0 → y ≠ 0 →
      Function.support y ⊆ Function.support x →
      Function.support x ⊆ Function.support y)
    (z : Fin n → ℝ) (hAz : A z = 0)
    (hzx : Function.support z ⊆ Function.support x) :
    ∃ t : ℝ, z = t • x := by
  classical
  have hex : ∃ i, 0 < x i := by
    by_contra h
    push_neg at h
    apply hxne
    funext i
    exact le_antisymm (h i) (hx i)
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [s, ne_of_gt hi]⟩
  obtain ⟨j, hj, hratio⟩ :=
    Finset.exists_min_image s (fun i => z i / x i) hs
  have hxj : x j ≠ 0 := (Finset.mem_filter.mp hj).2
  let t : ℝ := z j / x j
  have htj : t * x j = z j := div_mul_cancel₀ _ hxj
  have hout : ∀ i, x i = 0 → z i = 0 := by
    intro i hxi
    by_contra hzi
    exact (hzx hzi) hxi
  let q : Fin n → ℝ := z - t • x
  have hq : ∀ i, 0 ≤ q i := by
    intro i
    change 0 ≤ z i - t * x i
    by_cases hxi : x i = 0
    · simp [hxi, hout i hxi]
    · have hpos : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hxi)
      have hle : t ≤ z i / x i := hratio i (by simp [s, hxi])
      have hmul : t * x i ≤ z i := (le_div_iff₀ hpos).mp hle
      linarith
  have hAq : A q = 0 := by
    simp [q, map_sub, map_smul, hAz, hAx]
  have hqsub : Function.support q ⊆ Function.support x := by
    intro i hi
    change q i ≠ 0 at hi
    change x i ≠ 0
    intro hxi
    exact hi (by simp [q, hxi, hout i hxi])
  have hqzero : q = 0 := by
    by_contra hne
    have hjq : q j ≠ 0 := (hmin q hq hAq hne hqsub) hxj
    apply hjq
    change z j - t * x j = 0
    linarith
  exact ⟨t, sub_eq_zero.mp hqzero⟩

/-- An explicit injection into range(A) × ℝ gives the sharp rank+1 cutoff. -/
theorem support_card_le_rank_add_one (n k : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : Fin n → ℝ)
    (hxne : x ≠ 0)
    (hline : ∀ z : Fin n → ℝ, A z = 0 →
      Function.support z ⊆ Function.support x → ∃ t : ℝ, z = t • x) :
    Nat.card {i : Fin n // x i ≠ 0} ≤ Module.finrank ℝ (LinearMap.range A) + 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxne (funext h)
  let S := {i : Fin n // x i ≠ 0}
  let e : (S → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun v i => if h : x i ≠ 0 then v ⟨i, h⟩ else 0
      map_add' := by
        intro u v
        funext i
        by_cases h : x i ≠ 0
        · simp [h]
        · have hx0 : x i = 0 := by simpa using h
          simp [h, hx0]
      map_smul' := by
        intro r v
        funext i
        by_cases h : x i ≠ 0 <;> simp [h] }
  let f : (S → ℝ) →ₗ[ℝ] (LinearMap.range A × ℝ) :=
    { toFun := fun v => (⟨A (e v), ⟨e v, rfl⟩⟩, (e v) j)
      map_add' := by
        intro u v
        apply Prod.ext
        · apply Subtype.ext
          change A (e (u + v)) = A (e u) + A (e v)
          simp only [map_add]
        · change (e (u + v)) j = (e u) j + (e v) j
          simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro r v
        apply Prod.ext
        · apply Subtype.ext
          change A (e (r • v)) = r • A (e v)
          simp only [map_smul, RingHom.id_apply]
        · change (e (r • v)) j = r • (e v) j
          simp only [map_smul, RingHom.id_apply, Pi.smul_apply] }
  have hf : Function.Injective f := by
    intro u v huv
    have hfzero : f (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hA : A (e (u - v)) = 0 :=
      congrArg (fun w : LinearMap.range A × ℝ => (w.1 : Fin k → ℝ)) hfzero
    have hjzero : (e (u - v)) j = 0 := congrArg Prod.snd hfzero
    have hsub : Function.support (e (u - v)) ⊆ Function.support x := by
      intro i hi
      change (e (u - v)) i ≠ 0 at hi
      change x i ≠ 0
      intro hxi
      exact hi (by simp [e, hxi])
    obtain ⟨t, ht⟩ := hline (e (u - v)) hA hsub
    have htzero : t = 0 := by
      have hval := congrFun ht j
      change (e (u - v)) j = t * x j at hval
      have hm : t * x j = 0 := hval.symm.trans hjzero
      exact (mul_eq_zero.mp hm).resolve_right hj
    have hezero : e (u - v) = 0 := by rw [ht, htzero, zero_smul]
    funext i
    have hi := congrFun hezero i.1
    have hz : u i - v i = 0 := by simpa [e, i.property] using hi
    exact sub_eq_zero.mp hz
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simpa only [Module.finrank_fintype_fun_eq_card, Module.finrank_prod,
    Module.finrank_self, Nat.card_eq_fintype_card] using hd

end Hirsch.PositiveCircuitRank

/-! A certificate checker, not a trusted row-reduction oracle.
Every bounded support is audited, including supports that produce no output.
The two rank primitives above are reused verbatim from accepted PR #222.
-/
namespace Hirsch.CheckedCatalogue

abbrev QMatrix (n k : ℕ) := Fin k → Fin n → ℚ
abbrev LeftData (n k : ℕ) := Finset (Fin n) → Fin n → Option (Fin k) → ℚ

def column (n k : ℕ) (L : LeftData n k) (s : Finset (Fin n)) : Fin n → ℚ :=
  fun i => if i ∈ s then L s i none else 0

/-- One finite exact arithmetic certificate for an entire support. -/
def CellOK (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ) (s : Finset (Fin n)) : Prop :=
  if tag s then
    (∃ i, z s i ≠ 0) ∧ (∀ i, i ∉ s → z s i = 0) ∧
      (∀ r, (∑ i, A r i * z s i) = 0) ∧ (∑ i, z s i) = 0
  else
    ∀ i ∈ s, ∀ j ∈ s,
      (∑ r, L s i (some r) * A r j) + L s i none = if i = j then 1 else 0

instance (n k : ℕ) (A : QMatrix n k) (tag : Finset (Fin n) → Bool)
    (L : LeftData n k) (z : Finset (Fin n) → Fin n → ℚ) (s : Finset (Fin n)) :
    Decidable (CellOK n k A tag L z s) :=
  inferInstanceAs (Decidable (if tag s then
    (∃ i, z s i ≠ 0) ∧ (∀ i, i ∉ s → z s i = 0) ∧
      (∀ r, (∑ i, A r i * z s i) = 0) ∧ (∑ i, z s i) = 0
    else ∀ i ∈ s, ∀ j ∈ s,
      (∑ r, L s i (some r) * A r j) + L s i none = if i = j then 1 else 0))

def Emit (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k) (s : Finset (Fin n)) : Prop :=
  tag s = false ∧ (∀ i ∈ s, 0 < L s i none) ∧
    (∀ r, (∑ i, A r i * column n k L s i) = 0) ∧
    (∑ i, column n k L s i) = 1

instance (n k : ℕ) (A : QMatrix n k) (tag : Finset (Fin n) → Bool)
    (L : LeftData n k) (s : Finset (Fin n)) :
    Decidable (Emit n k A tag L s) :=
  inferInstanceAs (Decidable (tag s = false ∧ (∀ i ∈ s, 0 < L s i none) ∧
    (∀ r, (∑ i, A r i * column n k L s i) = 0) ∧
    (∑ i, column n k L s i) = 1))

/-- Enumerate cardinalities separately; do not generate the entire powerset
and then pretend that filtering it was bounded-support enumeration. -/
def supports (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.range (k + 2)).biUnion fun r => (Finset.univ : Finset (Fin n)).powersetCard r

lemma mem_supports (n k : ℕ) (s : Finset (Fin n)) :
    s ∈ supports n k ↔ s.card ≤ k + 1 := by
  classical
  simp only [supports, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨r, hr, hs⟩
    omega
  · intro h
    exact ⟨s.card, by omega, rfl⟩

/-- This executable Boolean consumes only finite rational equalities and signs. -/
def check (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ) : Bool :=
  decide (∀ s ∈ supports n k, CellOK n k A tag L z s)

lemma check_iff (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ) :
    check n k A tag L z = true ↔
      ∀ s : Finset (Fin n), s.card ≤ k + 1 → CellOK n k A tag L z s := by
  simp only [check, decide_eq_true_eq, mem_supports]

/-- No rank computation or solver call occurs in the output filter. -/
def catalogue (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k) : Finset (Fin n → ℚ) :=
  ((supports n k).filter (Emit n k A tag L)).image (column n k L)

def rowMap (n k : ℕ) (A : QMatrix n k) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun x r := ∑ i, (A r i : ℝ) * x i
  map_add' x y := by
    funext r
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t x := by
    funext r
    change (∑ i, (A r i : ℝ) * (t * x i)) = t * ∑ i, (A r i : ℝ) * x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The finite left-inverse identities reconstruct EVERY supported real null
vector, not merely the rational vectors used to generate the certificate. -/
lemma left_formula (n k : ℕ) (A : Fin k → Fin n → ℝ)
    (L : Fin n → Option (Fin k) → ℝ) (s : Finset (Fin n))
    (hL : ∀ i ∈ s, ∀ j ∈ s,
      (∑ r, L i (some r) * A r j) + L i none = if i = j then 1 else 0)
    (x : Fin n → ℝ) (hx : ∀ i, i ∉ s → x i = 0)
    (hAx : ∀ r, (∑ i, A r i * x i) = 0) :
    ∀ i ∈ s, x i = L i none * (∑ j, x j) := by
  classical
  intro i hi
  have hrecover : (∑ j, ((∑ r, L i (some r) * A r j) + L i none) * x j) = x i := by
    calc
      _ = ∑ j, if i = j then x j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ s
        · rw [hL i hi j hj]
          split_ifs <;> simp
        · have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
          simp [hx j hj, hij]
      _ = x i := by simp
  have hshuffle :
      (∑ j, ((∑ r, L i (some r) * A r j) + L i none) * x j) =
      (∑ r, L i (some r) * (∑ j, A r j * x j)) + L i none * (∑ j, x j) := by
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    · simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · exact (Finset.mul_sum _ _ _).symm
  rw [hshuffle] at hrecover
  simp only [hAx, mul_zero, Finset.sum_const_zero, zero_add] at hrecover
  exact hrecover.symm

lemma cast_left (n k : ℕ) (A : QMatrix n k) (L : LeftData n k)
    (s : Finset (Fin n))
    (hL : ∀ i ∈ s, ∀ j ∈ s,
      (∑ r, L s i (some r) * A r j) + L s i none = if i = j then 1 else 0) :
    ∀ i ∈ s, ∀ j ∈ s,
      (∑ r, (L s i (some r) : ℝ) * (A r j : ℝ)) + (L s i none : ℝ) =
        if i = j then 1 else 0 := by
  intro i hi j hj
  have h := hL i hi j hj
  by_cases he : i = j
  · simp only [he, ite_true] at h ⊢
    exact_mod_cast h
  · simp only [he, ite_false] at h ⊢
    exact_mod_cast h

/-- Soundness of an emitted normalized candidate. -/
theorem emitted_minimal (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ) (s : Finset (Fin n))
    (hcell : CellOK n k A tag L z s) (hemit : Emit n k A tag L s) :
    let x : Fin n → ℝ := fun i => (column n k L s i : ℝ)
    (∀ i, 0 ≤ x i) ∧ rowMap n k A x = 0 ∧ (∑ i, x i) = 1 ∧
      ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → rowMap n k A y = 0 → y ≠ 0 →
        Function.support y ⊆ Function.support x → Function.support x ⊆ Function.support y := by
  classical
  rcases hemit with ⟨htag, hpos, hnull, hmass⟩
  have hL := cast_left n k A L s (by simpa [CellOK, htag] using hcell)
  let x : Fin n → ℝ := fun i => (column n k L s i : ℝ)
  have hout : ∀ i, i ∉ s → x i = 0 := by intro i hi; simp [x, column, hi]
  have hx : ∀ i, 0 ≤ x i := by
    intro i
    by_cases hi : i ∈ s
    · have hp : 0 < (L s i none : ℝ) := by exact_mod_cast hpos i hi
      simpa [x, column, hi] using hp.le
    · simp [hout i hi]
  have hAx : rowMap n k A x = 0 := by
    funext r
    change (∑ i, (A r i : ℝ) * (column n k L s i : ℝ)) = 0
    exact_mod_cast hnull r
  have hm : (∑ i, x i) = 1 := by
    dsimp only [x]
    exact_mod_cast hmass
  refine ⟨hx, hAx, hm, ?_⟩
  intro y _hy hAy hyne hsub
  have hyout : ∀ i, i ∉ s → y i = 0 := by
    intro i hi
    by_contra hne
    exact (hsub hne) (hout i hi)
  have hyrows : ∀ r, (∑ i, (A r i : ℝ) * y i) = 0 := fun r => congrFun hAy r
  have hrep : y = (∑ i, y i) • x := by
    funext i
    by_cases hi : i ∈ s
    · have hf := left_formula n k (fun r i => (A r i : ℝ))
        (fun i j => (L s i j : ℝ)) s hL y hyout hyrows i hi
      simpa [x, column, hi, Pi.smul_apply, smul_eq_mul, mul_comm] using hf
    · simp [hyout i hi, hout i hi]
  have hmassne : (∑ i, y i) ≠ 0 := by
    intro hzero
    apply hyne
    rw [hrep, hzero, zero_smul]
  intro i hi
  change y i ≠ 0
  rw [hrep]
  exact mul_ne_zero hmassne hi

/-- Completeness: no normalized REAL positive circuit is omitted by a passing
finite rational table. The cutoff is k+1; the sharper rank+1 theorem is reused. -/
theorem table_complete (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ)
    (hcert : ∀ s : Finset (Fin n), s.card ≤ k + 1 → CellOK n k A tag L z s)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hAx : rowMap n k A x = 0) (hmass : (∑ i, x i) = 1)
    (hmin : ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → rowMap n k A y = 0 → y ≠ 0 →
      Function.support y ⊆ Function.support x → Function.support x ⊆ Function.support y) :
    ∃ q ∈ catalogue n k A tag L, x = fun i => (q i : ℝ) := by
  classical
  have hxne : x ≠ 0 := by intro h; simp [h] at hmass
  have hline := Hirsch.PositiveCircuitRank.signed_ray_of_minimal n k
    (rowMap n k A) x hx hAx hxne hmin
  have hbound := Hirsch.PositiveCircuitRank.support_card_le_rank_add_one n k
    (rowMap n k A) x hxne hline
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)
  have hcard : s.card = Nat.card {i : Fin n // x i ≠ 0} := by
    simp [s, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hrange : Module.finrank ℝ (LinearMap.range (rowMap n k A)) ≤ k := by
    have h := Submodule.finrank_le (LinearMap.range (rowMap n k A))
    simpa using h
  have hsbound : s.card ≤ k + 1 := by omega
  have hs : s ∈ supports n k := (mem_supports n k s).mpr hsbound
  have hcell := hcert s hsbound
  have hxout : ∀ i, i ∉ s → x i = 0 := by
    intro i hi
    by_contra hne
    exact hi (by simp [s, hne])
  have hfalse : tag s = false := by
    cases ht : tag s with
    | false => rfl
    | true =>
      have hdep : (∃ i, z s i ≠ 0) ∧ (∀ i, i ∉ s → z s i = 0) ∧
          (∀ r, (∑ i, A r i * z s i) = 0) ∧ (∑ i, z s i) = 0 := by
        simpa [CellOK, ht] using hcell
      obtain ⟨j, hj⟩ := hdep.1
      let v : Fin n → ℝ := fun i => (z s i : ℝ)
      have hvA : rowMap n k A v = 0 := by
        funext r
        change (∑ i, (A r i : ℝ) * (z s i : ℝ)) = 0
        exact_mod_cast hdep.2.2.1 r
      have hvsub : Function.support v ⊆ Function.support x := by
        intro i hi
        change x i ≠ 0
        intro hxi
        have his : i ∉ s := by simp [s, hxi]
        exact hi (by simp [v, hdep.2.1 i his])
      obtain ⟨t, htvec⟩ := hline v hvA hvsub
      have hvsum : (∑ i, v i) = 0 := by dsimp only [v]; exact_mod_cast hdep.2.2.2
      have htzero := congrArg (fun u : Fin n → ℝ => ∑ i, u i) htvec
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
        hvsum, hmass, mul_one] at htzero
      have hzj := congrFun htvec j
      rw [← htzero, zero_smul] at hzj
      have hzero : (z s j : ℝ) = 0 := hzj
      exact False.elim (hj (by exact_mod_cast hzero))
  have hL := cast_left n k A L s (by
    simpa [CellOK, hfalse] using hcell)
  have hxc : x = fun i => (column n k L s i : ℝ) := by
    funext i
    by_cases hi : i ∈ s
    · have hf := left_formula n k (fun r i => (A r i : ℝ))
        (fun i j => (L s i j : ℝ)) s hL x hxout (fun r => congrFun hAx r) i hi
      simpa [column, hi, hmass] using hf
    · simp [column, hi, hxout i hi]
  have hem : Emit n k A tag L s := by
    refine ⟨hfalse, ?_, ?_, ?_⟩
    · intro i hi
      have hxi : x i ≠ 0 := (Finset.mem_filter.mp hi).2
      have hp : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hxi)
      have he := congrFun hxc i
      simp only [column, if_pos hi] at he
      rw [he] at hp
      exact_mod_cast hp
    · intro r
      have ha := congrFun hAx r
      change (∑ i, (A r i : ℝ) * x i) = 0 at ha
      rw [hxc] at ha
      change (∑ i, (A r i : ℝ) * (column n k L s i : ℝ)) = 0 at ha
      exact_mod_cast ha
    · rw [hxc] at hmass
      change (∑ i, (column n k L s i : ℝ)) = 1 at hmass
      exact_mod_cast hmass
  exact ⟨column n k L s, Finset.mem_image.mpr
    ⟨s, Finset.mem_filter.mpr ⟨hs, hem⟩, rfl⟩, hxc⟩

/-- Correctness of the executable finite rational checker and output filter. -/
theorem checked_exact (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ) (hcheck : check n k A tag L z = true) :
    ∀ x : Fin n → ℝ,
      ((∀ i, 0 ≤ x i) ∧ rowMap n k A x = 0 ∧ (∑ i, x i) = 1 ∧
        ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → rowMap n k A y = 0 → y ≠ 0 →
          Function.support y ⊆ Function.support x → Function.support x ⊆ Function.support y) ↔
        ∃ q ∈ catalogue n k A tag L, x = fun i => (q i : ℝ) := by
  classical
  have hc := (check_iff n k A tag L z).mp hcheck
  intro x
  constructor
  · rintro ⟨hx, hAx, hm, hmin⟩
    exact table_complete n k A tag L z hc x hx hAx hm hmin
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hs, he⟩ := Finset.mem_filter.mp hs
    exact emitted_minimal n k A tag L z s (hc s ((mem_supports n k s).mp hs)) he

end Hirsch.CheckedCatalogue

namespace Hirsch.PositiveCircuitTests

noncomputable def supp {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) : Finset (ι) := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

@[simp] theorem mem_supp {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) (i : ι) :
    i ∈ supp x ↔ x i ≠ 0 := by
  classical
  simp [supp]

def NonnegNull {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ A x = 0

def Circuit {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (x : ι → ℝ) : Prop :=
  NonnegNull A x ∧ x ≠ 0 ∧
    ∀ y, NonnegNull A y → y ≠ 0 → supp y ⊆ supp x → supp x ⊆ supp y

private theorem positive_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) : ∃ i, 0 < x i := by
  by_contra h
  push_neg at h
  apply hne
  funext i
  exact le_antisymm (h i) (hx i)

/-- Subtract as far as possible in a supported direction with a positive entry. -/
private theorem prune {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsub : supp y ⊆ supp x)
    (hy : ∃ i, 0 < y i) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ (x - t • y) i) ∧
      supp (x - t • y) ⊂ supp x := by
  classical
  let s : Finset (ι) := Finset.univ.filter (fun i => 0 < y i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hy
    exact ⟨i, by simp [s, hi]⟩
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_min_image s (fun j => x j / y j) hs
  have hyi : 0 < y i := (Finset.mem_filter.mp hi).2
  have hxi : 0 < x i := by
    have hne : x i ≠ 0 := (mem_supp x i).mp
      (hsub ((mem_supp y i).mpr (ne_of_gt hyi)))
    exact lt_of_le_of_ne (hx i) (Ne.symm hne)
  let t : ℝ := x i / y i
  have ht : 0 < t := div_pos hxi hyi
  have hti : t * y i = x i := by
    exact div_mul_cancel₀ _ (ne_of_gt hyi)
  have hz : ∀ j, 0 ≤ (x - t • y) j := by
    intro j
    change 0 ≤ x j - t * y j
    by_cases hj : 0 < y j
    · have hratio : t ≤ x j / y j := hmin j (by simp [s, hj])
      have hprod : t * y j ≤ x j := (le_div_iff₀ hj).mp hratio
      linarith
    · have hprod : t * y j ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (le_of_not_gt hj)
      linarith [hx j]
  have hzero : ∀ j, x j = 0 → y j = 0 := by
    intro j hj
    by_contra hj'
    exact ((mem_supp x j).mp (hsub ((mem_supp y j).mpr hj'))) hj
  have hsmall : supp (x - t • y) ⊆ supp x := by
    intro j hj
    apply (mem_supp x j).mpr
    intro hxj
    have hyj := hzero j hxj
    have hneq := (mem_supp (x - t • y) j).mp hj
    apply hneq
    change x j - t * y j = 0
    rw [hxj, hyj]
    ring
  have hiout : i ∉ supp (x - t • y) := by
    intro hi'
    have hneq := (mem_supp (x - t • y) i).mp hi'
    apply hneq
    change x i - t * y i = 0
    linarith
  refine ⟨t, ht, hz, Finset.ssubset_iff_subset_ne.mpr ⟨hsmall, ?_⟩⟩
  intro heq
  apply hiout
  rw [heq]
  exact (mem_supp x i).mpr (ne_of_gt hxi)

/-- Every strictly negative nonnegative null certificate has a negative positive
circuit inside its support. Minimality concerns ALL nonnegative null vectors,
not just the negative ones. -/
theorem negative_circuit {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (b : (ι → ℝ) →ₗ[ℝ] ℝ) (w : ι → ℝ)
    (hw : NonnegNull A w) (hb : b w < 0) :
    ∃ x, Circuit A x ∧ b x < 0 ∧ supp x ⊆ supp w := by
  classical
  let P : ℕ → Prop := fun q => ∃ x : ι → ℝ,
    NonnegNull A x ∧ b x < 0 ∧ supp x ⊆ supp w ∧ (supp x).card = q
  have hex : ∃ q, P q := ⟨(supp w).card, w, hw, hb, fun _ h => h, rfl⟩
  obtain ⟨x, hx, hbx, hxw, hcard⟩ := Nat.find_spec hex
  have hminimal : ∀ y, NonnegNull A y → b y < 0 → supp y ⊆ supp w →
      (supp x).card ≤ (supp y).card := by
    intro y hy hby hyw
    rw [hcard]
    exact Nat.find_min' hex ⟨y, hy, hby, hyw, rfl⟩
  have hxne : x ≠ 0 := by
    intro h
    simpa [h] using hbx
  refine ⟨x, ⟨hx, hxne, ?_⟩, hbx, hxw⟩
  intro y hy hyne hyx
  by_cases hby : b y < 0
  · have hle := hminimal y hy hby (fun i hi => hxw (hyx hi))
    have heq : supp y = supp x := Finset.eq_of_subset_of_card_le hyx hle
    exact fun i hi => heq.symm ▸ hi
  · have hby0 : 0 ≤ b y := le_of_not_gt hby
    obtain ⟨t, ht, hz, hstrict⟩ :=
      prune x y hx.1 hyx (positive_coordinate y hy.1 hyne)
    have hzA : A (x - t • y) = 0 := by
      simp [map_sub, map_smul, hx.2, hy.2]
    have hzb : b (x - t • y) < 0 := by
      rw [map_sub, map_smul, smul_eq_mul]
      have hprod : 0 ≤ t * b y := mul_nonneg (le_of_lt ht) hby0
      linarith
    have hle := hminimal (x - t • y) ⟨hz, hzA⟩ hzb
      (fun i hi => hxw ((Finset.ssubset_iff_subset_ne.mp hstrict).1 hi))
    have hlt := Finset.card_lt_card hstrict
    omega

end Hirsch.PositiveCircuitTests

/-! The new bridge: the actual checked catalogue tests every real linear
functional on the whole nonnegative kernel, not only normalized circuits. -/
namespace Hirsch.CheckedCatalogue

/-- Normalize the negative circuit supplied by the accepted support-pruning
argument, then use the accepted arithmetic checker's real completeness. -/
theorem checked_linear_tests (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ)
    (hcheck : check n k A tag L z = true)
    (B : (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    (∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i) → rowMap n k A w = 0 → 0 ≤ B w) ↔
      ∀ q ∈ catalogue n k A tag L, 0 ≤ B (fun i => (q i : ℝ)) := by
  classical
  constructor
  · intro h q hq
    have hc := (checked_exact n k A tag L z hcheck (fun i => (q i : ℝ))).mpr
      ⟨q, hq, rfl⟩
    exact h _ hc.1 hc.2.1
  · intro h w hw hAw
    by_contra hbad
    obtain ⟨x, hx, hBx, _⟩ := Hirsch.PositiveCircuitTests.negative_circuit
      (rowMap n k A) B w ⟨hw, hAw⟩ (lt_of_not_ge hbad)
    obtain ⟨j, hj⟩ : ∃ j, 0 < x j := by
      by_contra h
      push_neg at h
      apply hx.2.1
      funext i
      exact le_antisymm (h i) (hx.1.1 i)
    let mass : ℝ := ∑ i, x i
    have hmass : 0 < mass := lt_of_lt_of_le hj
      (Finset.single_le_sum (fun i _ => hx.1.1 i) (Finset.mem_univ j))
    have hinv : 0 < mass⁻¹ := inv_pos.mpr hmass
    let v : Fin n → ℝ := mass⁻¹ • x
    have hv : ∀ i, 0 ≤ v i := by
      intro i
      exact mul_nonneg hinv.le (hx.1.1 i)
    have hAv : rowMap n k A v = 0 := by
      simp only [v, map_smul, hx.1.2, smul_zero]
    have hvsum : (∑ i, v i) = 1 := by
      change (∑ i, mass⁻¹ * x i) = 1
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ (ne_of_gt hmass)
    have hvx : Function.support v = Function.support x := by
      ext i
      change mass⁻¹ * x i ≠ 0 ↔ x i ≠ 0
      constructor
      · exact fun h hi => h (by rw [hi, mul_zero])
      · exact fun h => mul_ne_zero (ne_of_gt hinv) h
    have hvmin : ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → rowMap n k A y = 0 →
        y ≠ 0 → Function.support y ⊆ Function.support v →
          Function.support v ⊆ Function.support y := by
      intro y hy hAy hyne hyv
      have hyx : Hirsch.PositiveCircuitTests.supp y ⊆ Hirsch.PositiveCircuitTests.supp x := by
        intro i hi
        have hyi : i ∈ Function.support y :=
          (Hirsch.PositiveCircuitTests.mem_supp y i).mp hi
        have hxi : i ∈ Function.support x := hvx ▸ hyv hyi
        exact (Hirsch.PositiveCircuitTests.mem_supp x i).mpr hxi
      have hback := hx.2.2 y ⟨hy, hAy⟩ hyne hyx
      intro i hi
      have hxi : i ∈ Function.support x := hvx ▸ hi
      exact (Hirsch.PositiveCircuitTests.mem_supp y i).mp
        (hback ((Hirsch.PositiveCircuitTests.mem_supp x i).mpr hxi))
    obtain ⟨q, hq, hvq⟩ := (checked_exact n k A tag L z hcheck v).mp
      ⟨hv, hAv, hvsum, hvmin⟩
    have hnon : 0 ≤ B v := by rw [hvq]; exact h q hq
    have hneg : B v < 0 := by
      rw [show v = mass⁻¹ • x from rfl, map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg hinv hBx
    exact (not_lt_of_ge hnon) hneg

/-- Right-hand-side specialization. The coefficients may be arbitrary REAL
numbers even though the checker and catalogue use exact rational arithmetic. -/
def rhsPairing (n : ℕ) (b : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ i, w i * b i
  map_add' u v := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

theorem checked_rhs_tests (n k : ℕ) (A : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ)
    (hcheck : check n k A tag L z = true) (b : Fin n → ℝ) :
    (∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i) →
      (∀ r, (∑ i, (A r i : ℝ) * w i) = 0) → 0 ≤ ∑ i, w i * b i) ↔
      ∀ q ∈ catalogue n k A tag L, 0 ≤ ∑ i, (q i : ℝ) * b i := by
  have hn (w : Fin n → ℝ) : rowMap n k A w = 0 ↔
      ∀ r, (∑ i, (A r i : ℝ) * w i) = 0 := by
    constructor
    · intro h r
      exact congrFun h r
    · intro h
      funext r
      exact h r
  have h := checked_linear_tests n k A tag L z hcheck (rhsPairing n b)
  change (∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i) → rowMap n k A w = 0 →
    0 ≤ ∑ i, w i * b i) ↔
    (∀ q ∈ catalogue n k A tag L, 0 ≤ ∑ i, (q i : ℝ) * b i) at h
  simpa only [hn] using h

end Hirsch.CheckedCatalogue


open Set

private theorem compact_positive_of_tests
    (m : ℕ) (K : Set (Fin m → ℝ))
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (htest : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      ∃ x ∈ K, 0 ≤ ∑ i, w i * x i) :
    ∃ x ∈ K, ∀ i, 0 ≤ x i := by
  classical
  by_contra hn
  have hd : Disjoint K (ProperCone.positive ℝ (Fin m → ℝ) : Set (Fin m → ℝ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hpos
    exact hn ⟨x, hx, ProperCone.mem_positive.mp hpos⟩
  obtain ⟨f, hf, hneg⟩ :=
    (ProperCone.positive ℝ (Fin m → ℝ)).hyperplane_separation hconv hK hd
  let w : Fin m → ℝ := fun i => f (Pi.single i (1 : ℝ))
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    apply hf
    change (0 : Fin m → ℝ) ≤ Pi.single i (1 : ℝ)
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]
  obtain ⟨x, hx, hsum⟩ := htest w hw
  have hexp : (∑ i : Fin m, x i • (Pi.single i (1 : ℝ))) = x := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  have hfx : f x = ∑ i, w i * x i := by
    calc
      f x = f (∑ i : Fin m, x i • (Pi.single i (1 : ℝ))) := congrArg f hexp.symm
      _ = ∑ i, x i * w i := by simp [w, map_sum, map_smul, smul_eq_mul]
      _ = ∑ i, w i * x i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
  have hlt := hneg x hx
  rw [hfx] at hlt
  exact (not_lt_of_ge hsum) hlt

private theorem compact_linear_feasible_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (Q : Set E) (hQ : IsCompact Q) (hconv : Convex ℝ Q)
    (a : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ) :
    (∃ q ∈ Q, ∀ i, b i ≤ a i q) ↔
      (∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ q ∈ Q, (∑ i, w i * b i) ≤ ∑ i, w i * a i q) := by
  constructor
  · rintro ⟨q, hq, hbound⟩ w hw
    exact ⟨q, hq, Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hbound i) (hw i))⟩
  · intro htest
    let φ : E → (Fin m → ℝ) := fun q i => a i q - b i
    have hcont : Continuous φ := by
      apply continuous_pi
      intro i
      exact (a i).continuous.sub continuous_const
    have hc : Convex ℝ (φ '' Q) := by
      intro u hu v hv α β hα hβ hsum
      obtain ⟨p, hp, rfl⟩ := hu
      obtain ⟨q, hq, rfl⟩ := hv
      refine ⟨α • p + β • q, hconv hp hq hα hβ hsum, ?_⟩
      funext i
      change a i (α • p + β • q) - b i =
        α * (a i p - b i) + β * (a i q - b i)
      simp only [map_add, map_smul, smul_eq_mul]
      have hconst : α * b i + β * b i = b i := by
        rw [← add_mul, hsum, one_mul]
      nlinarith
    have ht : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ z ∈ φ '' Q, 0 ≤ ∑ i, w i * z i := by
      intro w hw
      obtain ⟨q, hq, hbound⟩ := htest w hw
      refine ⟨φ q, ⟨q, hq, rfl⟩, ?_⟩
      change 0 ≤ ∑ i, w i * (a i q - b i)
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact sub_nonneg.mpr hbound
    obtain ⟨z, hz, hpos⟩ := compact_positive_of_tests m (φ '' Q) (hQ.image hcont) hc ht
    obtain ⟨q, hq, rfl⟩ := hz
    exact ⟨q, hq, fun i => sub_nonneg.mp (hpos i)⟩



namespace Hirsch.FiniteAllocation

/-- The bounded allocation simplex; its zero-dimensional and zero-scale cases
are included. No boundedness assumption on the original polyhedron is used. -/
def allocationSimplex (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ (∑ j, x j) ≤ t}

lemma allocationSimplex_compact (k : ℕ) (t : ℝ) :
    IsCompact (allocationSimplex k t) := by
  classical
  have heq : allocationSimplex k t =
      Set.Icc (0 : Fin k → ℝ) (fun _ => t) ∩ {x | (∑ j, x j) ≤ t} := by
    ext x
    constructor
    · rintro ⟨hx, hs⟩
      refine ⟨⟨hx, ?_⟩, hs⟩
      intro j
      exact (Finset.single_le_sum (fun i _ => hx i) (Finset.mem_univ j)).trans hs
    · rintro ⟨⟨hx, _⟩, hs⟩
      exact ⟨hx, hs⟩
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)

lemma allocationSimplex_convex (k : ℕ) (t : ℝ) :
    Convex ℝ (allocationSimplex k t) := by
  intro x hx y hy α β hα hβ hab
  refine ⟨fun j => add_nonneg (mul_nonneg hα (hx.1 j))
    (mul_nonneg hβ (hy.1 j)), ?_⟩
  change (∑ j : Fin k, (α * x j + β * y j)) ≤ t
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h₁ := mul_le_mul_of_nonneg_left hx.2 hα
  have h₂ := mul_le_mul_of_nonneg_left hy.2 hβ
  have hc : α*t+β*t=t := by rw [← add_mul, hab, one_mul]
  linarith

lemma row_expansion {k : ℕ} (a : (Fin k → ℝ) →L[ℝ] ℝ) (x : Fin k → ℝ) :
    a x = ∑ j, a (Pi.single j (1 : ℝ)) * x j := by
  classical
  have he : (∑ j : Fin k, x j • Pi.single j (1 : ℝ)) = x := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  calc
    a x = a (∑ j : Fin k, x j • Pi.single j (1 : ℝ)) := congrArg a he.symm
    _ = ∑ j, a (Pi.single j (1 : ℝ)) * x j := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul, mul_comm]

lemma weighted_expansion {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (w : Fin m → ℝ) (x : Fin k → ℝ) :
    (∑ i, w i * a i x) =
      ∑ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) * x j := by
  calc
    (∑ i, w i * a i x) =
        ∑ i, w i * (∑ j, a i (Pi.single j (1 : ℝ)) * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : ℝ => w i * z) (row_expansion (a i) x)
    _ = ∑ j, ∑ i, w i * (a i (Pi.single j (1 : ℝ)) * x j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Construct the multiplier of the simplex-total row from the maximum of the
finitely many negative coefficients. This derives, rather than assumes, the
bounded allocation alternative needed after compact separation. -/
lemma weighted_simplex_minimum {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (w : Fin m → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ (μ : Fin k → ℝ) (ν : ℝ) (x : Fin k → ℝ),
      (∀ j, 0 ≤ μ j) ∧ 0 ≤ ν ∧ x ∈ allocationSimplex k t ∧
      (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) - μ j + ν = 0) ∧
      (∑ i, w i * a i x) = -ν*t := by
  classical
  let r : Fin k → ℝ := fun j => ∑ i, w i * a i (Pi.single j (1 : ℝ))
  let f : Option (Fin k) → ℝ := fun j => match j with
    | none => 0
    | some j => -r j
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Option (Fin k))) f ⟨none, Finset.mem_univ _⟩
  let ν := f j
  have hν : 0 ≤ ν := hmax none (Finset.mem_univ _)
  have hμ : ∀ i, 0 ≤ r i + ν := by
    intro i
    have hh : -r i ≤ ν := hmax (some i) (Finset.mem_univ _)
    linarith
  refine ⟨fun i => r i + ν, ν, ?_⟩
  cases j with
  | none =>
    refine ⟨0, hμ, hν, ⟨by simp, by simpa using ht⟩, ?_, ?_⟩
    · intro i
      change r i - (r i + ν) + ν = 0
      ring
    · simp [ν, f]
  | some j =>
    refine ⟨t • Pi.single j (1 : ℝ), hμ, hν, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : j = i
        · subst i
          simpa using ht
        · simp [Pi.smul_apply, Pi.single_apply, hi, Ne.symm hi]
      · change (∑ i : Fin k, t * (Pi.single j (1 : ℝ) : Fin k → ℝ) i) ≤ t
        simp [Pi.single_apply, mul_ite]
    · intro i
      change r i - (r i + ν) + ν = 0
      ring
    · simp only [map_smul, smul_eq_mul]
      calc
        (∑ i, w i * (t * a i (Pi.single j (1 : ℝ)))) =
            t * (∑ i, w i * a i (Pi.single j (1 : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = -ν*t := by dsimp [ν, f, r]; ring

/-- Full feasibility equivalence for the bounded simplex allocation system.
The sufficiency direction is proved from the compact separation core of #216,
not introduced as a Farkas axiom. -/
theorem allocation_alternative {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (b : Fin m → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    (∃ x ∈ allocationSimplex k t, ∀ i, a i x ≤ b i) ↔
      ∀ (w : Fin m → ℝ) (μ : Fin k → ℝ) (ν : ℝ),
        (∀ i, 0 ≤ w i) → (∀ j, 0 ≤ μ j) → 0 ≤ ν →
        (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) - μ j + ν = 0) →
        0 ≤ (∑ i, w i * b i) + ν*t := by
  constructor
  · rintro ⟨x, hx, hax⟩ w μ ν hw hμ hν hker
    have hweighted : (∑ i, w i * a i x) ≤ ∑ i, w i * b i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hax i) (hw i))
    have heq : (∑ i, w i * a i x) =
        (∑ j, μ j * x j) - ν*(∑ j, x j) := by
      rw [weighted_expansion]
      calc
        (∑ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) * x j) =
            ∑ j, (μ j - ν) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          have hh := hker j
          congr 1
          linarith
        _ = _ := by simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    have hpositive : 0 ≤ ∑ j, μ j * x j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hμ j) (hx.1 j))
    have hbudget := mul_le_mul_of_nonneg_left hx.2 hν
    linarith
  · intro hdual
    have htests : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ x ∈ allocationSimplex k t,
          (∑ i, w i * (-b i)) ≤ ∑ i, w i * (-(a i) x) := by
      intro w hw
      obtain ⟨μ, ν, x, hμ, hν, hx, hker, hval⟩ := weighted_simplex_minimum a w t ht
      have hh := hdual w μ ν hw hμ hν hker
      refine ⟨x, hx, ?_⟩
      simp only [ContinuousLinearMap.neg_apply, mul_neg, Finset.sum_neg_distrib]
      linarith
    obtain ⟨x, hx, hax⟩ :=
      (compact_linear_feasible_iff m (allocationSimplex k t)
        (allocationSimplex_compact k t) (allocationSimplex_convex k t)
        (fun i => -(a i)) (fun i => -b i)).mpr htests
    exact ⟨x, hx, fun i => by have hh := hax i; simpa using hh⟩

end Hirsch.FiniteAllocation

/-!
# Arbitrary covering allocation budgets, not only one simplex

A nonnegative row combination of the budget matrix dominates the total-mass
row. This bounds the nonnegative allocation variables. One redundant global
simplex inequality lets the ACCEPTED single-simplex alternative prove the full
multi-budget alternative. Its extra multiplier is absorbed algebraically; it
is not treated as a new independent constraint in the returned dual system.

NEW SOURCE CANDIDATE: no local Lean compiler or hosted verification is claimed.
-/
namespace Hirsch.CoveringAllocation
open Hirsch.FiniteAllocation

/-- A finite coverage certificate bounds total nonnegative allocation mass. -/
theorem total_mass_bound {k r : ℕ}
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) (rho t : Fin r → ℝ)
    (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) (hB : ∀ q, B q x ≤ t q) :
    (∑ j, x j) ≤ ∑ q, rho q * t q := by
  calc
    (∑ j, x j) ≤ ∑ j, (∑ q, rho q * B q (Pi.single j (1 : ℝ))) * x j := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcover j) (hx j)
    _ = ∑ q, rho q * B q x := (weighted_expansion B rho x).symm
    _ ≤ ∑ q, rho q * t q :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hB q) (hrho q))

/-- The auxiliary global-simplex multiplier can be absorbed into the actual
budget and nonnegativity multipliers. Coverage, not an equality, suffices. -/
theorem absorb_global_multiplier {k r : ℕ}
    (D : Fin r → Fin k → ℝ) (rho nu : Fin r → ℝ)
    (mu a : Fin k → ℝ) (eta : ℝ)
    (hrho : ∀ q, 0 ≤ rho q) (hnu : ∀ q, 0 ≤ nu q)
    (hmu : ∀ j, 0 ≤ mu j) (heta : 0 ≤ eta)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * D q j)
    (hker : ∀ j, a j + (∑ q, nu q * D q j) - mu j + eta = 0) :
    (∀ q, 0 ≤ nu q + eta * rho q) ∧
    (∀ j, 0 ≤ mu j + eta * ((∑ q, rho q * D q j) - 1)) ∧
    (∀ j, a j + (∑ q, (nu q + eta * rho q) * D q j) -
      (mu j + eta * ((∑ q, rho q * D q j) - 1)) = 0) := by
  refine ⟨fun q => add_nonneg (hnu q) (mul_nonneg heta (hrho q)), ?_, ?_⟩
  · intro j
    exact add_nonneg (hmu j) (mul_nonneg heta (sub_nonneg.mpr (hcover j)))
  · intro j
    calc
      _ = a j + (∑ q, nu q * D q j) - mu j + eta := by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        ring
      _ = 0 := hker j

/-- Full alternative with independently constrained budget rows. The coverage
certificate is finite and directly checkable. Budget right sides may be negative;
if their covered total is negative, the proof explicitly constructs a violated
nonnegative dual witness. No Farkas or feasible-allocation premise is assumed. -/
theorem alternative {m k r : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ)
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (b : Fin m → ℝ) (t : Fin r → ℝ) :
    (∃ x : Fin k → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, a i x ≤ b i) ∧ (∀ q, B q x ≤ t q)) ↔
    (∀ (w : Fin m → ℝ) (mu : Fin k → ℝ) (nu : Fin r → ℝ),
      (∀ i, 0 ≤ w i) → (∀ j, 0 ≤ mu j) → (∀ q, 0 ≤ nu q) →
      (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) +
        (∑ q, nu q * B q (Pi.single j (1 : ℝ))) - mu j = 0) →
      0 ≤ (∑ i, w i * b i) + ∑ q, nu q * t q) := by
  classical
  constructor
  · rintro ⟨x, hx, ha, hB⟩ w mu nu hw hmu hnu hker
    have hwa : (∑ i, w i * a i x) ≤ ∑ i, w i * b i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ha i) (hw i))
    have hnB : (∑ q, nu q * B q x) ≤ ∑ q, nu q * t q :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hB q) (hnu q))
    have hidentity : (∑ i, w i * a i x) + (∑ q, nu q * B q x) = ∑ j, mu j * x j := by
      rw [weighted_expansion a w x, weighted_expansion B nu x, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← add_mul, sub_eq_zero.mp (hker j)]
    have hnon : 0 ≤ ∑ j, mu j * x j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hmu j) (hx j))
    linarith
  · intro hdual
    let T : ℝ := ∑ q, rho q * t q
    have hT : 0 ≤ T := by
      have hh := hdual (fun _ => 0)
        (fun j => ∑ q, rho q * B q (Pi.single j (1 : ℝ))) rho
        (fun _ => le_rfl) (fun j => (by linarith [hcover j])) hrho
        (by intro j; simp)
      simpa only [zero_mul, Finset.sum_const_zero, zero_add] using hh
    let e := Fintype.equivFin (Fin m ⊕ Fin r)
    let a' : Fin (Fintype.card (Fin m ⊕ Fin r)) → (Fin k → ℝ) →L[ℝ] ℝ :=
      fun u => Sum.elim a B (e.symm u)
    let b' : Fin (Fintype.card (Fin m ⊕ Fin r)) → ℝ :=
      fun u => Sum.elim b t (e.symm u)
    have htest : ∀ (v : Fin (Fintype.card (Fin m ⊕ Fin r)) → ℝ)
        (mu : Fin k → ℝ) (eta : ℝ),
        (∀ u, 0 ≤ v u) → (∀ j, 0 ≤ mu j) → 0 ≤ eta →
        (∀ j, (∑ u, v u * a' u (Pi.single j (1 : ℝ))) - mu j + eta = 0) →
        0 ≤ (∑ u, v u * b' u) + eta * T := by
      intro v mu eta hv hmu heta hker
      let w : Fin m → ℝ := fun i => v (e (.inl i))
      let nu : Fin r → ℝ := fun q => v (e (.inr q))
      have hsplit (j : Fin k) :
          (∑ u, v u * a' u (Pi.single j (1 : ℝ))) =
          (∑ i, w i * a i (Pi.single j (1 : ℝ))) +
          ∑ q, nu q * B q (Pi.single j (1 : ℝ)) := by
        rw [← Equiv.sum_comp e (fun u => v u * a' u (Pi.single j (1 : ℝ)))]
        simp [a', w, nu, Fintype.sum_sum_type]
      have hker' : ∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) +
          (∑ q, nu q * B q (Pi.single j (1 : ℝ))) - mu j + eta = 0 := by
        intro j
        simpa only [hsplit j] using hker j
      have habs := absorb_global_multiplier
        (fun q j => B q (Pi.single j (1 : ℝ))) rho nu mu
        (fun j => ∑ i, w i * a i (Pi.single j (1 : ℝ))) eta
        hrho (fun q => hv _) hmu heta hcover hker'
      have hh := hdual w
        (fun j => mu j + eta * ((∑ q, rho q * B q (Pi.single j (1 : ℝ))) - 1))
        (fun q => nu q + eta * rho q) (fun i => hv _) habs.2.1 habs.1 habs.2.2
      have hb' : (∑ u, v u * b' u) = (∑ i, w i * b i) + ∑ q, nu q * t q := by
        rw [← Equiv.sum_comp e (fun u => v u * b' u)]
        simp [b', w, nu, Fintype.sum_sum_type]
      rw [hb']
      have heq : (∑ q, (nu q + eta * rho q) * t q) =
          (∑ q, nu q * t q) + eta * T := by
        simp only [T, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
      rw [heq] at hh
      linarith
    obtain ⟨x, hx, hrows⟩ := (allocation_alternative a' b' T hT).mpr htest
    refine ⟨x, hx.1, ?_, ?_⟩
    · intro i
      simpa [a', b'] using hrows (e (.inl i))
    · intro q
      simpa [a', b'] using hrows (e (.inr q))

end Hirsch.CoveringAllocation


namespace Hirsch.CheckedCovering
open Hirsch.CheckedCatalogue Hirsch.FiniteAllocation

/-- Bind the rational matrix to all actual rows, allowing any finite row order. -/
lemma encoded_kernel {m k r n : ℕ}
    (e : (Fin m ⊕ (Fin k ⊕ Fin r)) ≃ Fin n) (M : QMatrix n k)
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ)
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (ha : ∀ i j, (M j (e (.inl i)) : ℝ) = a i (Pi.single j (1 : ℝ)))
    (hneg : ∀ i j, (M j (e (.inr (.inl i))) : ℝ) = if i = j then -1 else 0)
    (hB : ∀ q j, (M j (e (.inr (.inr q))) : ℝ) = B q (Pi.single j (1 : ℝ)))
    (v : Fin n → ℝ) :
    rowMap n k M v = 0 ↔
      ∀ j, (∑ i, v (e (.inl i)) * a i (Pi.single j (1 : ℝ))) +
        (∑ q, v (e (.inr (.inr q))) * B q (Pi.single j (1 : ℝ))) -
          v (e (.inr (.inl j))) = 0 := by
  classical
  have hexp (j : Fin k) : rowMap n k M v j =
      (∑ i, v (e (.inl i)) * a i (Pi.single j (1 : ℝ))) +
      (∑ q, v (e (.inr (.inr q))) * B q (Pi.single j (1 : ℝ))) -
        v (e (.inr (.inl j))) := by
    change (∑ i, (M j i : ℝ) * v i) = _
    rw [← Equiv.sum_comp e (fun i => (M j i : ℝ) * v i)]
    simp [Fintype.sum_sum_type, ha, hneg, hB, ite_mul, mul_comm,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  constructor
  · intro hv j
    rw [← hexp j]
    exact congrFun hv j
  · intro hv
    funext j
    exact (hexp j).trans (hv j)

def testForm {m k r n : ℕ} (e : (Fin m ⊕ (Fin k ⊕ Fin r)) ≃ Fin n)
    (b : Fin m → ℝ) (t : Fin r → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := (∑ i, v (e (.inl i)) * b i) + ∑ q, v (e (.inr (.inr q))) * t q
  map_add' u v := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]
    ring

/-- The ACTUAL emitted catalogue is equivalent to simultaneous covering allocation.
Neither a Farkas theorem nor semantic completeness is an input. -/
theorem checked_allocation {m k r n : ℕ}
    (e : (Fin m ⊕ (Fin k ⊕ Fin r)) ≃ Fin n) (M : QMatrix n k)
    (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ) (hcheck : check n k M tag L z = true)
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ)
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (ha : ∀ i j, (M j (e (.inl i)) : ℝ) = a i (Pi.single j (1 : ℝ)))
    (hneg : ∀ i j, (M j (e (.inr (.inl i))) : ℝ) = if i = j then -1 else 0)
    (hB : ∀ q j, (M j (e (.inr (.inr q))) : ℝ) = B q (Pi.single j (1 : ℝ)))
    (b : Fin m → ℝ) (t : Fin r → ℝ) :
    (∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∀ i, a i θ ≤ b i) ∧
      (∀ q, B q θ ≤ t q)) ↔
    ∀ c ∈ catalogue n k M tag L,
      0 ≤ (∑ i, (c (e (.inl i)) : ℝ) * b i) +
        ∑ q, (c (e (.inr (.inr q))) : ℝ) * t q := by
  classical
  rw [Hirsch.CoveringAllocation.alternative a B rho hrho hcover b t]
  constructor
  · intro h c hc
    have hv := (checked_exact n k M tag L z hcheck (fun i => (c i : ℝ))).mpr
      ⟨c, hc, rfl⟩
    exact h (fun i => (c (e (.inl i)) : ℝ))
      (fun j => (c (e (.inr (.inl j))) : ℝ))
      (fun q => (c (e (.inr (.inr q))) : ℝ))
      (fun i => hv.1 _) (fun j => hv.1 _) (fun q => hv.1 _)
      ((encoded_kernel e M a B ha hneg hB _).mp hv.2.1)
  · intro h w mu nu hw hmu hnu hker
    let v : Fin n → ℝ := fun j => Sum.elim w (Sum.elim mu nu) (e.symm j)
    have hv : ∀ j, 0 ≤ v j := by
      intro j
      dsimp only [v]
      cases e.symm j with
      | inl i => exact hw i
      | inr u => cases u with
        | inl i => exact hmu i
        | inr q => exact hnu q
    have hvA : rowMap n k M v = 0 := by
      apply (encoded_kernel e M a B ha hneg hB v).mpr
      intro j
      simpa [v] using hker j
    have hf := (checked_linear_tests n k M tag L z hcheck (testForm e b t)).mpr h
    have hh := hf v hv hvA
    simpa [testForm, v] using hh

/-- Finite budget-row domination proves support on the entire allocated shape. -/
lemma support_from_budget
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m k r : ℕ}
    (a : Fin m → E →L[ℝ] ℝ) (G : (Fin k → ℝ) →L[ℝ] E)
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) (t : Fin r → ℝ)
    (h : Fin m → ℝ) (eta : Fin m → Fin r → ℝ)
    (heta : ∀ i q, 0 ≤ eta i q)
    (hdom : ∀ i j, a i (G (Pi.single j (1 : ℝ))) ≤
      ∑ q, eta i q * B q (Pi.single j (1 : ℝ)))
    (hcap : ∀ i, (∑ q, eta i q * t q) ≤ h i)
    (θ : Fin k → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hBθ : ∀ q, B q θ ≤ t q) :
    ∀ i, a i (G θ) ≤ h i := by
  intro i
  calc
    a i (G θ) = ∑ j, a i (G (Pi.single j (1 : ℝ))) * θ j :=
      row_expansion ((a i).comp G) θ
    _ ≤ ∑ j, (∑ q, eta i q * B q (Pi.single j (1 : ℝ))) * θ j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hdom i j) (hθ j))
    _ = ∑ q, eta i q * B q θ := (weighted_expansion B (eta i) θ).symm
    _ ≤ ∑ q, eta i q * t q :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hBθ q) (heta i q))
    _ ≤ h i := hcap i

/-- Whole-set equality uses the checked output and actual budget rows. -/
theorem checked_minkowski
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m k r n : ℕ) (e : (Fin m ⊕ (Fin k ⊕ Fin r)) ≃ Fin n)
    (a : Fin m → E →L[ℝ] ℝ) (G : (Fin k → ℝ) →L[ℝ] E)
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (M : QMatrix n k) (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ) (hcheck : check n k M tag L z = true)
    (ha : ∀ i j, (M j (e (.inl i)) : ℝ) = -a i (G (Pi.single j (1 : ℝ))))
    (hneg : ∀ i j, (M j (e (.inr (.inl i))) : ℝ) = if i = j then -1 else 0)
    (hB : ∀ q j, (M j (e (.inr (.inr q))) : ℝ) = B q (Pi.single j (1 : ℝ)))
    (b h : Fin m → ℝ) (t : Fin r → ℝ)
    (hsupport : ∀ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) → (∀ q, B q θ ≤ t q) →
      ∀ i, a i (G θ) ≤ h i) :
    ({x : E | ∀ i, a i x ≤ b i} =
      {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
        ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∀ q, B q θ ≤ t q) ∧ p + G θ = x}) ↔
    ∀ x : E, (∀ i, a i x ≤ b i) → ∀ c ∈ catalogue n k M tag L,
      0 ≤ (∑ i, (c (e (.inl i)) : ℝ) * (b i - a i x - h i)) +
        ∑ q, (c (e (.inr (.inr q))) : ℝ) * t q := by
  have halloc (x : E) := checked_allocation e M tag L z hcheck
    (fun i => -(a i).comp G) B rho hrho hcover ha hneg hB
    (fun i => b i - a i x - h i) t
  constructor
  · intro heq x hx
    have hx' : x ∈ {x : E | ∃ p : E, (∀ i, a i p ≤ b i - h i) ∧
        ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∀ q, B q θ ≤ t q) ∧ p + G θ = x} := heq ▸ hx
    obtain ⟨p, hp, θ, hθ, hBθ, hpθ⟩ := hx'
    apply (halloc x).mp
    refine ⟨θ, hθ, ?_, hBθ⟩
    intro i
    change -a i (G θ) ≤ b i - a i x - h i
    have he : a i p + a i (G θ) = a i x := by
      simpa only [map_add] using congrArg (a i) hpθ
    linarith [hp i]
  · intro htests
    apply Set.ext
    intro x
    constructor
    · intro hx
      obtain ⟨θ, hθ, hrows, hBθ⟩ := (halloc x).mpr (htests x hx)
      refine ⟨x - G θ, ?_, θ, hθ, hBθ, ?_⟩
      · intro i
        have hh := hrows i
        change -a i (G θ) ≤ b i - a i x - h i at hh
        rw [map_sub]
        linarith
      · abel
    · rintro ⟨p, hp, θ, hθ, hBθ, rfl⟩
      intro i
      rw [map_add]
      linarith [hp i, hsupport θ hθ hBθ i]

/-- Finite objective coefficient identities and sharp witnesses yield the exact
scalar region. No pointwise criterion or universal candidate support is assumed. -/
theorem checked_support_budgets
    (d m k r n : ℕ) (e : (Fin m ⊕ (Fin k ⊕ Fin r)) ≃ Fin n)
    (a : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] (Fin d → ℝ))
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (M : QMatrix n k) (tag : Finset (Fin n) → Bool) (L : LeftData n k)
    (z : Finset (Fin n) → Fin n → ℚ) (hcheck : check n k M tag L z = true)
    (ha : ∀ i j, (M j (e (.inl i)) : ℝ) = -a i (G (Pi.single j (1 : ℝ))))
    (hneg : ∀ i j, (M j (e (.inr (.inl i))) : ℝ) = if i = j then -1 else 0)
    (hB : ∀ q j, (M j (e (.inr (.inr q))) : ℝ) = B q (Pi.single j (1 : ℝ)))
    (b h : Fin m → ℝ) (t : Fin r → ℝ)
    (eta : Fin m → Fin r → ℝ) (heta : ∀ i q, 0 ≤ eta i q)
    (hdom : ∀ i j, a i (G (Pi.single j (1 : ℝ))) ≤
      ∑ q, eta i q * B q (Pi.single j (1 : ℝ)))
    (hcap : ∀ i, (∑ q, eta i q * t q) ≤ h i)
    (alpha : (Fin n → ℚ) → Fin m → ℝ) (xstar : (Fin n → ℚ) → Fin d → ℝ)
    (halpha : ∀ c ∈ catalogue n k M tag L, ∀ i, 0 ≤ alpha c i)
    (hxstar : ∀ c ∈ catalogue n k M tag L, ∀ i, a i (xstar c) ≤ b i)
    (hforms : ∀ c ∈ catalogue n k M tag L, ∀ j,
      (∑ i, (c (e (.inl i)) : ℝ) * a i (Pi.single j (1 : ℝ))) =
        ∑ i, alpha c i * a i (Pi.single j (1 : ℝ)))
    (hcomp : ∀ c ∈ catalogue n k M tag L, ∀ i,
      alpha c i * (b i - a i (xstar c)) = 0) :
    ({x : Fin d → ℝ | ∀ i, a i x ≤ b i} =
      {x : Fin d → ℝ | ∃ p : Fin d → ℝ, (∀ i, a i p ≤ b i - h i) ∧
        ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∀ q, B q θ ≤ t q) ∧ p + G θ = x}) ↔
    ∀ c ∈ catalogue n k M tag L,
      (∑ i, (c (e (.inl i)) : ℝ) * h i) -
        (∑ q, (c (e (.inr (.inr q))) : ℝ) * t q) ≤
          (∑ i, (c (e (.inl i)) : ℝ) * b i) - ∑ i, alpha c i * b i := by
  have hsupport := support_from_budget a G B t h eta heta hdom hcap
  rw [checked_minkowski m k r n e a G B rho hrho hcover M tag L z hcheck
    ha hneg hB b h t hsupport]
  have hforms' (c : Fin n → ℚ) (hc : c ∈ catalogue n k M tag L) (x : Fin d → ℝ) :
      (∑ i, (c (e (.inl i)) : ℝ) * a i x) = ∑ i, alpha c i * a i x := by
    rw [weighted_expansion a (fun i => (c (e (.inl i)) : ℝ)) x,
      weighted_expansion a (alpha c) x]
    apply Finset.sum_congr rfl
    intro j _
    rw [hforms c hc j]
  constructor
  · intro hall c hc
    have hstar : (∑ i, alpha c i * a i (xstar c)) = ∑ i, alpha c i * b i := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := hcomp c hc i
      nlinarith
    have hs := hall (xstar c) (hxstar c hc) c hc
    have hf := hforms' c hc (xstar c)
    simp only [mul_sub, Finset.sum_sub_distrib] at hs
    linarith
  · intro hscalar x hx c hc
    have hupper : (∑ i, alpha c i * a i x) ≤ ∑ i, alpha c i * b i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (halpha c hc i))
    have hf := hforms' c hc x
    have hs := hscalar c hc
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith

end Hirsch.CheckedCovering

/-- A passing concrete rational circuit audit and finite primal/dual support
certificates decide whole-set Minkowski reconstruction for covering budgets.
No catalogue-completeness, Farkas, or pointwise-equivalence premise is assumed.
-/
theorem solution
    (d m k r n : ℕ) (e : (Fin m ⊕ (Fin k ⊕ Fin r)) ≃ Fin n)
    (a : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] (Fin d → ℝ))
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (M : Fin k → Fin n → ℚ) (tag : Finset (Fin n) → Bool)
    (L : Finset (Fin n) → Fin n → Option (Fin k) → ℚ)
    (z : Finset (Fin n) → Fin n → ℚ)
    (ha : ∀ i j, (M j (e (.inl i)) : ℝ) = -a i (G (Pi.single j (1 : ℝ))))
    (hneg : ∀ i j, (M j (e (.inr (.inl i))) : ℝ) = if i = j then -1 else 0)
    (hB : ∀ q j, (M j (e (.inr (.inr q))) : ℝ) = B q (Pi.single j (1 : ℝ)))
    (b h : Fin m → ℝ) (t : Fin r → ℝ)
    (eta : Fin m → Fin r → ℝ) (heta : ∀ i q, 0 ≤ eta i q)
    (hdom : ∀ i j, a i (G (Pi.single j (1 : ℝ))) ≤
      ∑ q, eta i q * B q (Pi.single j (1 : ℝ)))
    (hcap : ∀ i, (∑ q, eta i q * t q) ≤ h i)
    (alpha : (Fin n → ℚ) → Fin m → ℝ) (xstar : (Fin n → ℚ) → Fin d → ℝ) :
    let U := (Finset.range (k + 2)).biUnion
      (fun s => (Finset.univ : Finset (Fin n)).powersetCard s)
    let v : Finset (Fin n) → Fin n → ℚ := fun s i => if i ∈ s then L s i none else 0
    let C := (U.filter (fun s => tag s = false ∧ (∀ i ∈ s, 0 < L s i none) ∧
      (∀ j, (∑ i, M j i * v s i) = 0) ∧ (∑ i, v s i) = 1)).image v
    decide (∀ s ∈ U, if tag s then
        (∃ i, z s i ≠ 0) ∧ (∀ i, i ∉ s → z s i = 0) ∧
          (∀ j, (∑ i, M j i * z s i) = 0) ∧ (∑ i, z s i) = 0
      else ∀ i ∈ s, ∀ j ∈ s,
        (∑ q, L s i (some q) * M q j) + L s i none = if i = j then 1 else 0) = true →
    (∀ c ∈ C, ∀ i, 0 ≤ alpha c i) →
    (∀ c ∈ C, ∀ i, a i (xstar c) ≤ b i) →
    (∀ c ∈ C, ∀ j,
      (∑ i, (c (e (.inl i)) : ℝ) * a i (Pi.single j (1 : ℝ))) =
        ∑ i, alpha c i * a i (Pi.single j (1 : ℝ))) →
    (∀ c ∈ C, ∀ i, alpha c i * (b i - a i (xstar c)) = 0) →
    (({x : Fin d → ℝ | ∀ i, a i x ≤ b i} =
      {x : Fin d → ℝ | ∃ p : Fin d → ℝ, (∀ i, a i p ≤ b i - h i) ∧
        ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∀ q, B q θ ≤ t q) ∧ p + G θ = x}) ↔
    ∀ c ∈ C,
      (∑ i, (c (e (.inl i)) : ℝ) * h i) -
        (∑ q, (c (e (.inr (.inr q))) : ℝ) * t q) ≤
          (∑ i, (c (e (.inl i)) : ℝ) * b i) - ∑ i, alpha c i * b i) := by
  dsimp only
  intro hcheck halpha hxstar hforms hcomp
  exact Hirsch.CheckedCovering.checked_support_budgets d m k r n e a G B rho hrho hcover
    M tag L z hcheck ha hneg hB b h t eta heta hdom hcap alpha xstar
    halpha hxstar hforms hcomp

#print axioms Hirsch.CheckedCovering.encoded_kernel
#print axioms Hirsch.CheckedCovering.checked_allocation
#print axioms Hirsch.CheckedCovering.support_from_budget
#print axioms Hirsch.CheckedCovering.checked_minkowski
#print axioms Hirsch.CheckedCovering.checked_support_budgets
#print axioms solution
