-- Prove2me | solution 1 for Hirsch.checked_rational_circuit_catalogue_exact
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T22:09:50.356973+00:00
-- url     : https://prove2.me/submissions/0dcf5eea-df74-4295-9a5e-c71edb96589d

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

/-- A passing finite rational audit certifies the COMPLETE normalized positive
circuit catalogue, even for real null vectors. All support decisions are backed
by finite identities; no RREF, rank-oracle, enumeration or completeness premise.
The exact Boolean checker is evaluated over the original rational coefficients.
-/
theorem solution (n k : ℕ) (A : Fin k → Fin n → ℚ)
    (tag : Finset (Fin n) → Bool)
    (L : Finset (Fin n) → Fin n → Option (Fin k) → ℚ)
    (z : Finset (Fin n) → Fin n → ℚ) :
    let U := (Finset.range (k + 2)).biUnion
      (fun r => (Finset.univ : Finset (Fin n)).powersetCard r)
    let c : Finset (Fin n) → Fin n → ℚ := fun s i => if i ∈ s then L s i none else 0
    decide (∀ s ∈ U, if tag s then
        (∃ i, z s i ≠ 0) ∧ (∀ i, i ∉ s → z s i = 0) ∧
          (∀ r, (∑ i, A r i * z s i) = 0) ∧ (∑ i, z s i) = 0
      else ∀ i ∈ s, ∀ j ∈ s,
        (∑ r, L s i (some r) * A r j) + L s i none = if i = j then 1 else 0) = true →
    ∀ x : Fin n → ℝ,
      ((∀ i, 0 ≤ x i) ∧ (∀ r, (∑ i, (A r i : ℝ) * x i) = 0) ∧
        (∑ i, x i) = 1 ∧
        ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) →
          (∀ r, (∑ i, (A r i : ℝ) * y i) = 0) → y ≠ 0 →
          Function.support y ⊆ Function.support x → Function.support x ⊆ Function.support y) ↔
      ∃ q ∈ (U.filter (fun s => tag s = false ∧ (∀ i ∈ s, 0 < L s i none) ∧
        (∀ r, (∑ i, A r i * c s i) = 0) ∧ (∑ i, c s i) = 1)).image c,
        x = fun i => (q i : ℝ) := by
  dsimp only
  intro hcheck x
  have h := Hirsch.CheckedCatalogue.checked_exact n k A tag L z hcheck x
  have hn (v : Fin n → ℝ) : Hirsch.CheckedCatalogue.rowMap n k A v = 0 ↔
      ∀ r, (∑ i, (A r i : ℝ) * v i) = 0 := by
    constructor
    · intro hv r
      exact congrFun hv r
    · intro hv
      funext r
      exact hv r
  simpa only [hn] using h

#print axioms Hirsch.CheckedCatalogue.emitted_minimal
#print axioms Hirsch.CheckedCatalogue.table_complete
#print axioms Hirsch.CheckedCatalogue.checked_exact
#print axioms solution

-- Kernel-evaluated concrete positive and negative audit examples.
namespace Hirsch.CheckedCatalogue.KernelSmoke
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def A : Fin 1 → Fin 4 → ℚ := fun _ => ![1, 1, -1, 0]
def tag (s : Finset (Fin 4)) : Bool :=
  if s = ({0, 1} : Finset (Fin 4)) then true else false
def z (s : Finset (Fin 4)) (i : Fin 4) : ℚ :=
  if s = ({0, 1} : Finset (Fin 4)) then ![(-1 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)] i else
  0
def L (s : Finset (Fin 4)) (i : Fin 4) (r : Option (Fin 1)) : ℚ :=
  if s = ({0} : Finset (Fin 4)) then
    match r with | none => ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] i | some _ => ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] i
  else
  if s = ({1} : Finset (Fin 4)) then
    match r with | none => ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] i | some _ => ![(0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)] i
  else
  if s = ({2} : Finset (Fin 4)) then
    match r with | none => ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] i | some _ => ![(0 : ℚ), (0 : ℚ), (-1 : ℚ), (0 : ℚ)] i
  else
  if s = ({3} : Finset (Fin 4)) then
    match r with | none => ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)] i | some _ => ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)] i
  else
  if s = ({0, 2} : Finset (Fin 4)) then
    match r with | none => ![((1 : ℚ) / 2), (0 : ℚ), ((1 : ℚ) / 2), (0 : ℚ)] i | some _ => ![((1 : ℚ) / 2), (0 : ℚ), ((-1 : ℚ) / 2), (0 : ℚ)] i
  else
  if s = ({0, 3} : Finset (Fin 4)) then
    match r with | none => ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)] i | some _ => ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (-1 : ℚ)] i
  else
  if s = ({1, 2} : Finset (Fin 4)) then
    match r with | none => ![(0 : ℚ), ((1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)] i | some _ => ![(0 : ℚ), ((1 : ℚ) / 2), ((-1 : ℚ) / 2), (0 : ℚ)] i
  else
  if s = ({1, 3} : Finset (Fin 4)) then
    match r with | none => ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)] i | some _ => ![(0 : ℚ), (1 : ℚ), (0 : ℚ), (-1 : ℚ)] i
  else
  if s = ({2, 3} : Finset (Fin 4)) then
    match r with | none => ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)] i | some _ => ![(0 : ℚ), (0 : ℚ), (-1 : ℚ), (1 : ℚ)] i
  else
  0

example : check 4 1 A tag L z = true := by decide +kernel
example : (catalogue 4 1 A tag L).card = 3 := by decide +kernel
example : check 4 1 A (fun _ => false) (fun _ _ _ => 0) (fun _ _ => 0) = false := by decide +kernel
end Hirsch.CheckedCatalogue.KernelSmoke
