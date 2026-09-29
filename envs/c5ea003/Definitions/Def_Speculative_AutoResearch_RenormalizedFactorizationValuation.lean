-- Prove2me | Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
-- name    : Speculative_AutoResearch_RenormalizedFactorizationValuation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:40.006701+00:00
-- url     : https://prove2.me/theorems/03569c4f-ff4b-42ea-8404-46d2c7b879e5
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_RenormalizedFactorizationValuation
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.RenormalizedFactorizationValuation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/RenormalizedFactorizationValuation.lean by skeleton subtraction
import Mathlib
/-
# Renormalized factorization over an arbitrary discretely valued group (Cycle 4)

This file closes two of the open conjectures listed in `FUTURE_DIRECTIONS.md` for the
Conjecture-C thread of `Catalog/Probability/RenormalizedNormalizedFactorization.lean`:

* **C4 (transfer to other valued fields).**  Nothing in the Laurent-series proof uses the
  coefficientwise structure of `LaurentSeries K`.  All that is needed is a commutative group
  `G` (the group of units of the field), a homomorphism `val : G → ℤ`, and a uniformizer
  `π` with `val π = 1`.  This is packaged as `DiscreteVal G`.  In this generality:
  `realizable_iff` — for every `m ≥ 1`, every integer exponent `k` and every pole profile
  `d`, the set of `π ^ k * ∏_{i < m} f i` with `val (f i) = d i` is exactly the level set
  `{g | val g = k + ∑_{i<m} d i}`.
* **C1 (rigidity index).**  The fibre of the renormalized-product map over a realizable `g`
  is a torsor under the group of "twists" (`fibreEquivTwist`), and that twist group is in
  bijection with `Fin (m-1)` copies of the valuation-zero subgroup (`twistEquivPi`).  Hence
  `card_factorizations`: the fibre has exactly `#{u | val u = 0} ^ (m-1)` elements — the
  rigidity index is `m - 1`, so the fibre is a singleton **iff** `m = 1`
  (`rigidity_dichotomy`).

The two instantiations proved at the end are genuinely different worlds:

* `laurentVal K` — the Laurent series field `LaurentSeries K` over any field `K`, recovering
  the results of the companion file;
* `padicVal p` — the `p`-adic numbers `ℚ_[p]`, where the same dichotomy is new.

No `sorry`, no `native_decide`, no new axioms.
-/

namespace Catalog.Probability.RenormalizedFactorizationValuation

open Finset

variable {G : Type*} [CommGroup G]

/-! ## The abstract setting: a `ℤ`-valued valuation with a uniformizer -/

/-- A `ℤ`-valued *discrete valuation datum* on a commutative group `G`: a homomorphism
`val : G → ℤ` together with a uniformizer of value `1` (so `val` is surjective).  For a
discretely valued field one takes `G = Fˣ`. -/
structure DiscreteVal (G : Type*) [CommGroup G] where
  /-- The valuation. -/
  val : G → ℤ
  /-- The valuation is a homomorphism. -/
  val_mul : ∀ a b, val (a * b) = val a + val b
  /-- A chosen element of valuation `1`. -/
  uniformizer : G
  /-- The uniformizer has valuation `1`. -/
  val_uniformizer : val uniformizer = 1

namespace DiscreteVal

variable (V : DiscreteVal G)

@[simp] lemma val_one : V.val 1 = 0 := by
  have := V.val_mul 1 1
  simp at this
  omega

@[simp] lemma val_inv (a : G) : V.val a⁻¹ = -V.val a := by
  have := V.val_mul a a⁻¹
  rw [mul_inv_cancel, V.val_one] at this
  omega

lemma val_div (a b : G) : V.val (a / b) = V.val a - V.val b := by
  rw [div_eq_mul_inv, V.val_mul, V.val_inv]; ring



lemma val_prod {ι : Type*} (s : Finset ι) (f : ι → G) :
    V.val (∏ i ∈ s, f i) = ∑ i ∈ s, V.val (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, V.val_mul, ih, Finset.sum_insert ha]


/-! ## Renormalized products and their fibres -/

/-- The renormalized product `π ^ k * ∏_{i < m} f i`. -/
def renormProd (V : DiscreteVal G) (k : ℤ) (m : ℕ) (f : ℕ → G) : G :=
  V.uniformizer ^ k * ∏ i ∈ range m, f i

/-- `f` realizes the pole profile `d` on the window `[0, m)`, and is trivial outside it. -/
def HasProfile (V : DiscreteVal G) (m : ℕ) (d : ℕ → ℤ) (f : ℕ → G) : Prop :=
  (∀ i < m, V.val (f i) = d i) ∧ ∀ i, m ≤ i → f i = 1

/-- The fibre of the renormalized-product map: all profile-`d` families whose renormalized
product is `g`. -/
def factorizations (V : DiscreteVal G) (k : ℤ) (m : ℕ) (d : ℕ → ℤ) (g : G) : Set (ℕ → G) :=
  {f | HasProfile V m d f ∧ renormProd V k m f = g}


/-- The canonical factorization: the slots `1, …, m-1` carry pure powers of the uniformizer
and slot `0` absorbs the whole discrepancy. -/
def canonFam (V : DiscreteVal G) (k : ℤ) (m : ℕ) (d : ℕ → ℤ) (g : G) : ℕ → G :=
  fun i => (if i = 0 then V.uniformizer ^ (-(k + ∑ j ∈ range m, d j)) * g else 1) *
      (if i < m then V.uniformizer ^ (d i) else 1)





/-! ## The fibre is a torsor under the twist group -/

/-- The group of *twists*: families of valuation-`0` elements supported on `[0, m)` whose
product is `1`. -/
def twistGroup (V : DiscreteVal G) (m : ℕ) : Set (ℕ → G) :=
  {u | (∀ i < m, V.val (u i) = 0) ∧ (∀ i, m ≤ i → u i = 1) ∧ ∏ i ∈ range m, u i = 1}

/-- **Fibre = torsor.**  Once one factorization `f₀` of `g` is fixed, the whole fibre is in
bijection with the twist group, via `f ↦ f / f₀`. -/
def fibreEquivTwist (V : DiscreteVal G) (k : ℤ) (m : ℕ) (d : ℕ → ℤ) (g : G)
    (f₀ : ℕ → G) (hf₀ : f₀ ∈ factorizations V k m d g) :
    factorizations V k m d g ≃ twistGroup V m where
  toFun f := by
    refine ⟨fun i => (f : ℕ → G) i / f₀ i, ?_, ?_, ?_⟩
    · intro i hi
      show V.val ((f : ℕ → G) i / f₀ i) = 0
      rw [V.val_div, f.2.1.1 i hi, hf₀.1.1 i hi, sub_self]
    · intro i hi
      show (f : ℕ → G) i / f₀ i = 1
      rw [f.2.1.2 i hi, hf₀.1.2 i hi, div_self']
    · rw [Finset.prod_div_distrib]
      have h : V.uniformizer ^ k * ∏ i ∈ range m, (f : ℕ → G) i
          = V.uniformizer ^ k * ∏ i ∈ range m, f₀ i := by
        rw [← renormProd, ← renormProd, f.2.2, hf₀.2]
      rw [mul_left_cancel h, div_self']
  invFun u := by
    refine ⟨fun i => f₀ i * (u : ℕ → G) i, ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      show V.val (f₀ i * (u : ℕ → G) i) = d i
      rw [V.val_mul, hf₀.1.1 i hi, u.2.1 i hi, add_zero]
    · intro i hi
      show f₀ i * (u : ℕ → G) i = 1
      rw [hf₀.1.2 i hi, u.2.2.1 i hi, mul_one]
    · rw [renormProd, Finset.prod_mul_distrib, u.2.2.2, mul_one, ← renormProd, hf₀.2]
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    simp
  right_inv := by
    intro u
    apply Subtype.ext
    funext i
    simp

/-! ## Rigidity: the fibre is a singleton exactly when `m = 1` -/


/-- The explicit twist supported on the two slots `0` and `1`. -/
def twoSlotTwist (u : G) : ℕ → G := fun i => if i = 0 then u else if i = 1 then u⁻¹ else 1




/-! ## The rigidity index: the fibre has `#{val = 0} ^ (m-1)` elements -/

/-- The twist family determined by `n` free valuation-zero elements: slot `i+1` carries the
`i`-th datum and slot `0` is forced to be the inverse of their product. -/
def piToFam (V : DiscreteVal G) (n : ℕ) (w : Fin n → {u : G // V.val u = 0}) : ℕ → G :=
  fun i => if i = 0 then (∏ j : Fin n, (w j : G))⁻¹
    else if h : i - 1 < n then (w ⟨i - 1, h⟩ : G) else 1

@[simp] lemma piToFam_zero (n : ℕ) (w : Fin n → {u : G // V.val u = 0}) :
    piToFam V n w 0 = (∏ j : Fin n, (w j : G))⁻¹ := by
  simp [piToFam]

lemma piToFam_succ (n : ℕ) (w : Fin n → {u : G // V.val u = 0}) (i : ℕ) :
    piToFam V n w (i + 1) = if h : i < n then (w ⟨i, h⟩ : G) else 1 := by
  simp [piToFam]

lemma val_prod_coe (n : ℕ) (w : Fin n → {u : G // V.val u = 0}) :
    V.val (∏ j : Fin n, (w j : G)) = 0 := by
  rw [V.val_prod]
  exact Finset.sum_eq_zero fun j _ => (w j).2

lemma piToFam_mem (n : ℕ) (w : Fin n → {u : G // V.val u = 0}) :
    piToFam V n w ∈ twistGroup V (n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [piToFam_zero, V.val_inv, V.val_prod_coe, neg_zero]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [piToFam_succ]
      by_cases h : j < n
      · rw [dif_pos h]; exact (w ⟨j, h⟩).2
      · rw [dif_neg h]; exact V.val_one
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [piToFam_succ, dif_neg (by omega : ¬j < n)]
  · rw [Finset.prod_range_succ' (fun i => piToFam V n w i) n, piToFam_zero]
    have hshift : ∀ i ∈ range n, piToFam V n w (i + 1)
        = (fun i : ℕ => if h : i < n then (w ⟨i, h⟩ : G) else 1) i := fun i _ => piToFam_succ V n w i
    rw [Finset.prod_congr rfl hshift]
    have hfin : ∏ i ∈ range n, (fun i : ℕ => if h : i < n then (w ⟨i, h⟩ : G) else 1) i
        = ∏ j : Fin n, (w j : G) := by
      rw [← Fin.prod_univ_eq_prod_range (fun i : ℕ => if h : i < n then (w ⟨i, h⟩ : G) else 1) n]
      exact Finset.prod_congr rfl fun j _ => by simp
    rw [hfin, mul_inv_cancel]

/-- The twist group on `m = n + 1` slots is a free choice of `n` valuation-zero elements: the
zeroth slot is determined by the product condition.  This is the "rigidity index `m - 1`". -/
def twistEquivPi (V : DiscreteVal G) (n : ℕ) :
    twistGroup V (n + 1) ≃ (Fin n → {u : G // V.val u = 0}) where
  toFun u := fun j => ⟨(u : ℕ → G) (j + 1), u.2.1 (j + 1) (by omega)⟩
  invFun w := ⟨piToFam V n w, V.piToFam_mem n w⟩
  left_inv := by
    intro u
    apply Subtype.ext
    funext i
    simp only [piToFam]
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have hprod : (∏ j : Fin n, (u : ℕ → G) (j + 1)) = ∏ i ∈ range n, (u : ℕ → G) (i + 1) :=
        Fin.prod_univ_eq_prod_range (fun i : ℕ => (u : ℕ → G) (i + 1)) n
      have hone : (∏ i ∈ range n, (u : ℕ → G) (i + 1)) * (u : ℕ → G) 0 = 1 := by
        rw [← Finset.prod_range_succ' (fun i => (u : ℕ → G) i) n]
        exact u.2.2.2
      rw [if_pos rfl, hprod, eq_inv_of_mul_eq_one_left hone, inv_inv]
    · rw [if_neg (by omega : ¬i = 0)]
      by_cases h : i - 1 < n
      · rw [dif_pos h]
        exact congrArg (fun t : ℕ => (u : ℕ → G) t) (by omega : i - 1 + 1 = i)
      · rw [dif_neg h]
        exact (u.2.2.1 i (by omega)).symm
  right_inv := by
    intro w
    funext j
    apply Subtype.ext
    simp only [piToFam]
    rw [if_neg (by omega : ¬(j : ℕ) + 1 = 0), dif_pos (by omega : (j : ℕ) + 1 - 1 < n)]
    exact congrArg (fun t : Fin n => ((w t : {x : G // V.val x = 0}) : G)) (Fin.ext (by simp))


end DiscreteVal

/-! ## Instantiation 1: Laurent series -/

open HahnSeries

/-- The `q`-adic valuation datum on the unit group of the Laurent series field. -/
noncomputable def laurentVal (K : Type*) [Field K] : DiscreteVal (LaurentSeries K)ˣ where
  val u := ((u : LaurentSeries K)).order
  val_mul a b := by
    simp only [Units.val_mul]
    exact HahnSeries.order_mul (x := (a : LaurentSeries K)) (y := (b : LaurentSeries K))
      (Units.ne_zero a) (Units.ne_zero b)
  uniformizer := Units.mk0 (HahnSeries.single (1 : ℤ) (1 : K)) (by simp)
  val_uniformizer := by
    simp [HahnSeries.order_single (one_ne_zero : (1 : K) ≠ 0)]



/-! ## Instantiation 2: the `p`-adic numbers -/

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-adic valuation datum on `ℚ_[p]ˣ`. -/
noncomputable def padicVal : DiscreteVal (ℚ_[p])ˣ where
  val u := Padic.valuation (p := p) (u : ℚ_[p])
  val_mul a b := by
    simp only [Units.val_mul]
    exact Padic.valuation_mul (p := p) (Units.ne_zero a) (Units.ne_zero b)
  uniformizer := Units.mk0 (p : ℚ_[p]) (by
    exact_mod_cast (Nat.cast_ne_zero (R := ℚ_[p])).mpr hp.out.ne_zero)
  val_uniformizer := Padic.valuation_p (p := p)



end Catalog.Probability.RenormalizedFactorizationValuation


