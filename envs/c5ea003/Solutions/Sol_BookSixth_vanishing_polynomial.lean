-- Prove2me | solution 1 for BookSixth.vanishing_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T00:45:55.656865+00:00
-- url     : https://prove2.me/submissions/c10b7387-0465-442a-9f3c-79c770c8bba1

import Mathlib
import Definitions.Def_BookSixth

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open BookSixth

namespace BookFix

open MvPolynomial

/-- The exponent vectors of total degree at most `d` in `n` variables. -/
def monos (n d : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.range (d + 1)).biUnion fun e => (Finset.univ : Finset (Fin n)).finsuppAntidiag e

theorem mem_monos {n d : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ monos n d ↔ ∑ i, m i ≤ d := by
  simp only [monos, Finset.mem_biUnion, Finset.mem_range, Finset.mem_finsuppAntidiag]
  constructor
  · rintro ⟨e, he, hsum, -⟩
    have hs : ∑ i, m i = e := hsum
    omega
  · intro h
    exact ⟨∑ i, m i, by omega, rfl, by simp⟩

/-- Restriction of an exponent vector on `Fin (n+1)` to its first `n` coordinates. -/
noncomputable def restr {n : ℕ} (m : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => m i.castSucc

theorem sum_eq {k : ℕ} (m : Fin k →₀ ℕ) : (m.sum fun _ e => e) = ∑ i, m i := by
  rw [Finsupp.sum_fintype]
  intro; rfl

theorem restr_apply {n : ℕ} (m : Fin (n + 1) →₀ ℕ) (i : Fin n) : restr m i = m i.castSucc := rfl

theorem sum_restr {n : ℕ} (m : Fin (n + 1) →₀ ℕ) :
    (∑ i, restr m i) + m (Fin.last n) = ∑ i, m i := by
  simp only [restr_apply]
  exact (Fin.sum_univ_castSucc (f := fun j => m j)).symm

/-- The monomials of total degree at most `d` are at least `(n+d).choose d` in number. -/
theorem choose_le_card_monos (n d : ℕ) : Nat.choose (n + d) d ≤ (monos n d).card := by
  classical
  have hsrc : ((Finset.univ : Finset (Fin (n + 1))).finsuppAntidiag d).card
      = Nat.choose (n + d) d := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    congr 1
    simp
  rw [← hsrc]
  refine Finset.card_le_card_of_injOn restr ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_finsuppAntidiag] at hm
    rw [Finset.mem_coe, mem_monos]
    have h := sum_restr m
    have h2 : ∑ i, m i = d := hm.1
    omega
  · intro m1 h1 m2 h2 heq
    rw [Finset.mem_coe, Finset.mem_finsuppAntidiag] at h1 h2
    have e1 : ∑ i, m1 i = d := h1.1
    have e2 : ∑ i, m2 i = d := h2.1
    have hr : ∀ i : Fin n, m1 i.castSucc = m2 i.castSucc := fun i => by
      have := congrFun (congrArg (fun (f : Fin n →₀ ℕ) => (f : Fin n → ℕ)) heq) i
      simpa [restr_apply] using this
    have hs1 := sum_restr m1
    have hs2 := sum_restr m2
    have hsum : ∑ i, restr m1 i = ∑ i, restr m2 i :=
      Finset.sum_congr rfl fun i _ => by simpa [restr_apply] using hr i
    have hlast : m1 (Fin.last n) = m2 (Fin.last n) := by omega
    refine Finsupp.ext fun j => ?_
    refine Fin.lastCases ?_ ?_ j
    · exact hlast
    · intro i; exact hr i


variable {F : Type*} [Field F] [DecidableEq F]

/-- The linear map sending a coefficient vector to the tuple of values at the points of `E`. -/
noncomputable def evalMap (n d : ℕ) (E : Finset (Fin n → F)) :
    ((monos n d) → F) →ₗ[F] ({x // x ∈ E} → F) where
  toFun c := fun x => ∑ m : (monos n d), c m * ∏ i, (x : Fin n → F) i ^ ((m : Fin n →₀ ℕ) i)
  map_add' c1 c2 := by
    funext x
    simp only [Pi.add_apply, add_mul]
    exact Finset.sum_add_distrib
  map_smul' a c := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem evalMap_apply (n d : ℕ) (E : Finset (Fin n → F)) (c : (monos n d) → F)
    (x : {x // x ∈ E}) :
    evalMap n d E c x = ∑ m : (monos n d), c m * ∏ i, (x : Fin n → F) i ^ ((m : Fin n →₀ ℕ) i) :=
  rfl

theorem vanishing_polynomial {n d : ℕ} (E : Finset (Fin n → F))
    (hE : E.card < Nat.choose (n + d) d) :
    ∃ p : MvPolynomial (Fin n) F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      ∀ x ∈ E, MvPolynomial.eval x p = 0 := by
  classical
  have hcard : E.card < (monos n d).card := lt_of_lt_of_le hE (choose_le_card_monos n d)
  have hnotinj : ¬ Function.Injective (evalMap n d E) := by
    intro hinj
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe] at h
    omega
  rw [← LinearMap.ker_eq_bot] at hnotinj
  obtain ⟨c, hcmem, hcne⟩ := Submodule.ne_bot_iff _ |>.1 hnotinj
  have hker : ∀ x ∈ E, ∑ m : (monos n d), c m * ∏ i, x i ^ ((m : Fin n →₀ ℕ) i) = 0 := by
    intro x hx
    have := congrFun (LinearMap.mem_ker.1 hcmem) ⟨x, hx⟩
    simpa [evalMap_apply] using this
  obtain ⟨m0, hm0⟩ : ∃ m0 : (monos n d), c m0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hcne (funext hcon)
  refine ⟨∑ m ∈ (monos n d).attach, MvPolynomial.monomial (m : Fin n →₀ ℕ) (c m), ?_, ?_, ?_⟩
  · intro hzero
    apply hm0
    have hco : MvPolynomial.coeff (m0 : Fin n →₀ ℕ)
        (∑ m ∈ (monos n d).attach, MvPolynomial.monomial (m : Fin n →₀ ℕ) (c m)) = c m0 := by
      rw [MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single m0]
      · simp
      · intro b _ hb
        rw [MvPolynomial.coeff_monomial, if_neg]
        exact fun hcontra => hb (Subtype.ext hcontra)
      · intro h
        exact absurd (Finset.mem_attach _ m0) h
    rw [hzero] at hco
    simpa using hco.symm
  · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
    refine Finset.sup_le fun m _ => ?_
    refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
    have hm := mem_monos.1 m.2
    rw [show ((m : Fin n →₀ ℕ).sum fun _ => id) = ∑ i, (m : Fin n →₀ ℕ) i from
      Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact hm
  · intro x hx
    rw [map_sum]
    have : ∀ m ∈ (monos n d).attach,
        MvPolynomial.eval x (MvPolynomial.monomial (m : Fin n →₀ ℕ) (c m))
          = c m * ∏ i, x i ^ ((m : Fin n →₀ ℕ) i) := by
      intro m _
      rw [MvPolynomial.eval_monomial]
      congr 1
      exact Finsupp.prod_fintype _ _ (fun i => pow_zero (x i))
    rw [Finset.sum_congr rfl this]
    have hsum : ∑ m ∈ (monos n d).attach, c m * ∏ i, x i ^ ((m : Fin n →₀ ℕ) i)
        = ∑ m : (monos n d), c m * ∏ i, x i ^ ((m : Fin n →₀ ℕ) i) := rfl
    rw [hsum]
    exact hker x hx

end BookFix

open scoped BigOperators in
open BookSixth in
theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}
    (E : Finset (Fin n → F)) (hE : E.card < Nat.choose (n+d) d) :
    ∃ p : MvPolynomial (Fin n) F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      ∀ x ∈ E, MvPolynomial.eval x p = 0 :=
  BookFix.vanishing_polynomial E hE
