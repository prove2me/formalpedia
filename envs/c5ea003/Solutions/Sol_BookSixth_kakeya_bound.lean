-- Prove2me | solution 1 for BookSixth.kakeya_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T04:02:40.656434+00:00
-- url     : https://prove2.me/submissions/dbc7eff3-70fb-4062-b9e8-c7f0f66d167c

import Mathlib
import Definitions.Def_BookSixth

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open BookSixth

/-!
# Dvir's theorem: the finite-field Kakeya bound

Mathlib has neither the polynomial method for Kakeya sets nor the interpolation bound that
feeds it; both are developed here in a private namespace.
-/

namespace Kak



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

/-! ## Top coefficients of products of polynomials -/

section Coeff

variable {R : Type*} [CommRing R]

theorem coeff_mul_of_le {p q : Polynomial R} {M N : ℕ}
    (hp : p.natDegree ≤ M) (hq : q.natDegree ≤ N) :
    (p * q).coeff (M + N) = p.coeff M * q.coeff N := by
  classical
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (M, N) ?_ ?_
  · rintro ⟨i, j⟩ hij hne
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rcases lt_or_gt_of_ne (fun h : i = M => hne (by
      subst h
      have : j = N := by omega
      simp [this])) with hi | hi
    · have : N < j := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq this), mul_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hi), zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp : (M, N).1 + (M, N).2 = M + N)) h

theorem coeff_prod_of_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial R) (g : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ g i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, g i) = ∏ i ∈ s, (f i).coeff (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
      have hdeg : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, g i :=
        le_trans (Polynomial.natDegree_prod_le _ _)
          (Finset.sum_le_sum fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [coeff_mul_of_le (h a (Finset.mem_insert_self a s)) hdeg,
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- A linear polynomial `a + b X`. -/
theorem natDegree_lin_le (a b : R) : (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree
    ≤ 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  simp only [Polynomial.natDegree_C, max_le_iff]
  refine ⟨Nat.zero_le _, le_trans (Polynomial.natDegree_mul_le) ?_⟩
  simp only [Polynomial.natDegree_C, zero_add]
  exact Polynomial.natDegree_X_le

theorem coeff_one_lin (a b : R) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).coeff 1 = b := by
  simp

theorem natDegree_lin_pow_le (a b : R) (e : ℕ) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ e).natDegree ≤ e := by
  refine le_trans (Polynomial.natDegree_pow_le) ?_
  have := natDegree_lin_le a b
  nlinarith [this]

theorem coeff_lin_pow (a b : R) (e : ℕ) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ e).coeff e = b ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [pow_succ, show e + 1 = e + 1 from rfl,
        coeff_mul_of_le (natDegree_lin_pow_le a b e) (natDegree_lin_le a b), ih,
        coeff_one_lin, pow_succ]

end Coeff

/-! ## Restricting a polynomial to a line -/

section Line

open MvPolynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- The `i`-th coordinate of the parametrised line `w + t v`, as a polynomial in `t`. -/
noncomputable def lineP (w v : Fin n → F) (i : Fin n) : Polynomial F :=
  Polynomial.C (w i) + Polynomial.C (v i) * Polynomial.X

/-- The restriction of `P` to the line `t ↦ w + t v`. -/
noncomputable def restrictLine (P : MvPolynomial (Fin n) F) (w v : Fin n → F) : Polynomial F :=
  MvPolynomial.aeval (lineP w v) P

theorem eval_restrictLine (P : MvPolynomial (Fin n) F) (w v : Fin n → F) (t : F) :
    Polynomial.eval t (restrictLine P w v) = MvPolynomial.eval (fun i => w i + v i * t) P := by
  rw [restrictLine, MvPolynomial.aeval_def]
  rw [show Polynomial.eval t (MvPolynomial.eval₂ (algebraMap F (Polynomial F)) (lineP w v) P)
      = (Polynomial.evalRingHom t)
          (MvPolynomial.eval₂ (algebraMap F (Polynomial F)) (lineP w v) P) from rfl]
  rw [MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom t)]
  simp only [MvPolynomial.eval, lineP, Function.comp_def, Polynomial.coe_evalRingHom,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  ext a
  simp

theorem restrictLine_eq_sum (P : MvPolynomial (Fin n) F) (w v : Fin n → F) :
    restrictLine P w v
      = ∑ m ∈ P.support,
          Polynomial.C (MvPolynomial.coeff m P) * ∏ i, (lineP w v i) ^ (m i) := by
  rw [restrictLine, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  rfl

theorem natDegree_term_le (P : MvPolynomial (Fin n) F) (w v : Fin n → F)
    {m : Fin n →₀ ℕ} :
    (Polynomial.C (MvPolynomial.coeff m P) * ∏ i, (lineP w v i) ^ (m i)).natDegree
      ≤ ∑ i, m i := by
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  simp only [Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  exact Finset.sum_le_sum fun i _ => natDegree_lin_pow_le _ _ _

theorem natDegree_restrictLine_le (P : MvPolynomial (Fin n) F) (w v : Fin n → F) :
    (restrictLine P w v).natDegree ≤ P.totalDegree := by
  rw [restrictLine_eq_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine le_trans (natDegree_term_le P w v) ?_
  have := MvPolynomial.le_totalDegree (s := m) hm
  rwa [sum_eq] at this

theorem coeff_term_top (P : MvPolynomial (Fin n) F) (w v : Fin n → F) {m : Fin n →₀ ℕ} :
    (Polynomial.C (MvPolynomial.coeff m P) * ∏ i, (lineP w v i) ^ (m i)).coeff (∑ i, m i)
      = MvPolynomial.coeff m P * ∏ i, v i ^ (m i) := by
  rw [Polynomial.coeff_C_mul]
  congr 1
  rw [coeff_prod_of_le (Finset.univ : Finset (Fin n)) (fun i => lineP w v i ^ (m i))
    (fun i => m i) (fun i _ => natDegree_lin_pow_le (w i) (v i) (m i))]
  exact Finset.prod_congr rfl fun i _ => coeff_lin_pow _ _ _

theorem coeff_restrictLine (P : MvPolynomial (Fin n) F) (w v : Fin n → F) :
    (restrictLine P w v).coeff P.totalDegree
      = MvPolynomial.eval v (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  set d := P.totalDegree with hd
  rw [restrictLine_eq_sum, Polynomial.finset_sum_coeff]
  have hdeg : ∀ m ∈ P.support, ∑ i, m i ≤ d := by
    intro m hm
    have := MvPolynomial.le_totalDegree (s := m) hm
    rwa [sum_eq] at this
  have hcoeffH : ∀ m : Fin n →₀ ℕ,
      MvPolynomial.coeff m (MvPolynomial.homogeneousComponent d P)
        = if (∑ i, m i) = d then MvPolynomial.coeff m P else 0 := by
    intro m
    rw [MvPolynomial.coeff_homogeneousComponent, Finsupp.degree_eq_sum]
  have hterm : ∀ m ∈ P.support,
      (Polynomial.C (MvPolynomial.coeff m P) * ∏ i, (lineP w v i) ^ (m i)).coeff d
        = MvPolynomial.coeff m (MvPolynomial.homogeneousComponent d P) * ∏ i, v i ^ (m i) := by
    intro m hm
    rw [hcoeffH m]
    by_cases hmd : (∑ i, m i) = d
    · rw [if_pos hmd, ← hmd, coeff_term_top]
    · rw [if_neg hmd, zero_mul]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_term_le P w v) (lt_of_le_of_ne (hdeg m hm) hmd))
  rw [Finset.sum_congr rfl hterm, MvPolynomial.eval_eq']
  refine (Finset.sum_subset ?_ ?_).symm
  · intro m hm
    rw [MvPolynomial.mem_support_iff, hcoeffH m] at hm
    rw [MvPolynomial.mem_support_iff]
    intro hc
    apply hm
    split <;> simp [hc]
  · intro m hm hnm
    rw [MvPolynomial.notMem_support_iff] at hnm
    rw [hnm, zero_mul]

end Line

/-! ## Dvir's theorem -/

section Dvir

open MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

theorem exists_ne_zero_dir (hn : 0 < n) : ∃ v : Fin n → F, v ≠ 0 := by
  refine ⟨Pi.single ⟨0, hn⟩ (1 : F), ?_⟩
  intro hc
  have := congrFun hc ⟨0, hn⟩
  simp at this

/-- **Dvir's theorem**: a Kakeya set in `Fⁿ` has at least `C(q + n - 1, n)` points. -/
theorem kakeya_choose_le (hn : 0 < n) (K : Finset (Fin n → F)) (hK : Kakeya K) :
    Nat.choose (Fintype.card F + n - 1) n ≤ K.card := by
  classical
  set q := Fintype.card F with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  by_contra hlt
  push Not at hlt
  -- a nonzero polynomial of degree at most `q - 1` vanishing on `K`
  have hchoose : Nat.choose (n + (q - 1)) (q - 1) = Nat.choose (q + n - 1) n := by
    have h1 : n + (q - 1) = q + n - 1 := by omega
    have h2 : (q + n - 1) - n = q - 1 := by omega
    rw [h1]
    conv_lhs => rw [← h2]
    exact Nat.choose_symm (by omega)
  obtain ⟨P, hP0, hPdeg, hPvan⟩ := vanishing_polynomial K (by rw [hchoose]; exact hlt)
  set D := P.totalDegree with hD
  -- `K` is nonempty
  obtain ⟨v0, hv0⟩ := exists_ne_zero_dir (F := F) hn
  obtain ⟨w0, hw0⟩ := hK v0 hv0
  have hKne : (w0 : Fin n → F) ∈ K := by
    have := hw0 0
    simpa using this
  -- the top degree is positive
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · exfalso
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h
      rw [h] at hP0 hPvan
      have := hPvan w0 hKne
      rw [MvPolynomial.eval_C] at this
      exact hP0 (by rw [this]; simp)
    · exact h
  set H := MvPolynomial.homogeneousComponent D P with hH
  have hcoeffH : ∀ m : Fin n →₀ ℕ,
      MvPolynomial.coeff m H = if (∑ i, m i) = D then MvPolynomial.coeff m P else 0 := by
    intro m
    rw [hH, MvPolynomial.coeff_homogeneousComponent, Finsupp.degree_eq_sum]
  -- `H` is nonzero
  have hHne : H ≠ 0 := by
    obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support
      (MvPolynomial.support_nonempty.2 hP0) (fun m : Fin n →₀ ℕ => m.sum fun _ e => e)
    have hmD : (∑ i, m i) = D := by
      rw [hD, MvPolynomial.totalDegree, hmd, sum_eq]
    intro hc
    have : MvPolynomial.coeff m H = MvPolynomial.coeff m P := by rw [hcoeffH m, if_pos hmD]
    rw [hc] at this
    exact (MvPolynomial.mem_support_iff.1 hm) this.symm
  -- `H` vanishes everywhere
  have hHvan : ∀ v : Fin n → F, MvPolynomial.eval v H = 0 := by
    intro v
    by_cases hv : v = 0
    · subst hv
      rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, hcoeffH 0]
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero]
      rw [if_neg (by omega)]
    · obtain ⟨w, hw⟩ := hK v hv
      have hzero : restrictLine P w v = 0 := by
        refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
          Function.injective_id ?_ ?_
        · intro t
          rw [Function.id_def]
          rw [eval_restrictLine]
          refine hPvan _ ?_
          have := hw t
          have heq : (fun i => w i + v i * t) = w + t • v := by
            funext i
            simp [mul_comm]
          rw [heq]
          exact this
        · exact lt_of_le_of_lt (natDegree_restrictLine_le P w v) (by omega)
      have := coeff_restrictLine P w v
      rw [hzero] at this
      simpa [hH] using this.symm
  -- contradiction with the vanishing criterion
  have hzero : H = 0 := by
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset H (fun _ => Finset.univ) ?_ ?_
    · intro i
      have h1 : H.degreeOf i ≤ H.totalDegree := MvPolynomial.degreeOf_le_totalDegree H i
      have h2 : H.totalDegree = D :=
        (MvPolynomial.homogeneousComponent_isHomogeneous D P).totalDegree hHne
      have hcard : (Finset.univ : Finset F).card = q := by simp [hq]
      rw [hcard]
      omega
    · intro x _
      exact hHvan x
  exact hHne hzero

/-- The second Kakeya bound, `qⁿ ≤ n! · |K|`. -/
theorem kakeya_pow_le (hn : 0 < n) (K : Finset (Fin n → F)) (hK : Kakeya K) :
    Fintype.card F ^ n ≤ n.factorial * K.card := by
  have h1 := kakeya_choose_le hn K hK
  have h2 : (Fintype.card F).ascFactorial n
      = n.factorial * (Fintype.card F + n - 1).choose n :=
    Nat.ascFactorial_eq_factorial_mul_choose' _ _
  have h3 : Fintype.card F ^ n ≤ (Fintype.card F).ascFactorial n :=
    Nat.pow_succ_le_ascFactorial _ _
  calc Fintype.card F ^ n ≤ (Fintype.card F).ascFactorial n := h3
    _ = n.factorial * (Fintype.card F + n - 1).choose n := h2
    _ ≤ n.factorial * K.card := Nat.mul_le_mul_left _ h1

end Dvir


end Kak

open scoped BigOperators in
open BookSixth in
theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (hn : 0 < n)
    (K : Finset (Fin n → F)) (hK : Kakeya K) :
    Nat.choose (Fintype.card F + n - 1) n ≤ K.card ∧
      Fintype.card F ^ n ≤ n.factorial * K.card :=
  ⟨Kak.kakeya_choose_le hn K hK, Kak.kakeya_pow_le hn K hK⟩
