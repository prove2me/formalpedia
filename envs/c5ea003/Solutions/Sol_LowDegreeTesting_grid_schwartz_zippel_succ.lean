-- Prove2me | solution 1 for LowDegreeTesting.grid_schwartz_zippel_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:57:27.773034+00:00
-- url     : https://prove2.me/submissions/c0e4732e-05c5-45b6-b5e5-2bebb691f846

-- Sol generated from Bridges/LowDegreeTesting.lean
import Mathlib
import Definitions.Def_Bridges_LowDegreeTesting
/-
# Low-Degree Testing over Finite Grids

This file formalizes the **finite-grid uniqueness and testability principle** for
multivariate polynomials: on a Cartesian product grid S^n ⊆ K^n, a nonzero polynomial
of bounded total degree cannot vanish on too many grid points.

This is the combinatorial soundness theorem underlying:
- **Reed–Muller codes**: evaluation codes with explicit minimum distance
- **Low-degree testing**: random agreement tests are sound
- **Self-correction**: uniqueness enables correction from noisy oracles
- **PCP/sum-check**: algebraic proof systems rely on polynomial rigidity

## Main results

- `grid_schwartz_zippel`: A nonzero polynomial of total degree d < |S| has at most
  d · |S|^(n-1) zeros on the grid S^n. This is the finite-grid Schwartz–Zippel bound.

- `mvpoly_eq_on_grid_of_agree_many`: If two bounded-degree polynomials agree on more
  than d · |S|^(n-1) grid points, they agree on all grid points.

- `low_degree_explanation_unique`: Two low-degree polynomials that each explain too much
  of the same data must agree on the entire grid.

- `low_degree_code_distance`: Distinct bounded-degree polynomials disagree on at least
  |S|^n - d · |S|^(n-1) grid points (Reed–Muller minimum distance).

## References

- Schwartz (1980), Zippel (1979): Probabilistic polynomial identity testing
- Reed–Muller codes: Evaluation codes over finite grids
- Arora–Barak: Computational Complexity, Chapter 19 (Low-degree testing)
-/


open Classical in
noncomputable section

open LowDegreeTesting

open MvPolynomial Polynomial Finset BigOperators

variable {K : Type*} [Field K] [DecidableEq K]

/-! ## Section 1: Grid Definition and Basic Properties -/


@[simp]
theorem mem_Grid {S : Finset K} {n : ℕ} {x : Fin n → K} :
    x ∈ Grid S n ↔ ∀ i, x i ∈ S :=
  Fintype.mem_piFinset

theorem Grid_card (S : Finset K) (n : ℕ) : (Grid S n).card = S.card ^ n := by
  simp [Grid, Fintype.card_piFinset]

/-! ## Section 2: Univariate Root Bound in a Finite Set -/

/-
A nonzero univariate polynomial of degree d has at most d roots in any finite set.
-/
theorem univariate_roots_in_finset (p : Polynomial K) (S : Finset K)
    (hp : p ≠ 0) :
    (S.filter (fun x => p.eval x = 0)).card ≤ p.natDegree := by
  exact le_trans ( Finset.card_le_card ( show { x ∈ S | Polynomial.eval x p = 0 } ⊆ p.roots.toFinset from fun x hx => by aesop ) ) ( le_trans ( Multiset.toFinset_card_le _ ) ( Polynomial.card_roots' _ ) )

/-! ## Section 3: Fiber Decomposition -/


/-
Evaluating the fiber polynomial at t gives eval (Fin.cons t a) p.
-/
theorem eval_fiberPoly {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) K) (a : Fin n → K) (t : K) :
    Polynomial.eval t (fiberPoly p a) = MvPolynomial.eval (Fin.cons t a) p := by
  unfold fiberPoly;
  grind +suggestions

/-
The fiber zero count decomposes as a sum over the smaller grid.
-/
theorem grid_zero_card_eq_sum_fibers (S : Finset K) (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K) :
    ((Grid S (n + 1)).filter (fun x => MvPolynomial.eval x p = 0)).card =
    ∑ a ∈ Grid S n, (S.filter (fun t => MvPolynomial.eval (Fin.cons t a) p = 0)).card := by
  simp +decide only [card_filter];
  rw [ ← Finset.sum_product' ];
  refine' Finset.sum_bij ( fun x hx => ( Fin.tail x, x 0 ) ) _ _ _ _ <;> simp_all +decide;
  · exact fun a ha i => ha _;
  · intro a₁ ha₁ a₂ ha₂ h₁ h₂; ext i; induction i using Fin.inductionOn <;> simp_all +decide [ funext_iff, Fin.tail ] ;
  · exact fun a b ha hb => ⟨ Fin.cons b a, fun i => by cases i using Fin.inductionOn <;> simp +decide [ * ], rfl, rfl ⟩

/-! ## Section 4: Coefficient Degree Bound -/

/-
Total degree of the j-th coefficient of finSuccEquiv is at most totalDegree - j.
-/
theorem coeff_totalDegree_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (j : ℕ) :
    ((MvPolynomial.finSuccEquiv K n f).coeff j).totalDegree ≤ f.totalDegree - j := by
  simp +decide [ MvPolynomial.totalDegree ];
  intro b hb;
  refine' le_tsub_of_add_le_right ( le_trans _ ( Finset.le_sup <| show ( Finsupp.cons j b ) ∈ f.support from _ ) );
  · simp +decide [ Finsupp.sum_fintype, Fin.sum_univ_succ ];
    rw [ add_comm ];
  · simp_all +decide [ MvPolynomial.finSuccEquiv_coeff_coeff ]

/-
The leading coefficient (in the finSuccEquiv sense) is nonzero when f is nonzero.
-/
theorem finSuccEquiv_leadingCoeff_ne_zero {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) :
    (MvPolynomial.finSuccEquiv K n f).leadingCoeff ≠ 0 := by
  exact Polynomial.leadingCoeff_ne_zero.mpr ( by simpa using hf )

/-
The natDegree of the fiber polynomial is at most the natDegree of finSuccEquiv.
-/
theorem natDegree_fiberPoly_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (a : Fin n → K)
    (ha : MvPolynomial.eval a
      ((MvPolynomial.finSuccEquiv K n f).leadingCoeff) ≠ 0) :
    (fiberPoly f a).natDegree = (MvPolynomial.finSuccEquiv K n f).natDegree := by
  convert Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ _;
  exact ha


/-! ## Section 5: Main Grid Zero Count Theorem -/

/-
Base case: a nonzero polynomial in 0 variables has no zeros on S^0.
-/

/-
When the leading coefficient evaluates to nonzero, the fiber polynomial is nonzero.
-/
theorem fiberPoly_ne_zero_of_leadingCoeff {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) K) (a : Fin n → K)
    (ha : MvPolynomial.eval a
      ((MvPolynomial.finSuccEquiv K n p).leadingCoeff) ≠ 0) :
    fiberPoly p a ≠ 0 := by
  unfold fiberPoly;
  exact fun h => ha <| by simpa using congr_arg ( fun q => Polynomial.coeff q ( Polynomial.natDegree ( MvPolynomial.finSuccEquiv K n p ) ) ) h;

/-
Bound on fiber zero count for good fibers (leading coeff evaluates to nonzero).
-/
theorem fiber_zero_count_good {n : ℕ} (S : Finset K)
    (p : MvPolynomial (Fin (n + 1)) K) (a : Fin n → K)
    (ha : MvPolynomial.eval a
      ((MvPolynomial.finSuccEquiv K n p).leadingCoeff) ≠ 0) :
    (S.filter (fun t => MvPolynomial.eval (Fin.cons t a) p = 0)).card
    ≤ (MvPolynomial.finSuccEquiv K n p).natDegree := by
  -- By eval_fiberPoly, the filter becomes {t ∈ S | (fiberPoly p a).eval t = 0}.
  suffices h_filter : (S.filter (fun t => (fiberPoly p a).eval t = 0)).card ≤ (fiberPoly p a).natDegree by
    convert h_filter using 2;
    · exact Finset.filter_congr fun x hx => by rw [ eval_fiberPoly ] ;
    · exact?;
  convert univariate_roots_in_finset ( fiberPoly p a ) S _;
  exact?

/-
The leading coefficient's total degree is bounded.
-/
theorem leadingCoeff_totalDegree_le {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) K) :
    (MvPolynomial.finSuccEquiv K n p).leadingCoeff.totalDegree
    ≤ p.totalDegree - (MvPolynomial.finSuccEquiv K n p).natDegree := by
  convert coeff_totalDegree_le p ( Polynomial.natDegree ( MvPolynomial.finSuccEquiv K n p ) ) using 1

/-
The degreeOf 0 is at most the totalDegree.
-/
theorem natDegree_finSuccEquiv_le_totalDegree {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) K) :
    (MvPolynomial.finSuccEquiv K n p).natDegree ≤ p.totalDegree := by
  -- By MvPolynomial.natDegree_finSuccEquiv, the natDegree of `finSuccEquiv K n p` is equal to the degreeOf 0 p.
  have h_natDegree_eq_degreeOf : ((MvPolynomial.finSuccEquiv K n) p).natDegree = p.degreeOf 0 := by
    exact?;
  exact h_natDegree_eq_degreeOf.symm ▸ p.degreeOf_le_totalDegree 0

/-
**Grid Schwartz–Zippel Theorem (inductive step)**:
-/


/-! ## Section 6: Uniqueness and Distance Corollaries -/

/-
**Theorem A: Finite-grid uniqueness from large agreement.**
    If two polynomials of total degree ≤ d < |S| agree on more than d · |S|^(n-1)
    grid points, they agree on all grid points.
-/

/-
The original Theorem B as stated in the assignment (with each polynomial agreeing
   with f on > d · |S|^(n-1) points individually) is FALSE. Counterexample:
   K = ℚ, S = {0,1,2}, n = 1, d = 1, p(x) = x, q(x) = 2-x, f(0) = 2, f(1) = 1, f(2) = 2.
   Both p and q agree with f on 2 > 1 = d·|S|^0 points, yet p ≠ q on S.

   The correct version requires the SUM of agreements to exceed |S|^n + d · |S|^(n-1),
   which ensures the overlap (intersection of the two agreement sets) exceeds d · |S|^(n-1).

**Theorem B (corrected): Uniqueness of a low-degree explanation for a noisy function.**
    If two degree-≤ d polynomials p and q have combined agreement with f exceeding
    |S|^n + d · |S|^(n-1), then p and q agree on all grid points.
    This is the unique decoding radius condition for Reed–Muller codes.
-/

/-
**Theorem C: Distance lower bound for distinct low-degree polynomials.**
    Distinct polynomials of total degree ≤ d < |S| disagree on at least
    |S|^n - d · |S|^(n-1) grid points (Reed–Muller minimum distance).
-/



open LowDegreeTesting in
theorem solution(n : ℕ) (S : Finset K)
    (p : MvPolynomial (Fin (n + 1)) K)
    (hp : p ≠ 0) (hS : p.totalDegree < S.card)
    (ih : ∀ (q : MvPolynomial (Fin n) K), q ≠ 0 → q.totalDegree < S.card →
      ((Grid S n).filter (fun x => MvPolynomial.eval x q = 0)).card
      ≤ q.totalDegree * S.card ^ (n - 1)) :
    ((Grid S (n + 1)).filter (fun x => MvPolynomial.eval x p = 0)).card
    ≤ p.totalDegree * S.card ^ n := by
  by_cases hn : n = 0;
  · subst hn; simp_all +decide [ Grid ] ;
    -- Since $p$ is a polynomial in one variable, its total degree is equal to its degree.
    have h_deg : p.totalDegree = Polynomial.natDegree (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) p) := by
      rw [ MvPolynomial.eval₂_eq' ];
      rw [ Polynomial.natDegree_sum_eq_of_disjoint ];
      · refine' le_antisymm _ _ <;> simp +decide [ MvPolynomial.totalDegree ];
        · intro b hb; refine' le_trans _ ( Finset.le_sup ( f := fun i => Polynomial.natDegree ( Polynomial.C ( MvPolynomial.coeff i p ) * Polynomial.X ^ i 0 ) ) ( Finsupp.mem_support_iff.mpr hb ) ) ; simp +decide [ Finsupp.sum_fintype ] ;
          rw [ Polynomial.natDegree_C_mul_X_pow ] ; aesop;
        · intro b hb; rw [ Polynomial.natDegree_C_mul_X_pow ] <;> simp_all +decide [ Finsupp.sum_fintype ] ;
          exact Finset.le_sup ( f := fun s => s 0 ) ( Finsupp.mem_support_iff.mpr hb );
      · intro i hi j hj hij; contrapose hij; simp_all +decide [ Polynomial.natDegree_C_mul, Polynomial.natDegree_prod' ] ;
        exact Finsupp.ext fun x => by fin_cases x; exact hij;
    -- By the properties of the polynomial evaluation, we have that $MvPolynomial.eval x p = Polynomial.eval (x 0) (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) p)$ for any $x : Fin 1 → K$.
    have h_eval : ∀ x : Fin 1 → K, MvPolynomial.eval x p = Polynomial.eval (x 0) (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) p) := by
      intro x; rw [ MvPolynomial.eval_eq' ];
      simp +decide [ MvPolynomial.eval₂_eq', Polynomial.eval_finset_sum ];
    -- By the properties of the polynomial evaluation, we have that $MvPolynomial.eval x p = Polynomial.eval (x 0) (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) p)$ for any $x : Fin 1 → K$. Therefore, the number of zeros of $p$ on $S$ is equal to the number of zeros of $MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) p$ on $S$.
    have h_zeros_eq : (Finset.filter (fun x : Fin 1 → K => MvPolynomial.eval x p = 0) (Fintype.piFinset fun _ => S)).card = (Finset.filter (fun x : K => Polynomial.eval x (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) p) = 0) S).card := by
      refine' Finset.card_bij ( fun x hx => x 0 ) _ _ _ <;> simp +decide [ h_eval ];
      · exact fun a₁ ha₁ ha₂ a₂ ha₃ ha₄ h => by ext i; fin_cases i; exact h;
      · exact fun b hb hb' => ⟨ fun _ => b, ⟨ hb, hb' ⟩, rfl ⟩;
    rw [ h_zeros_eq, h_deg ];
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact ( MvPolynomial.eval₂ Polynomial.C ( fun x => Polynomial.X ) p |> Polynomial.roots |> Multiset.toFinset );
    · simp +contextual [ Finset.subset_iff ];
      intro x hx hx'; contrapose! hp; simp_all +decide [ MvPolynomial.eval₂_eq' ] ;
      ext x; replace hp := congr_arg ( fun q => Polynomial.coeff q ( x 0 ) ) hp; simp_all +decide [ Polynomial.coeff_C, Polynomial.coeff_X_pow ] ;
      rw [ Finset.sum_eq_single x ] at hp <;> simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_succ ];
      exact fun b hb hb' => Ne.symm hb';
    · exact le_trans ( Multiset.toFinset_card_le _ ) ( Polynomial.card_roots' _ );
  · -- Apply the induction hypothesis to the leading coefficient.
    have h_ind : (Finset.filter (fun a => MvPolynomial.eval a ((MvPolynomial.finSuccEquiv K n p).leadingCoeff) = 0) (Grid S n)).card ≤ (MvPolynomial.finSuccEquiv K n p).leadingCoeff.totalDegree * S.card ^ (n - 1) := by
      apply ih;
      · grind +suggestions;
      · exact lt_of_le_of_lt ( leadingCoeff_totalDegree_le p ) ( lt_of_le_of_lt ( Nat.sub_le _ _ ) hS );
    -- Split the sum into two parts: one over the bad fibers and one over the good fibers.
    have h_split : (Finset.filter (fun x => MvPolynomial.eval x p = 0) (Grid S (n + 1))).card ≤
      (Finset.filter (fun a => MvPolynomial.eval a ((MvPolynomial.finSuccEquiv K n p).leadingCoeff) = 0) (Grid S n)).card * S.card +
      (Finset.filter (fun a => MvPolynomial.eval a ((MvPolynomial.finSuccEquiv K n p).leadingCoeff) ≠ 0) (Grid S n)).card * (MvPolynomial.finSuccEquiv K n p).natDegree := by
        rw [ grid_zero_card_eq_sum_fibers ];
        refine' le_trans ( Finset.sum_le_sum fun a ha => show #({t ∈ S | (MvPolynomial.eval (Fin.cons t a)) p = 0}) ≤ if (MvPolynomial.eval a) ((MvPolynomial.finSuccEquiv K n) p).leadingCoeff = 0 then #S else (MvPolynomial.finSuccEquiv K n p).natDegree from _ ) _;
        · split_ifs with h;
          · exact Finset.card_filter_le _ _;
          · convert fiber_zero_count_good S p a h using 1;
        · simp +decide [ Finset.sum_ite, Finset.filter_not, Finset.card_sdiff ];
    -- Substitute the induction hypothesis into the split sum inequality.
    have h_subst : (Finset.filter (fun x => MvPolynomial.eval x p = 0) (Grid S (n + 1))).card ≤
      (p.totalDegree - (MvPolynomial.finSuccEquiv K n p).natDegree) * S.card ^ (n - 1) * S.card +
      S.card ^ n * (MvPolynomial.finSuccEquiv K n p).natDegree := by
        refine' le_trans h_split ( add_le_add _ _ );
        · gcongr;
          exact h_ind.trans ( Nat.mul_le_mul_right _ ( leadingCoeff_totalDegree_le p ) );
        · exact mul_le_mul_of_nonneg_right ( le_trans ( Finset.card_filter_le _ _ ) ( by simp +decide [ Grid_card ] ) ) ( Nat.zero_le _ );
    refine le_trans h_subst ?_;
    rw [ show #S ^ n = #S ^ ( n - 1 ) * #S by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.pos_of_ne_zero hn ) ] ];
    nlinarith only [ Nat.sub_add_cancel ( show ( MvPolynomial.finSuccEquiv K n p ).natDegree ≤ p.totalDegree from natDegree_finSuccEquiv_le_totalDegree p ), show 0 ≤ #S ^ ( n - 1 ) * #S by positivity ]
