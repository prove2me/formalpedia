-- Prove2me | solution 1 for fib_entry_point
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:29:42.825912+00:00
-- url     : https://prove2.me/submissions/8f06009e-2038-42b8-8e75-ab0076f5a8cf

-- Sol generated from Algebra/OpenDirections.lean
import Mathlib
import Definitions.Def_Algebra_OpenDirections

/-! # CatalogBuild.Speculative.OpenDirections

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 42
-/











































set_option maxHeartbeats 2000000 in
theorem solution(p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    p ∣ Nat.fib (p - 1) ∨ p ∣ Nat.fib (p + 1) := by
  by_contra! h;
  haveI := Fact.mk hp;
  -- Let's consider the roots of the characteristic polynomial of the Fibonacci sequence modulo p.
  obtain ⟨α, β, hαβ⟩ : ∃ α β : AlgebraicClosure (ZMod p), α + β = 1 ∧ α * β = -1 := by
    -- The polynomial $x^2 - x - 1$ has roots in the algebraic closure of $\mathbb{Z}/p\mathbb{Z}$.
    have h_poly_roots : ∃ α : AlgebraicClosure (ZMod p), α^2 - α - 1 = 0 := by
      have h_alg_closed : IsAlgClosed (AlgebraicClosure (ZMod p)) := by
        infer_instance;
      have := h_alg_closed.exists_root;
      exact Exists.elim ( this ( Polynomial.X ^ 2 - Polynomial.X - 1 ) ( by erw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> erw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num ) ) fun x hx => ⟨ x, by simpa using hx ⟩;
    exact ⟨ h_poly_roots.choose, 1 - h_poly_roots.choose, by ring, by linear_combination -h_poly_roots.choose_spec ⟩;
  -- Using the roots α and β, we can express F_n as (α^n - β^n) / (α - β).
  have h_fib_expr : ∀ n : ℕ, (Nat.fib n : AlgebraicClosure (ZMod p)) = (α^n - β^n) / (α - β) := by
    intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.fib_add_two ] ;
    · rw [ div_self ] ; intro H ; simp_all +decide [ sub_eq_iff_eq_add ];
      simp_all +decide [ ← two_mul ];
      have := congr_arg ( · ^ 2 ) hαβ.1; norm_num [ mul_pow, hαβ.2 ] at this;
      simp_all +decide [sq];
      rw [ neg_eq_iff_add_eq_zero ] at this;
      norm_num at this;
      erw [ CharP.cast_eq_zero_iff ( AlgebraicClosure ( ZMod p ) ) p ] at this ; have := Nat.le_of_dvd ( by decide ) this ; interval_cases p <;> trivial;
    · grind;
  -- Since $p$ is prime and does not divide $5$, we have $\alpha^p = \beta$ and $\beta^p = \alpha$.
  have h_alpha_beta_p : α^p = β ∧ β^p = α := by
    have h_alpha_beta_p : α^p + β^p = 1 ∧ α^p * β^p = -1 := by
      have h_alpha_beta_p : α^p + β^p = (α + β)^p ∧ α^p * β^p = (α * β)^p := by
        simp +decide [ add_pow_char, mul_pow ];
      cases hp.eq_two_or_odd' <;> simp_all +decide;
    have h_alpha_beta_p : α^p = β ∨ α^p = α := by
      grind +ring;
    cases h_alpha_beta_p <;> simp_all +decide [ ← eq_sub_iff_add_eq' ];
    have := h_fib_expr ( p - 1 ) ; rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.fib_add_two ] ;
    have h_contra : (Nat.fib (p + 1) : AlgebraicClosure (ZMod (p + 2))) = 0 := by
      grind;
    erw [ CharP.cast_eq_zero_iff ( AlgebraicClosure ( ZMod ( p + 2 ) ) ) ( p + 2 ) ] at h_contra ; aesop;
  -- Using the expressions for α^p and β^p, we can simplify F_{p-1} and F_{p+1} to show that one of them must be zero.
  have h_fib_p_minus_1_zero : (Nat.fib (p - 1) : AlgebraicClosure (ZMod p)) = 0 ∨ (Nat.fib (p + 1) : AlgebraicClosure (ZMod p)) = 0 := by
    grind;
  simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
  have h_fib_p_minus_1_zero : (Nat.fib (p - 1) : ZMod p) = 0 ∨ (Nat.fib (p + 1) : ZMod p) = 0 := by
    have h_fib_p_minus_1_zero : Function.Injective (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
      exact RingHom.injective _;
    exact Or.imp ( fun h => h_fib_p_minus_1_zero <| by aesop ) ( fun h => h_fib_p_minus_1_zero <| by aesop ) ‹ ( α ^ ( p - 1 ) - β ^ ( p - 1 ) = 0 ∨ α - β = 0 ) ∨ α ^ ( p + 1 ) - β ^ ( p + 1 ) = 0 ∨ α - β = 0 ›;
  aesop
