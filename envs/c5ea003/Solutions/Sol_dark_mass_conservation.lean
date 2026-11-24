-- Prove2me | solution 1 for dark_mass_conservation
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:36:40.738346+00:00
-- url     : https://prove2.me/submissions/34307169-aa2d-442f-babc-90492399f742

-- Thm stub generated from Bridges/BerggrenTrees/ArithmeticDarkMatter.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenTrees_ArithmeticDarkMatter

/-! # CatalogBuild.Algebra.Core.ArithmeticDarkMatter

Auto-generated from theorem catalog database.
Domain: Algebra/Core
Declarations: 24
-/

structure ArithParticle where
  a : ℤ
  b : ℤ
  c : ℤ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c

def ArithParticle.massSq (p : ArithParticle) : ℤ :=
  p.c ^ 2 - p.a ^ 2 - p.b ^ 2

def ArithParticle.isPhoton (p : ArithParticle) : Prop :=
  p.massSq = 0

def ArithParticle.isMassive' (p : ArithParticle) : Prop :=
  p.massSq > 0

def ArithParticle.isTachyon (p : ArithParticle) : Prop :=
  p.massSq < 0

theorem every_nonneg_mass_realized (m_sq : ℕ) :
    massIsRealized (m_sq : ℤ) := by
  by_contra h;
  -- For even m_sq, we can take a=1, b=m_sq/2, c=m_sq/2+1.
  by_cases h_even : Even m_sq;
  · obtain ⟨ k, rfl ⟩ := h_even;
    exact h ⟨ 1, k, k + 1, by norm_num, by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; exact h ⟨ 3, 4, 5, by norm_num ⟩ ) ], by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; exact h ⟨ 3, 4, 5, by norm_num ⟩ ) ], by push_cast; linarith ⟩;
  · -- For odd m_sq, we can take a=2, b=(m_sq+3)/2, c=(m_sq+5)/2.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m_sq = 2 * k + 1 := by
      exact m_sq.even_or_odd.resolve_left h_even;
    refine h ⟨ 2, k + 2, k + 3, by norm_num, by linarith, by linarith, ?_ ⟩ ; push_cast [ hk ] ; ring

theorem B1_preserves_Q (a b c : ℤ) :
    Q_form (berggren_B1 a b c).1 (berggren_B1 a b c).2.1 (berggren_B1 a b c).2.2
    = Q_form a b c := by
  unfold berggren_B1 Q_form
  ring

theorem B2_preserves_Q (a b c : ℤ) :
    Q_form (berggren_B2 a b c).1 (berggren_B2 a b c).2.1 (berggren_B2 a b c).2.2
    = Q_form a b c := by
  unfold berggren_B2 Q_form
  ring

theorem B3_preserves_Q (a b c : ℤ) :
    Q_form (berggren_B3 a b c).1 (berggren_B3 a b c).2.1 (berggren_B3 a b c).2.2
    = Q_form a b c := by
  unfold berggren_B3 Q_form
  ring

theorem dark_mass_conservation (seed : ℤ × ℤ × ℤ) (p : DarkPath) :
    Q_form (darkTriple seed p).1 (darkTriple seed p).2.1 (darkTriple seed p).2.2
    = Q_form seed.1 seed.2.1 seed.2.2 := by
  induction p with
  | root => rfl
  | b1 p ih =>
    simp only [darkTriple]
    rw [show (darkTriple seed p).1 = (darkTriple seed p).1 from rfl]
    have : Q_form (darkTriple seed p).1 (darkTriple seed p).2.1 (darkTriple seed p).2.2
      = Q_form seed.1 seed.2.1 seed.2.2 := ih
    set a := (darkTriple seed p).1
    set b := (darkTriple seed p).2.1
    set c := (darkTriple seed p).2.2
    show Q_form (a - 2*b + 2*c) (2*a - b + 2*c) (2*a - 2*b + 3*c) = Q_form seed.1 seed.2.1 seed.2.2
    rw [show Q_form (a - 2*b + 2*c) (2*a - b + 2*c) (2*a - 2*b + 3*c) = Q_form a b c from by unfold Q_form; ring]
    exact ih
  | b2 p ih =>
    simp only [darkTriple]
    set a := (darkTriple seed p).1
    set b := (darkTriple seed p).2.1
    set c := (darkTriple seed p).2.2
    show Q_form (a + 2*b + 2*c) (2*a + b + 2*c) (2*a + 2*b + 3*c) = Q_form seed.1 seed.2.1 seed.2.2
    rw [show Q_form (a + 2*b + 2*c) (2*a + b + 2*c) (2*a + 2*b + 3*c) = Q_form a b c from by unfold Q_form; ring]
    exact ih
  | b3 p ih =>
    simp only [darkTriple]
    set a := (darkTriple seed p).1
    set b := (darkTriple seed p).2.1
    set c := (darkTriple seed p).2.2
    show Q_form (-a + 2*b + 2*c) (-2*a + b + 2*c) (-2*a + 2*b + 3*c) = Q_form seed.1 seed.2.1 seed.2.2
    rw [show Q_form (-a + 2*b + 2*c) (-2*a + b + 2*c) (-2*a + 2*b + 3*c) = Q_form a b c from by unfold Q_form; ring]
    exact ih

def massCensus (N : ℕ) : List (ℤ × ℕ) :=
  let triples := do
    let c ← List.range (N + 1)
    let b ← List.range (c + 1)
    let a ← List.range (b + 1)
    if a > 0 && b > 0 && c > 0 then
      return (a, b, c)
    else .nil
  let masses := triples.map fun (a, b, c) =>
    ((c * c : ℤ) - (a * a : ℤ) - (b * b : ℤ))
  -- Group by mass-squared and count
  let distinct := masses.eraseDups
  let counts := distinct.map fun m => (m, (masses.filter (· == m)).length)
  let filtered := counts.filter (fun p => p.2 > 2)
  filtered.take 20

def photonFraction (N : ℕ) : ℕ × ℕ :=
  let triples := do
    let c ← List.range (N + 1)
    let b ← List.range (c + 1)
    let a ← List.range (b + 1)
    if a > 0 && b > 0 && c > 0 then return (a, b, c) else .nil
  let total := triples.length
  let photons := triples.filter (fun (a, b, c) => a*a + b*b == c*c) |>.length
  (photons, total)

theorem universal_branching : ∀ (seed : ℤ × ℤ × ℤ),
    (darkTreeLevel seed 1).length = 3 * (darkTreeLevel seed 0).length := by
  intro seed
  simp [darkTreeLevel]

theorem dark_has_more_states (n : ℕ) (m : ℕ) (hm : 1 < m) :
    photonStates n < darkStates n m := by
  unfold photonStates darkStates
  have h3 : 0 < 3 ^ n := Nat.pos_of_ne_zero (by positivity)
  nlinarith


theorem solution (seed : ℤ × ℤ × ℤ) (p : DarkPath) :
    Q_form (darkTriple seed p).1 (darkTriple seed p).2.1 (darkTriple seed p).2.2
    = Q_form seed.1 seed.2.1 seed.2.2 := by
  induction p with
  | root => rfl
  | b1 p ih =>
    simp only [darkTriple]
    rw [show (darkTriple seed p).1 = (darkTriple seed p).1 from rfl]
    have : Q_form (darkTriple seed p).1 (darkTriple seed p).2.1 (darkTriple seed p).2.2
      = Q_form seed.1 seed.2.1 seed.2.2 := ih
    set a := (darkTriple seed p).1
    set b := (darkTriple seed p).2.1
    set c := (darkTriple seed p).2.2
    show Q_form (a - 2*b + 2*c) (2*a - b + 2*c) (2*a - 2*b + 3*c) = Q_form seed.1 seed.2.1 seed.2.2
    rw [show Q_form (a - 2*b + 2*c) (2*a - b + 2*c) (2*a - 2*b + 3*c) = Q_form a b c from by unfold Q_form; ring]
    exact ih
  | b2 p ih =>
    simp only [darkTriple]
    set a := (darkTriple seed p).1
    set b := (darkTriple seed p).2.1
    set c := (darkTriple seed p).2.2
    show Q_form (a + 2*b + 2*c) (2*a + b + 2*c) (2*a + 2*b + 3*c) = Q_form seed.1 seed.2.1 seed.2.2
    rw [show Q_form (a + 2*b + 2*c) (2*a + b + 2*c) (2*a + 2*b + 3*c) = Q_form a b c from by unfold Q_form; ring]
    exact ih
  | b3 p ih =>
    simp only [darkTriple]
    set a := (darkTriple seed p).1
    set b := (darkTriple seed p).2.1
    set c := (darkTriple seed p).2.2
    show Q_form (-a + 2*b + 2*c) (-2*a + b + 2*c) (-2*a + 2*b + 3*c) = Q_form seed.1 seed.2.1 seed.2.2
    rw [show Q_form (-a + 2*b + 2*c) (-2*a + b + 2*c) (-2*a + 2*b + 3*c) = Q_form a b c from by unfold Q_form; ring]
    exact ih

#print axioms solution
