-- Prove2me | Definitions.Def_Bridges_BerggrenTrees_ArithmeticDarkMatter
-- name    : Bridges_BerggrenTrees_ArithmeticDarkMatter
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:51.954032+00:00
-- url     : https://prove2.me/theorems/80540895-dfdf-4b0d-ac26-32b77bb129ba
-- title:
--   Aether Catalog definitions — Bridges_BerggrenTrees_ArithmeticDarkMatter
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenTrees.ArithmeticDarkMatter`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenTrees/ArithmeticDarkMatter.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Algebra.Core.ArithmeticDarkMatter

Auto-generated from theorem catalog database.
Domain: Algebra/Core
Declarations: 24
-/


/-- The Lorentz form Q(a,b,c) = a² + b² - c² -/
def Q_form (a b c : ℤ) : ℤ := a ^ 2 + b ^ 2 - c ^ 2
























/-- The mass spectrum: which mass-squared values are realized? -/
def massIsRealized (m_sq : ℤ) : Prop :=
  ∃ a b c : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ c ^ 2 - a ^ 2 - b ^ 2 = m_sq








/-- The Berggren B₁ matrix action on a triple -/
def berggren_B1 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a - 2*b + 2*c, 2*a - b + 2*c, 2*a - 2*b + 3*c)








/-- B₂ also preserves Q -/
def berggren_B2 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a + 2*b + 2*c, 2*a + b + 2*c, 2*a + 2*b + 3*c)








/-- B₃ also preserves Q -/
def berggren_B3 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (-a + 2*b + 2*c, -2*a + b + 2*c, -2*a + 2*b + 3*c)








/-- A path in the dark matter tree (same branching as the photon tree) -/
inductive DarkPath where
  | root : DarkPath
  | b1 : DarkPath → DarkPath
  | b2 : DarkPath → DarkPath
  | b3 : DarkPath → DarkPath
  deriving Repr




/-- The triple at a given dark matter path, starting from seed (a₀, b₀, c₀) -/
def darkTriple (seed : ℤ × ℤ × ℤ) : DarkPath → ℤ × ℤ × ℤ
  | .root => seed
  | .b1 p =>
    let (a, b, c) := darkTriple seed p
    (a - 2*b + 2*c, 2*a - b + 2*c, 2*a - 2*b + 3*c)
  | .b2 p =>
    let (a, b, c) := darkTriple seed p
    (a + 2*b + 2*c, 2*a + b + 2*c, 2*a + 2*b + 3*c)
  | .b3 p =>
    let (a, b, c) := darkTriple seed p
    (-a + 2*b + 2*c, -2*a + b + 2*c, -2*a + 2*b + 3*c)









-- #eval massCensus 15  -- slow





-- Watch the photon fraction shrink toward zero:
/-- Generate the dark matter tree from a massive seed -/
def darkTreeLevel (seed : ℤ × ℤ × ℤ) : ℕ → List (ℤ × ℤ × ℤ)
  | 0 => [seed]
  | n + 1 =>
    let parents := darkTreeLevel seed n
    parents.flatMap fun (a, b, c) =>
      [ (a - 2*b + 2*c, 2*a - b + 2*c, 2*a - 2*b + 3*c),
        (a + 2*b + 2*c, 2*a + b + 2*c, 2*a + 2*b + 3*c),
        (-a + 2*b + 2*c, -2*a + b + 2*c, -2*a + 2*b + 3*c) ]

-- Dark matter tree from seed (1, 1, 2) [mass² = 2]:
-- Verify mass conservation:
-- Dark matter tree from seed (1, 2, 3) [mass² = 4]:
-- Tachyon tree from seed (2, 2, 1) [mass² = -7]:




/-- The number of possible photon states at depth n -/
def photonStates (n : ℕ) : ℕ := 3 ^ n




/-- The number of possible dark matter states at depth n with m mass choices -/
def darkStates (n m : ℕ) : ℕ := m * 3 ^ n


